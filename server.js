require('dotenv').config();
const express  = require('express');
const http     = require('http');
const { Server } = require('socket.io');
const cors     = require('cors');
const crypto   = require('crypto');
const mongoose = require('mongoose');
const jwt      = require('jsonwebtoken');
const { QUESTIONS_DB } = require('./questions');
const User              = require('./models/User');
const TournamentPlayer  = require('./models/TournamentPlayer');
const TournamentSchedule = require('./models/TournamentSchedule');
const WinnerSubmission  = require('./models/WinnerSubmission');
const Question          = require('./models/Question');
const { log } = require('console');

// ─── Hardcoded admin credentials ─────────────────────────────────────────────
const ADMIN_EMAIL    = 'indtropical@gmail.com';
const ADMIN_PASSWORD = 'Olatun@900';

const app    = express();
const server = http.createServer(app);

const io = new Server(server, {
  cors: {
    origin: '*',
    methods: ['GET', 'POST'],
  },
  // Prevent clients from hammering with huge payloads
  maxHttpBufferSize: 1e4,   // 10 KB max per message
  // Increased timeouts for mobile networks
  pingTimeout: 30000,       // 30s before considering disconnected
  pingInterval: 15000,      // 15s ping interval
  // Allow polling fallback for restrictive networks
  transports: ['websocket', 'polling'],
  // Upgrade timeout for slow connections
  upgradeTimeout: 30000,
  // Allow reconnection
  allowUpgrades: true,
});

app.use(cors());
app.use(express.json({ limit: '10kb' }));
app.get('/', (_, res) => res.send('QuizDuel Server running ✅'));

// ─── In-memory state ──────────────────────────────────────────────────────────
const lobby       = new Map();   // deviceId → { socketId, username, joinedAt }
const matches     = new Map();   // matchId  → Match
const devices     = new Map();   // deviceId → socketId  (for reconnects)
const sessions    = new Map();   // sessionToken → { deviceId, socketId, createdAt }
const violations  = new Map();   // deviceId → count

// Rate-limit: track event timestamps per socket
const rateLimits  = new Map();   // socketId → { join_lobby: [timestamps], submit_answer: [...] }

// Spectator / view sockets
const spectators  = new Set();   // set of socketIds for view-only clients

// Leaderboard: username → { username, wins, stage }
const leaderboard = new Map();

// Runtime question bank. Populated from MongoDB on startup so matches can read
// synchronously with zero DB hits per question.
let questionBank = [];

// Load all questions from the MongoDB collection into the in-memory cache.
// Safe to call repeatedly — fully replaces the in-memory bank from the DB.
async function loadQuestionBankFromDB() {
  if (!mongoUp()) {
    console.log('⚠️  Mongo not connected — skipping question-bank load from DB');
    return 0;
  }
  try {
    const docs = await Question.find({}, { _id: 0, id: 1, question: 1, options: 1, correct: 1, category: 1 }).lean();
    questionBank = docs.map(d => ({
      id: d.id,
      question: d.question,
      options: d.options,
      correct: d.correct,
      category: d.category || 'General',
    }));
    console.log(`✅ Loaded ${questionBank.length} questions from MongoDB into memory`);
    return questionBank.length;
  } catch (e) {
    console.error('⚠️  loadQuestionBankFromDB failed:', e.message);
    return 0;
  }
}

// Fallback loader: read `questions.example.json` straight off disk.
// Used at startup when MongoDB is unavailable or the collection is empty,
// so the tournament can run from the JSON file alone.
function loadQuestionBankFromFile() {
  const fs = require('fs');
  const path = require('path');
  const filePath = path.join(__dirname, 'questions.example.json');
  try {
    if (!fs.existsSync(filePath)) {
      console.log(`⚠️  ${filePath} not found — no fallback question bank`);
      return 0;
    }
    const raw = fs.readFileSync(filePath, 'utf8');
    const parsed = JSON.parse(raw);
    if (!Array.isArray(parsed)) {
      console.error('⚠️  questions.example.json must contain an array');
      return 0;
    }
    questionBank = parsed.filter(q =>
      q && q.id && q.question && q.options && ['A','B','C','D'].includes(q.correct)
    ).map(q => ({
      id: q.id,
      question: q.question,
      options: q.options,
      correct: q.correct,
      category: q.category || 'General',
    }));
    console.log(`✅ Loaded ${questionBank.length} questions from questions.example.json into memory`);
    return questionBank.length;
  } catch (e) {
    console.error('⚠️  loadQuestionBankFromFile failed:', e.message);
    return 0;
  }
}

// Live admin sockets — receive real-time winner submission notifications
const adminSockets = new Set();

// ─── NEW: Dedicated Queues for Real-Time Matchmaking ─────────────────────────
// waitingQueue: players waiting to be matched for the FIRST time in a round
// winnersQueue: players who WON their match, waiting to be paired with another winner
// Key: deviceId → { deviceId, username, socketId, round, queuedAt, wins }
const waitingQueue = new Map();
const winnersQueue = new Map();

// Matchmaking lock to prevent race conditions
let matchmakingLock = false;

// Track which players are currently IN an active match (prevents double-queueing)
const playersInMatch = new Set(); // deviceIds of players currently in a match

// Server-driven match timers: matchId → { timer, currentQuestion, questionStartTime }
const matchTimers = new Map();

// ─── Tournament Pacing Settings ──────────────────────────────────────────────
// Adjust these to control how fast the tournament runs.
// POST_MATCH_DELAY is the pause between "last match in a round ended" and
// "next round pairs". Kept short so the bracket flies once every match is done.
const TOURNAMENT_PACING = {
  QUESTION_TIME_SECONDS: 10,       // Seconds per question
  PRE_MATCH_COUNTDOWN: 3,          // Seconds shown before each match starts
  BETWEEN_ROUNDS_DELAY: 2,         // Seconds shown after a round_result before next question
  POST_MATCH_DELAY: 1,             // Seconds between last match of a round ending and next round pairing
  DISCONNECT_GRACE_SECONDS: 25,    // How long a disconnected player has to reconnect before forfeit
};

// ─── Tournament Registration System ──────────────────────────────────────────
// Players enter username before tournament. Auto-start when MAX_TOURNAMENT_PLAYERS
// is reached, or admin can force-start with any count ≥ 2.
const MAX_TOURNAMENT_PLAYERS = 400;
const registeredPlayers = new Map(); // deviceId → { username, deviceId, joinedAt, socketId }
let tournamentConfig = {
  scheduledDate: null,            // ISO string — when set, registration mode is active
  tournamentStarted: false,       // Has the admin started the tournament?
  maxPlayers: MAX_TOURNAMENT_PLAYERS,
  rewardAmount: '',               // Admin-configured display string e.g. "₦20,000"
  tournamentId: null,             // Stable id used to scope WinnerSubmission docs
};

// Compute a human round name from the player count entering that round.
function roundNameForCount(count) {
  if (count <= 1) return 'Champion';
  if (count === 2) return 'Final';
  if (count === 4) return 'Semi Final';
  if (count === 8) return 'Quarter Final';
  return null; // null → caller uses `Round N`
}
function roundLabel(roundNumber, playersEntering) {
  return roundNameForCount(playersEntering) || `Round ${roundNumber}`;
}

// Largest power of 2 ≤ n. Used to trim a registered roster down to a clean
// bracket so every round is a perfect pair (2, 4, 8, 16, 32, 64, 128, 256...).
function largestPowerOfTwo(n) {
  if (n < 2) return 0;
  return 1 << Math.floor(Math.log2(n));
}

// Elimination bracket: tracks winners waiting for next round pairing
// round → [ { deviceId, username, socketId, wins } ]
const bracketWinners = new Map();
let currentRound = 1;

// Registration is open whenever the tournament hasn't started yet.
// Players are added to registeredPlayers by /api/users when forTournament=true.
function isRegistrationMode() {
  return !tournamentConfig.tournamentStarted;
}

// Whether MongoDB is connected and usable
function mongoUp() {
  return mongoose.connection && mongoose.connection.readyState === 1;
}

function canStartPlaying() {
  return tournamentConfig.tournamentStarted;
}

// Get count of currently connected (active) players
function getActivePlayerCount() {
  let count = 0;
  for (const player of registeredPlayers.values()) {
    if (player.socketId) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) count++;
    }
  }
  return count;
}

// Get list of currently connected players
function getActivePlayers() {
  const active = [];
  for (const player of registeredPlayers.values()) {
    if (player.socketId) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) {
        active.push(player);
      }
    }
  }
  return active;
}

// Auto-start timer reference
let autoStartTimer = null;

// ─── Elimination bracket helpers ─────────────────────────────────────────────

// Shuffle array in-place (Fisher-Yates)
function shuffleArray(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

// Pair a list of players into matches for the current round.
// Returns the list of match descriptors created.
function pairPlayersForRound(players, round, questionsPerMatch = 5) {
  shuffleArray(players);
  const matchPairs = [];
  const playersEntering = players.length;
  const label = roundLabel(round, playersEntering);

  for (let i = 0; i < players.length - 1; i += 2) {
    const p1 = players[i];
    const p2 = players[i + 1];

    // ATOMIC: Check they're not already in a match
    if (playersInMatch.has(p1.deviceId) || playersInMatch.has(p2.deviceId)) {
      console.log(`[pairPlayersForRound] Skipping already-in-match players: ${p1.username} or ${p2.username}`);
      continue;
    }

    // Mark as in match BEFORE creating
    playersInMatch.add(p1.deviceId);
    playersInMatch.add(p2.deviceId);

    // Remove from any queues
    waitingQueue.delete(p1.deviceId);
    waitingQueue.delete(p2.deviceId);
    winnersQueue.delete(p1.deviceId);
    winnersQueue.delete(p2.deviceId);

    const match = createMatch(
      { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
      { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
      questionsPerMatch
    );
    // Tag the match with round info so evaluateRound can trigger next-round logic
    match.tournamentRound = round;
    match.roundLabel = label;

    matchPairs.push({
      matchId: match.matchId,
      round,
      roundLabel: label,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });

    const s1 = io.sockets.sockets.get(p1.socketId);
    const s2 = io.sockets.sockets.get(p2.socketId);

    // Build match payload for each player - include their own info AND opponent info.
    // Include the full question objects (without `correct`) inline so clients don't
    // depend on a separate question-bank fetch having completed — eliminates the
    // race where match starts before /api/questions returns and players see no questions.
    const sanitizedQuestions = (match.questions || []).map(q => ({
      id: q.id,
      question: q.question,
      options: q.options,
      category: q.category || 'General',
    }));
    const basePayload = {
      matchId: match.matchId,
      matchSeed: match.seed,
      questionIds: (match.questions || []).map(q => q.id),
      questions: sanitizedQuestions,
      round,
      roundLabel: label,
      totalQuestions: match.questions?.length || questionsPerMatch,
      isTournament: true,
      preMatchCountdown: TOURNAMENT_PACING.PRE_MATCH_COUNTDOWN, // Tell clients to show countdown
      questionTime: TOURNAMENT_PACING.QUESTION_TIME_SECONDS,
    };

    if (s1) {
      s1.join(match.matchId);
      s1.emit('match_found', {
        ...basePayload,
        you: { username: p1.username, deviceId: p1.deviceId },
        opponent: { username: p2.username, deviceId: p2.deviceId },
      });
    }
    if (s2) {
      s2.join(match.matchId);
      s2.emit('match_found', {
        ...basePayload,
        you: { username: p2.username, deviceId: p2.deviceId },
        opponent: { username: p1.username, deviceId: p1.deviceId },
      });
    }

    // Start server-driven timer AFTER pre-match countdown
    setTimeout(() => {
      if (match.active) {
        startMatchTimer(match);
      }
    }, TOURNAMENT_PACING.PRE_MATCH_COUNTDOWN * 1000);

    console.log(`[tournament ${label}] Paired: ${p1.username} vs ${p2.username} → ${match.matchId} (${questionsPerMatch} questions)`);
  }

  // Odd player out → automatic bye (advances to next round)
  if (players.length % 2 !== 0) {
    const byePlayer = players[players.length - 1];
    const s = io.sockets.sockets.get(byePlayer.socketId);
    if (s) s.emit('tournament_bye', { message: `You got a bye this ${label}! You advance automatically.`, username: byePlayer.username, round, roundLabel: label });

    // Bye player advances with infinite duration so they sort behind real wins
    // if the next round ends up odd.
    queueWinnerForNextRound({ ...byePlayer, matchDurationMs: Number.MAX_SAFE_INTEGER }, round);
    console.log(`[tournament ${label}] Bye: ${byePlayer.username}`);
  }

  broadcastToSpectators('round_started', { round, roundLabel: label, matchCount: matchPairs.length, playerCount: playersEntering });
  // Broadcast each match individually so the view screen can display them
  for (const mp of matchPairs) {
    broadcastToSpectators('match_started', {
      matchId: mp.matchId,
      round: mp.round,
      roundLabel: label,
      p1: mp.p1,
      p2: mp.p2,
    });
  }
  io.emit('tournament_round_started', { round, roundLabel: label, matchCount: matchPairs.length, playerCount: playersEntering });
  return matchPairs;
}

// Called after a match ends: buffer winner into the round's bracket.
// Strict round gating: winners wait until EVERY match in this round is finished
// before any pairing for the next round happens.
function queueWinnerForNextRound(player, round) {
  if (!bracketWinners.has(round)) bracketWinners.set(round, []);
  // Avoid duplicate buffering (forfeit + evaluateRound can both fire)
  const buf = bracketWinners.get(round);
  if (!buf.some(p => p.deviceId === player.deviceId)) {
    buf.push(player);
  }

  console.log(`[bracket R${round}] ${player.username} queued (${buf.length} winners so far)`);

  // Check if the round is now complete (all matches finished).
  // If so, schedule the next round's pairing after POST_MATCH_DELAY.
  maybeAdvanceCompletedRound(round);
}

// Round is complete when no active match still carries tournamentRound === round.
function isRoundComplete(round) {
  for (const m of matches.values()) {
    if (m.active && m.tournamentRound === round) return false;
  }
  return true;
}

// Called whenever a match ends. If the round is now complete, schedule the
// next round's pairing. No-op if more matches are still active.
function maybeAdvanceCompletedRound(round) {
  if (!isRoundComplete(round)) {
    const active = [...matches.values()].filter(m => m.active && m.tournamentRound === round).length;
    console.log(`[bracket R${round}] Round not yet complete (${active} matches still active)`);
    return;
  }

  const delayMs = TOURNAMENT_PACING.POST_MATCH_DELAY * 1000;
  console.log(`[bracket R${round}] ✅ Round complete — advancing in ${TOURNAMENT_PACING.POST_MATCH_DELAY}s`);
  setTimeout(() => advanceToNextRound(round), delayMs);
}

// Advance all waiting winners into the next round (strict gating).
function advanceToNextRound(completedRound) {
  // Idempotency: if already advanced, bracketWinners[round] is empty/missing
  const advancingPlayers = bracketWinners.get(completedRound) || [];
  if (advancingPlayers.length === 0) {
    console.log(`[tournament] advanceToNextRound(${completedRound}): no winners buffered — nothing to do`);
    return;
  }
  bracketWinners.delete(completedRound);

  // Filter to only include still-connected players
  const connectedAdvancers = advancingPlayers.filter(p => {
    if (!p.socketId) return false;
    const socket = io.sockets.sockets.get(p.socketId);
    return socket && socket.connected;
  });

  console.log(`[tournament] Round ${completedRound} complete — ${advancingPlayers.length} winners (${connectedAdvancers.length} connected)`);

  if (connectedAdvancers.length === 0) {
    console.log(`[tournament] No connected players remain — tournament ends`);
    io.emit('tournament_no_winner', { round: completedRound, message: 'All remaining players disconnected.' });
    return;
  }

  if (connectedAdvancers.length === 1) {
    declareTournamentChampion(connectedAdvancers[0]);
    return;
  }

  // If the count is odd (forfeit, double-disconnect, or stragglers from a
  // prior bye), drop the SLOWEST winner — they took longest to defeat their
  // opponent so they don't get the free pass. This guarantees every round
  // is a perfect pair.
  if (connectedAdvancers.length % 2 !== 0) {
    connectedAdvancers.sort((a, b) => (a.matchDurationMs || 0) - (b.matchDurationMs || 0));
    const dropped = connectedAdvancers.pop();
    const rp = registeredPlayers.get(dropped.deviceId);
    if (rp) rp.status = 'not_selected';
    const s = io.sockets.sockets.get(dropped.socketId);
    if (s) s.emit('tournament_not_selected', {
      message: `Round ${completedRound} ended with an odd number of winners. The slowest match win is dropped to keep the bracket clean — that was you this time.`,
      bracketSize: connectedAdvancers.length,
    });
    broadcastToSpectators('player_eliminated', { username: dropped.username });
    console.log(`[tournament] Odd advance count — dropped slowest winner: ${dropped.username} (${Math.round((dropped.matchDurationMs || 0) / 1000)}s match)`);
  }

  const nextRound = completedRound + 1;
  currentRound = nextRound;

  const questionsPerMatch = getQuestionsPerMatch(connectedAdvancers.length);
  const label = roundLabel(nextRound, connectedAdvancers.length);
  console.log(`[tournament] ${label}: ${questionsPerMatch} questions/match for ${connectedAdvancers.length} players`);

  io.emit('tournament_next_round', {
    round: nextRound,
    roundLabel: label,
    playerCount: connectedAdvancers.length,
    questionsPerMatch,
  });

  // If exactly 2 advancers, they are the finalists — notify each personally.
  if (connectedAdvancers.length === 2) {
    connectedAdvancers.forEach(p => {
      const s = io.sockets.sockets.get(p.socketId);
      if (s) s.emit('tournament_final_notice', {
        message: '🏆 You are in the Final! One more match to become Champion!',
        round: nextRound,
      });
    });
  }

  pairPlayersForRound(connectedAdvancers, nextRound, questionsPerMatch);
}

// NEW: Server-driven match timer
function startMatchTimer(match) {
  const QUESTION_TIME_MS = TOURNAMENT_PACING.QUESTION_TIME_SECONDS * 1000;
  const COUNTDOWN_INTERVAL_MS = 1000; // emit countdown every second

  let timeLeft = TOURNAMENT_PACING.QUESTION_TIME_SECONDS;
  match.questionStartTime = Date.now();

  const countdownInterval = setInterval(() => {
    timeLeft--;
    
    // Emit countdown to both players
    io.to(match.matchId).emit('timer_tick', {
      matchId: match.matchId,
      timeLeft,
      questionIndex: match.questionIndex,
    });

    if (timeLeft <= 0) {
      clearInterval(countdownInterval);
      
      // Force timeout for any player who hasn't answered
      const players = Object.values(match.players);
      let needsEval = false;
      
      for (const player of players) {
        if (player.answerTime === null && match.active) {
          // Player didn't answer in time — mark as timed out
          player.answer = null;
          player.answerTime = TOURNAMENT_PACING.QUESTION_TIME_SECONDS;
          needsEval = true;
        }
      }

      // Evaluate if all players have been resolved (submitted or timed out)
      if (needsEval && match.active && players.every(p => p.answerTime !== null)) {
        evaluateRound(match, io);
      }
    }
  }, COUNTDOWN_INTERVAL_MS);

  // Store timer reference for cleanup
  matchTimers.set(match.matchId, {
    interval: countdownInterval,
    currentQuestion: match.questionIndex,
    questionStartTime: match.questionStartTime,
  });
}

// Clean up timer when match ends
function cleanupMatchTimer(matchId) {
  const timerData = matchTimers.get(matchId);
  if (timerData) {
    clearInterval(timerData.interval);
    matchTimers.delete(matchId);
  }
}

// NEW: Try to instantly pair players from the waitingQueue
function tryInstantQueuePair() {
  if (matchmakingLock) {
    setTimeout(tryInstantQueuePair, 50);
    return;
  }

  matchmakingLock = true;
  
  try {
    // Get connected players from waiting queue
    const availablePlayers = [];
    for (const [deviceId, player] of waitingQueue) {
      // Skip if already in match
      if (playersInMatch.has(deviceId)) {
        waitingQueue.delete(deviceId);
        continue;
      }
      
      // Verify socket is connected
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket && socket.connected) {
        availablePlayers.push(player);
      } else {
        // Ghost user — remove
        waitingQueue.delete(deviceId);
        console.log(`[waitingQueue] Removed ghost: ${player.username}`);
      }
    }
    
    console.log(`[tryInstantQueuePair] ${availablePlayers.length} players available`);
    
    // Pair in groups of 2
    while (availablePlayers.length >= 2) {
      const p1 = availablePlayers.shift();
      const p2 = availablePlayers.shift();
      
      // Remove from queue ATOMICALLY
      waitingQueue.delete(p1.deviceId);
      waitingQueue.delete(p2.deviceId);
      
      // Mark as in match
      playersInMatch.add(p1.deviceId);
      playersInMatch.add(p2.deviceId);
      
      // Create match
      const questionsPerMatch = 5;
      const match = createMatch(
        { deviceId: p1.deviceId, username: p1.username, socketId: p1.socketId },
        { deviceId: p2.deviceId, username: p2.username, socketId: p2.socketId },
        questionsPerMatch
      );
      match.tournamentRound = 1; // Default to round 1 for queue matches
      
      const basePayload = {
        matchId: match.matchId,
        matchSeed: match.seed,
        questionIds: (match.questions || []).map(q => q.id),
        questions: (match.questions || []).map(q => ({
          id: q.id,
          question: q.question,
          options: q.options,
          category: q.category || 'General',
        })),
        round: 1,
        totalQuestions: questionsPerMatch,
        isTournament: true,
        questionTime: TOURNAMENT_PACING.QUESTION_TIME_SECONDS,
      };
      
      const s1 = io.sockets.sockets.get(p1.socketId);
      const s2 = io.sockets.sockets.get(p2.socketId);
      
      if (s1) {
        s1.join(match.matchId);
        s1.emit('match_found', {
          ...basePayload,
          you: { username: p1.username, deviceId: p1.deviceId },
          opponent: { username: p2.username, deviceId: p2.deviceId },
        });
      }
      if (s2) {
        s2.join(match.matchId);
        s2.emit('match_found', {
          ...basePayload,
          you: { username: p2.username, deviceId: p2.deviceId },
          opponent: { username: p1.username, deviceId: p1.deviceId },
        });
      }
      
      // Start server-driven timer
      startMatchTimer(match);
      
      console.log(`[instant-queue-pair] ${p1.username} vs ${p2.username} → ${match.matchId}`);
      broadcastToSpectators('match_started', {
        matchId: match.matchId,
        p1: { username: p1.username, deviceId: p1.deviceId },
        p2: { username: p2.username, deviceId: p2.deviceId },
      });
    }
    
    // Notify remaining players of their queue position
    let position = 1;
    for (const [, player] of waitingQueue) {
      const socket = io.sockets.sockets.get(player.socketId);
      if (socket) {
        socket.emit('queue_update', { 
          position, 
          totalWaiting: waitingQueue.size,
          message: `Position ${position} of ${waitingQueue.size}`
        });
      }
      position++;
    }
  } finally {
    matchmakingLock = false;
  }
}

// Periodic ghost user cleanup (runs every 30 seconds)
setInterval(() => {
  let cleaned = 0;
  
  // Clean waitingQueue
  for (const [deviceId, player] of waitingQueue) {
    const socket = io.sockets.sockets.get(player.socketId);
    if (!socket || !socket.connected) {
      waitingQueue.delete(deviceId);
      cleaned++;
    }
  }
  
  // Clean winnersQueue
  for (const [deviceId, player] of winnersQueue) {
    const socket = io.sockets.sockets.get(player.socketId);
    if (!socket || !socket.connected) {
      winnersQueue.delete(deviceId);
      cleaned++;
    }
  }
  
  // Clean playersInMatch (if their match is no longer active)
  for (const deviceId of playersInMatch) {
    let inActiveMatch = false;
    for (const [, match] of matches) {
      if (match.active && match.players[deviceId]) {
        inActiveMatch = true;
        break;
      }
    }
    if (!inActiveMatch) {
      playersInMatch.delete(deviceId);
      cleaned++;
    }
  }
  
  if (cleaned > 0) {
    console.log(`[ghost-cleanup] Removed ${cleaned} stale entries`);
  }
}, 30000);

// Declare the overall tournament champion
async function declareTournamentChampion(player) {
  // Guard: don't declare a player champion if they never actually won a match
  // (e.g. bye player who advanced because all opponents got both-wrong)
  const registered = registeredPlayers.get(player.deviceId);
  const actualWins = registered?.wins || player.wins || 0;
  
  if (actualWins === 0) {
    console.log(`[tournament] ⚠️ ${player.username} would be champion but has 0 wins (bye only) — no champion declared`);
    io.emit('tournament_no_winner', { 
      round: currentRound, 
      message: 'All competing players were eliminated — no champion this tournament.' 
    });
    return;
  }

  console.log(`[tournament] 🏆 CHAMPION: ${player.username} (${actualWins} wins)`);
  
  // Mark champion status in registeredPlayers for guard checks
  if (registered) {
    registered.status = 'champion';
  }
  
  const rewardAmount = tournamentConfig.rewardAmount || '';
  const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || null;

  io.emit('tournament_champion', {
    username: player.username,
    deviceId: player.deviceId,
    rewardAmount,
    tournamentId,
  });
  broadcastToSpectators('tournament_champion', {
    username: player.username,
    rewardAmount,
  });

  const s = io.sockets.sockets.get(player.socketId);
  if (s) s.emit('you_are_champion', {
    message: '🏆 Congratulations! You are the Tournament Champion!',
    username: player.username,
    rewardAmount,
    tournamentId,
  });

  // Update leaderboard
  const lb = leaderboard.get(player.username) || { username: player.username, wins: 0 };
  lb.stage = 'champion';
  leaderboard.set(player.username, lb);
  broadcastLeaderboard();

  // Persist champion status to MongoDB
  try {
    await TournamentPlayer.findOneAndUpdate(
      { deviceId: player.deviceId, tournamentId: tournamentConfig.scheduledDate },
      { status: 'winner' }
    );
  } catch (e) { console.error('[tournament] DB update champion error:', e.message); }
}

// Reusable function to start the tournament and pair all players (Round 1)
function startTournament() {
  if (tournamentConfig.tournamentStarted) return { error: 'Tournament already started' };
  if (registeredPlayers.size < 2) return { error: 'Need at least 2 registered players' };
  if (questionBank.length === 0) return { error: 'No questions available. Admin must add questions first.' };

  tournamentConfig.tournamentStarted = true;
  tournamentConfig.tournamentId = tournamentConfig.scheduledDate || ('tournament_' + Date.now());
  currentRound = 1;
  bracketWinners.clear();

  // Update tournament status in DB
  TournamentSchedule.findOneAndUpdate(
    { status: 'scheduled' },
    { status: 'started' }
  ).catch(e => console.error('[tournament] DB status update error:', e.message));

  // Only include players who have an active socket connection
  const allPlayers = [...registeredPlayers.values()];
  const disconnectedNames = [];
  const connectedPlayers = allPlayers.filter(p => {
    if (!p.socketId) {
      disconnectedNames.push(p.username);
      return false;
    }
    const socket = io.sockets.sockets.get(p.socketId);
    const isConnected = socket && socket.connected;
    if (!isConnected) {
      disconnectedNames.push(p.username);
    }
    return isConnected;
  });

  if (disconnectedNames.length > 0) {
    console.log(`[tournament] ⚠️ Disconnected players: ${disconnectedNames.join(', ')}`);
  }
  console.log(`[tournament] ${allPlayers.length} registered, ${connectedPlayers.length} connected`);

  if (connectedPlayers.length < 2) {
    tournamentConfig.tournamentStarted = false; // Rollback
    return { error: `Only ${connectedPlayers.length} players connected. Need at least 2.` };
  }

  // Trim down to the largest power of 2 so every round pairs perfectly
  // (2, 4, 8, 16, 32, 64, 128, 256 ...). Timing-based: the LATEST to
  // register loses their seat first ("first-come, first-served").
  // Ties on joinedAt are broken by deviceId for determinism.
  const targetSize = largestPowerOfTwo(connectedPlayers.length);
  connectedPlayers.sort((a, b) => {
    const aT = a.joinedAt || Number.MAX_SAFE_INTEGER;
    const bT = b.joinedAt || Number.MAX_SAFE_INTEGER;
    if (aT !== bT) return aT - bT;
    return String(a.deviceId).localeCompare(String(b.deviceId));
  });
  const players = connectedPlayers.slice(0, targetSize);
  const trimmed = connectedPlayers.slice(targetSize);

  if (trimmed.length > 0) {
    console.log(`[tournament] Trimmed ${trimmed.length} players to keep the bracket a power of 2 (${connectedPlayers.length} → ${targetSize})`);
    for (const p of trimmed) {
      // Mark them as not-selected; they stay in registeredPlayers but won't be paired.
      const rp = registeredPlayers.get(p.deviceId);
      if (rp) rp.status = 'not_selected';
      const s = io.sockets.sockets.get(p.socketId);
      if (s) s.emit('tournament_not_selected', {
        message: `The bracket is capped at ${targetSize} for a clean elimination. Seats go to the first ${targetSize} who registered — you joined later this time. Try the next tournament.`,
        bracketSize: targetSize,
      });
    }
  }

  // Track initial player count for bye/champion logic
  tournamentConfig.initialPlayerCount = players.length;

  const questionsPerMatch = getQuestionsPerMatch(players.length);
  const label = roundLabel(1, players.length);
  console.log(`[tournament] Using ${questionsPerMatch} questions per match for ${players.length} players (clean bracket)`);

  // Broadcast tournament start to all clients
  io.emit('tournament_started', {
    message: 'Tournament is starting!',
    playerCount: players.length,          // size of the clean bracket
    registeredCount: registeredPlayers.size,
    round: 1,
    roundLabel: label,
    questionsPerMatch,
    rewardAmount: tournamentConfig.rewardAmount,
    maxPlayers: tournamentConfig.maxPlayers,
    tournamentId: tournamentConfig.tournamentId,
  });

  // Pair the selected (power-of-2) players for Round 1
  const matchPairs = pairPlayersForRound(players, 1, questionsPerMatch);

  broadcastToSpectators('tournament_started', {
    playerCount: players.length,
    matchCount: matchPairs.length,
    round: 1,
    roundLabel: label,
    rewardAmount: tournamentConfig.rewardAmount,
  });

  console.log(`[tournament] 🎮 Started with ${players.length}/${registeredPlayers.size} players (clean bracket), ${matchPairs.length} ${label} matches`);

  return { ok: true, playerCount: players.length, matches: matchPairs, round: 1, roundLabel: label };
}

// Schedule auto-start timer for a tournament
function scheduleAutoStart(scheduledDate) {
  // Clear any existing timer
  if (autoStartTimer) {
    clearTimeout(autoStartTimer);
    autoStartTimer = null;
  }

  const startTime = new Date(scheduledDate).getTime();
  const now = Date.now();
  const delay = startTime - now;

  console.log(`[tournament] scheduleAutoStart called:`);
  console.log(`  - Scheduled: ${scheduledDate}`);
  console.log(`  - Server now: ${new Date(now).toISOString()}`);
  console.log(`  - Delay: ${Math.round(delay / 1000)}s (${Math.round(delay / 60000)} min)`);

  if (delay <= 0) {
    // Time already passed — start immediately if possible
    console.log('[tournament] Scheduled time already passed — auto-starting now');
    io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
    attemptTournamentStart();
    return;
  }

  // Schedule countdown warnings at 5min, 1min, 30s, 10s before start
  const countdownWarnings = [
    { ms: 5 * 60 * 1000, msg: '5 minutes' },
    { ms: 1 * 60 * 1000, msg: '1 minute' },
    { ms: 30 * 1000, msg: '30 seconds' },
    { ms: 10 * 1000, msg: '10 seconds' },
    { ms: 5 * 1000, msg: '5 seconds' },
  ];

  countdownWarnings.forEach(({ ms, msg }) => {
    const warningDelay = delay - ms;
    if (warningDelay > 0) {
      setTimeout(() => {
        io.emit('tournament_countdown', { 
          secondsRemaining: Math.round(ms / 1000), 
          message: `Tournament starts in ${msg}!` 
        });
        console.log(`[tournament] ⏱️  Countdown: ${msg} remaining`);
      }, warningDelay);
    }
  });

  console.log(`[tournament] ✅ Auto-start timer SET — will fire in ${Math.round(delay / 1000)}s`);
  autoStartTimer = setTimeout(() => {
    console.log('[tournament] ⏰ Auto-start timer FIRED! Starting tournament...');
    io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
    attemptTournamentStart();
  }, delay);
}

// Attempt to start tournament with retry logic
let autoStartRetryCount = 0;
const MAX_AUTO_START_RETRIES = 720; // Retry for up to 1 hour (720 x 5s) — keeps waiting for players
const GRACE_PERIOD_SECONDS = 10; // Wait 10s after min players reached to let more join
let gracePeriodTimer = null;
let gracePeriodStartCount = 0;

function attemptTournamentStart() {
  const activeCount = getActivePlayerCount();
  const registeredCount = registeredPlayers.size;
  
  // If we have enough players but grace period hasn't started, start it
  if (activeCount >= 2 && !gracePeriodTimer) {
    gracePeriodStartCount = activeCount;
    console.log(`[tournament] ✅ ${activeCount} players ready! Starting ${GRACE_PERIOD_SECONDS}s grace period for more players to join...`);
    
    io.emit('tournament_grace_period', {
      message: `${activeCount} players ready! Starting in ${GRACE_PERIOD_SECONDS} seconds...`,
      registeredCount,
      activeCount,
      secondsRemaining: GRACE_PERIOD_SECONDS,
    });
    
    // Countdown during grace period
    let remaining = GRACE_PERIOD_SECONDS;
    gracePeriodTimer = setInterval(() => {
      remaining--;
      if (remaining > 0 && remaining <= 5) {
        io.emit('tournament_countdown', { 
          message: `Starting in ${remaining}...`, 
          secondsRemaining: remaining 
        });
        console.log(`[tournament] ⏱️ Grace period: ${remaining}s remaining (${getActivePlayerCount()} players)`);
      }
      if (remaining <= 0) {
        clearInterval(gracePeriodTimer);
        gracePeriodTimer = null;
        // Now actually start
        const finalCount = getActivePlayerCount();
        console.log(`[tournament] Grace period ended. Starting with ${finalCount} players (was ${gracePeriodStartCount} at start)`);
        doActualTournamentStart();
      }
    }, 1000);
    return;
  }
  
  // If grace period is already running, don't do anything - let it complete
  if (gracePeriodTimer) {
    return;
  }
  
  // Not enough players yet
  console.log(`[tournament] Auto-start attempt ${autoStartRetryCount + 1} failed: Need at least 2 registered players`);
  console.log(`[tournament] State: ${registeredCount} registered, ${activeCount} active`);
  
  if (autoStartRetryCount < MAX_AUTO_START_RETRIES) {
    autoStartRetryCount++;
    console.log(`[tournament] Retrying in 5 seconds... (attempt ${autoStartRetryCount}/${MAX_AUTO_START_RETRIES})`);
    
    io.emit('tournament_auto_start_pending', {
      message: `Waiting for players... Retry ${autoStartRetryCount}/${MAX_AUTO_START_RETRIES}`,
      registeredCount,
      activeCount,
      retryIn: 5,
    });
    
    setTimeout(() => {
      attemptTournamentStart();
    }, 5000);
  } else {
    // Give up after max retries
    autoStartRetryCount = 0;
    console.log(`[tournament] Auto-start failed after ${MAX_AUTO_START_RETRIES} retries`);
    
    io.emit('tournament_auto_start_failed', { 
      error: 'Not enough players',
      message: `Tournament could not start: Not enough players. Please try again.`,
      registeredCount,
      activeCount,
    });
  }
}

function doActualTournamentStart() {
  const result = startTournament();
  
  if (result.error) {
    console.log(`[tournament] Start failed after grace period: ${result.error}`);
    io.emit('tournament_auto_start_failed', { 
      error: result.error,
      message: `Tournament could not start: ${result.error}`,
    });
  } else {
    autoStartRetryCount = 0;
    console.log(`[tournament] ✅ Auto-start successful!`);
  }
}

// ─── Security helpers ─────────────────────────────────────────────────────────

// Rate limiter: allow max `limit` events per `windowMs`
function isRateLimited(socketId, event, limit = 5, windowMs = 5000) {
  if (!rateLimits.has(socketId)) rateLimits.set(socketId, {});
  const buckets = rateLimits.get(socketId);
  if (!buckets[event]) buckets[event] = [];
  const now = Date.now();
  buckets[event] = buckets[event].filter(t => now - t < windowMs);
  if (buckets[event].length >= limit) return true;
  buckets[event].push(now);
  return false;
}

// Track violation; auto-disconnect after threshold
function recordViolation(socket, reason) {
  const deviceId = socket.data.deviceId || socket.id;
  const count = (violations.get(deviceId) || 0) + 1;
  violations.set(deviceId, count);
  console.warn(`[⚠️  VIOLATION] ${deviceId} — ${reason} (total: ${count})`);
  socket.emit('security_violation', { reason, count });
  if (count >= 3) {
    console.warn(`[🔴 BAN] ${deviceId} exceeded violation limit — disconnecting`);
    socket.emit('security_ban', { reason: 'Too many violations. You have been disconnected.' });
    setTimeout(() => socket.disconnect(true), 500);
  }
}

// Validate session token — one active socket per session
function validateSession(socket, sessionToken, deviceId) {
  const existing = sessions.get(sessionToken);
  if (existing && existing.socketId !== socket.id && existing.deviceId !== deviceId) {
    // Different device/socket trying to reuse token → duplicate session
    return false;
  }
  sessions.set(sessionToken, { deviceId, socketId: socket.id, createdAt: Date.now() });
  return true;
}

// Answer timing validation (ms)
const MIN_ANSWER_MS = 350; // impossible to answer faster than this


// ─── Helpers ──────────────────────────────────────────────────────────────────

// Simple deterministic hash → number (mulberry32 seed)
function hashStr(str) {
  let h = 0x811c9dc5;
  for (let i = 0; i < str.length; i++) {
    h ^= str.charCodeAt(i);
    h = Math.imul(h, 0x01000193) >>> 0;
  }
  return h;
}

function mulberry32(seed) {
  let s = seed >>> 0;
  return () => {
    s += 0x6d2b79f5;
    let t = Math.imul(s ^ (s >>> 15), 1 | s);
    t ^= t + Math.imul(t ^ (t >>> 7), 61 | t);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function seededShuffle(arr, seedStr) {
  const rng = mulberry32(hashStr(String(seedStr)));
  const a = [...arr];
  for (let i = a.length - 1; i > 0; i--) {
    const j = Math.floor(rng() * (i + 1));
    [a[i], a[j]] = [a[j], a[i]];
  }
  return a;
}

// Remove stale lobby entries (> 60s — give players time to find opponent)
function pruneLobby() {
  const now = Date.now();
  for (const [id, entry] of lobby) {
    if (entry.isBot) continue; // never prune bots
    if (now - entry.joinedAt > 60000) lobby.delete(id);
  }
}

// Instantly try to pair a player with anyone waiting in the lobby
function tryInstantPair(deviceId, username, socketId) {
  // Find any other real player waiting
  let paired = null;
  for (const [id, entry] of lobby) {
    if (id === deviceId) continue;
    paired = entry;
    break;
  }

  if (paired) {
    lobby.delete(paired.deviceId);
    lobby.delete(deviceId);

    const p1 = { deviceId: paired.deviceId, username: paired.username, socketId: paired.socketId };
    const p2 = { deviceId, username, socketId };
    const match = createMatch(p1, p2);
    
    const socket = io.sockets.sockets.get(socketId);
    if (socket) socket.join(match.matchId);
    const p1Socket = io.sockets.sockets.get(paired.socketId);
    if (p1Socket) p1Socket.join(match.matchId);
    
    const payload = (myDeviceId) => {
      const opp = Object.values(match.players).find(p => p.deviceId !== myDeviceId);
      return {
        matchId: match.matchId,
        seed: match.seed,
        questionIds: (match.questions || []).map(q => q.id),
        opponent: { username: opp.username, deviceId: opp.deviceId },
      };
    };
    
    if (socket) socket.emit('match_found', payload(deviceId));
    if (p1Socket) p1Socket.emit('match_found', payload(paired.deviceId));
    console.log(`[instant-pair] ${match.matchId}  ${paired.username} vs ${username}`);
    
    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });
    broadcastToSpectators('match_update', {
      matchId: match.matchId,
      players: {
        [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: null },
        [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: null },
      },
    });
    broadcastLobbyCount();
    return true;
  }
  return false;
}

// ─── View / spectator helpers ─────────────────────────────────────────────────

function broadcastLobbyCount() {
  const count = lobby.size;
  io.emit('lobby_count', { count });
}

function broadcastToSpectators(event, data) {
  for (const sid of spectators) {
    const s = io.sockets.sockets.get(sid);
    if (s) s.emit(event, data);
  }
}

function getLeaderboardArray() {
  return [...leaderboard.values()].sort((a, b) => (b.wins || 0) - (a.wins || 0));
}

function broadcastLeaderboard() {
  const arr = getLeaderboardArray();
  broadcastToSpectators('leaderboard_update', arr);
  io.emit('leaderboard_update', arr);
}

function matchesToView() {
  const result = {};
  for (const [id, m] of matches) {
    if (!m.active) continue; // Only show active matches
    result[id] = {
      matchId: m.matchId,
      players: Object.fromEntries(
        Object.entries(m.players).map(([did, p]) => [
          did,
          { username: p.username, deviceId: p.deviceId, answer: p.answer !== null ? '✓' : null },
        ])
      ),
    };
  }
  return result;
}

function sendViewState(socket) {
  socket.emit('view_state', {
    matches: matchesToView(),
    players: getLeaderboardArray(),
    lobbyCount: lobby.size,
    registeredCount: registeredPlayers.size,
  });
}

// ─── Match factory ────────────────────────────────────────────────────────────

// Calculate questions per match based on number of players in tournament
function getQuestionsPerMatch(playerCount) {
  // More players = more rounds = can have fewer questions per match
  // Fewer players = fewer rounds = need more questions per match for excitement
  if (playerCount <= 4) return 10;      // 2 rounds max → 10 questions per match
  if (playerCount <= 8) return 7;       // 3 rounds max → 7 questions per match
  if (playerCount <= 16) return 5;      // 4 rounds max → 5 questions per match
  if (playerCount <= 32) return 5;      // 5 rounds max → 5 questions per match
  return 3;                              // 6+ rounds → 3 questions per match (faster games)
}

function createMatch(p1, p2, questionsCount = 5) {
  const matchId = 'match_' + Date.now() + '_' + Math.random().toString(36).slice(2, 6);
  const seed    = matchId;

  // Tournament/server-authoritative matches pull from the runtime questionBank.
  // If empty, questions stays null and the client must provide its own seeded questions
  // (used by the casual 1v1 lobby flow).
  let questions = null;
  if (questionBank.length > 0) {
    let pool = questionBank;
    while (pool.length < questionsCount) pool = [...pool, ...questionBank];
    questions = seededShuffle(pool, seed).slice(0, questionsCount);
  }

  const match = {
    matchId,
    seed,
    questions,          // null = use seeded frontend bank; array = use these exact questions
    questionsCount,     // Track how many questions this match should have
    players: {
      [p1.deviceId]: { ...p1, answer: null, answerTime: null, ready: false, connected: true },
      [p2.deviceId]: { ...p2, answer: null, answerTime: null, ready: false, connected: true },
    },
    questionIndex: 0,
    bothCorrectCount: 0,
    startTime: Date.now(),
    questionStartTime: Date.now(),
    active: true,
  };
  matches.set(matchId, match);
  return match;
}

// ─── Socket.io ────────────────────────────────────────────────────────────────
io.on('connection', (socket) => {
  console.log(`[+] connected  ${socket.id}`);

  // Clean up rate limit buckets on disconnect
  socket.on('disconnect', () => {
    const deviceId = socket.data.deviceId;
    console.log(`[-] disconnected ${socket.id} (${deviceId || 'unknown'})`);
    rateLimits.delete(socket.id);
    spectators.delete(socket.id);
    if (deviceId) {
      lobby.delete(deviceId);
      
      // IMMEDIATELY remove from queues (ghost cleanup)
      waitingQueue.delete(deviceId);
      winnersQueue.delete(deviceId);
      
      broadcastLobbyCount();
      
      // Broadcast updated active count during tournament registration
      if (isRegistrationMode()) {
        const activeCount = getActivePlayerCount();
        io.emit('active_count', { count: activeCount, registered: registeredPlayers.size });
      }
      
      // Mark player as disconnected in any active match
      for (const [matchId, match] of matches) {
        if (match.players[deviceId] && match.active) {
          match.players[deviceId].connected = false;
          match.players[deviceId].disconnectedAt = Date.now();
          socket.to(matchId).emit('opponent_disconnected', { matchId });
          
          // Reconnect grace period; if they don't come back, the opponent wins by forfeit.
          setTimeout(() => {
            const m = matches.get(matchId);
            if (m && m.active && !m.players[deviceId]?.connected) {
              // Check if opponent is still connected before declaring them winner
              const opponent = Object.values(m.players).find(p => p.deviceId !== deviceId);
              const opponentSocket = opponent ? io.sockets.sockets.get(opponent.socketId) : null;
              const opponentConnected = opponentSocket && opponentSocket.connected;
              
              // Clean up match timer
              cleanupMatchTimer(matchId);
              
              // Remove disconnected player from playersInMatch
              playersInMatch.delete(deviceId);
              
              if (opponent && opponentConnected) {
                // Opponent is still connected — they win by forfeit
                playersInMatch.delete(opponent.deviceId);
                
                opponentSocket.emit('match_over_forfeit', { result: 'win', reason: 'Opponent left the match.' });
                
                // Update leaderboard
                const wb = leaderboard.get(opponent.username) || { username: opponent.username, wins: 0 };
                wb.wins = (wb.wins || 0) + 1;
                leaderboard.set(opponent.username, wb);
                broadcastLeaderboard();
                
                // If this is a tournament match, queue winner for next round
                if (m.tournamentRound) {
                  const round = m.tournamentRound;
                  const wp = registeredPlayers.get(opponent.deviceId);
                  if (wp) {
                    wp.wins = (wp.wins || 0) + 1;
                    wp.round = round + 1;
                  }
                  // Forfeits get a high duration so they sort behind real wins
                  // when an odd round needs trimming.
                  queueWinnerForNextRound(
                    {
                      deviceId: opponent.deviceId,
                      username: opponent.username,
                      socketId: opponent.socketId,
                      wins: (wp?.wins || 1),
                      matchDurationMs: Number.MAX_SAFE_INTEGER,
                    },
                    round
                  );
                }
                
                broadcastToSpectators('player_eliminated', { username: m.players[deviceId].username });
                broadcastToSpectators('match_ended', {
                  matchId,
                  winner: opponent.username,
                  loser: m.players[deviceId].username,
                });
              } else {
                // Both players disconnected — treat as both eliminated
                console.log(`[forfeit] Both players disconnected in match ${matchId} — no winner`);
                playersInMatch.delete(opponent?.deviceId);
                
                // If tournament match, check if bye player should advance
                if (m.tournamentRound) {
                  const round = m.tournamentRound;
                  broadcastToSpectators('match_ended', {
                    matchId,
                    winner: null,
                    reason: 'Both players disconnected',
                  });
                  
                  // Check if round is complete and if there's a bye player waiting
                  const activeRoundMatches = [...matches.values()].filter(ma => ma.matchId !== matchId && ma.tournamentRound === round && ma.active);
                  const waitingWinners = bracketWinners.get(round) || [];
                  
                  console.log(`[forfeit] Round ${round}: ${activeRoundMatches.length} other matches active, ${waitingWinners.length} winners waiting`);
                  
                  if (activeRoundMatches.length === 0) {
                    if (waitingWinners.length >= 2) {
                      advanceToNextRound(round);
                    } else if (waitingWinners.length === 1) {
                      // The bye player wins!
                      declareTournamentChampion(waitingWinners[0]);
                    } else {
                      io.emit('tournament_no_winner', { round, message: 'All players eliminated — no champion.' });
                    }
                  }
                }
              }
              
              m.active = false;
              matches.delete(matchId);
            }
          }, TOURNAMENT_PACING.DISCONNECT_GRACE_SECONDS * 1000);
        }
      }
    }
  });

  // ── Spectator / view-screen registration ────────────────────────────────
  socket.on('spectator_join', () => {
    spectators.add(socket.id);
    sendViewState(socket);
    console.log(`[spectator] ${socket.id} joined view`);
  });

  // ── Register device + session token ─────────────────────────────────────
  socket.on('register_device', ({ deviceId, sessionToken }) => {
    if (isRateLimited(socket.id, 'register_device', 3, 5000)) {
      return recordViolation(socket, 'Rate limit: register_device');
    }
    if (!deviceId || typeof deviceId !== 'string' || deviceId.length > 80) {
      return recordViolation(socket, 'Invalid deviceId');
    }

    // Session token check — block duplicate tabs/windows trying to play twice
    if (sessionToken) {
      const ok = validateSession(socket, sessionToken, deviceId);
      if (!ok) {
        socket.emit('security_duplicate_session', {
          message: 'Another session is already active for this device. Please close other tabs.',
        });
        return;
      }
    }

    socket.data.deviceId = deviceId;
    socket.data.sessionToken = sessionToken;
    devices.set(deviceId, socket.id);
    
    // ── AUTO-RECONNECT: Restore player to active match if they had one ──
    // Check if player is in an active match and restore their connection
    for (const [matchId, match] of matches) {
      if (match.players[deviceId] && match.active) {
        const player = match.players[deviceId];
        const oldSocketId = player.socketId;
        
        // Update socketId to new connection
        player.socketId = socket.id;
        player.connected = true;
        player.disconnectedAt = null;
        
        // Re-join the match room
        socket.join(matchId);
        
        // Update registered players if this is a tournament
        const registered = registeredPlayers.get(deviceId);
        if (registered) {
          registered.socketId = socket.id;
        }
        
        // Also update winners queue if present
        const queueEntry = winnersQueue.get(deviceId);
        if (queueEntry) {
          queueEntry.socketId = socket.id;
        }
        
        console.log(`[reconnect] ${player.username} reconnected to match ${matchId} (old: ${oldSocketId}, new: ${socket.id})`);
        
        // Send current match state back to the reconnected player
        const opponent = Object.values(match.players).find(p => p.deviceId !== deviceId);
        socket.emit('match_reconnected', {
          matchId,
          matchSeed: match.seed,
          questionIds: (match.questions || []).map(q => q.id),
          questionIndex: match.questionIndex,
          totalQuestions: match.questions?.length || 5,
          currentQuestionId: match.questions?.[match.questionIndex]?.id || null,
          round: match.tournamentRound || 1,
          opponent: opponent ? { username: opponent.username, deviceId: opponent.deviceId } : null,
          myAnswer: player.answer,
          timeLeft: match.questionStartTime 
            ? Math.max(0, 10 - Math.floor((Date.now() - match.questionStartTime) / 1000))
            : 10,
          isTournament: !!match.tournamentRound,
        });
        
        // Notify opponent that player reconnected
        if (opponent) {
          const oppSocket = io.sockets.sockets.get(opponent.socketId);
          if (oppSocket) {
            oppSocket.emit('opponent_reconnected', { matchId });
          }
        }
        
        break; // Found the match, stop searching
      }
    }
    
    // Also restore tournament registration status
    const registered = registeredPlayers.get(deviceId);
    if (registered && !tournamentConfig.tournamentStarted) {
      registered.socketId = socket.id;
      console.log(`[reconnect] ${registered.username} restored to tournament registration`);
    }
  });

  // ── Request current state sync (reconnection / visibility change) ──────
  socket.on('request_state_sync', ({ deviceId }) => {
    if (!deviceId) return;
    
    // Build current state for this player
    const syncData = {
      timestamp: Date.now(),
    };
    
    // Check if in tournament registration mode
    if (isRegistrationMode()) {
      const player = registeredPlayers.get(deviceId);
      if (player) {
        syncData.stage = 'waiting';
        syncData.waitingCount = registeredPlayers.size;
        syncData.scheduledDate = tournamentConfig.scheduledDate;
        syncData.tournamentStarted = false;
      }
    } else if (tournamentConfig.tournamentStarted) {
      syncData.tournamentStarted = true;
    }
    
    // Check if in active match
    if (playersInMatch.has(deviceId)) {
      for (const [matchId, match] of matches) {
        if (match.p1?.deviceId === deviceId || match.p2?.deviceId === deviceId) {
          const isP1 = match.p1?.deviceId === deviceId;
          const opponent = isP1 ? match.p2 : match.p1;
          syncData.stage = 'match';
          syncData.matchId = matchId;
          syncData.opponent = opponent ? { username: opponent.username, id: opponent.deviceId } : null;
          syncData.tournament = {
            phase: 'in_match',
            matchId,
            currentQuestionIndex: match.currentQuestion || 0,
            round: match.tournamentRound || 1,
          };
          break;
        }
      }
    }
    
    // Check if in winners queue (waiting for next round)
    if (winnersQueue.has(deviceId)) {
      syncData.stage = 'waiting';
      syncData.tournament = {
        phase: 'waiting_match',
        round: winnersQueue.get(deviceId).round || currentRound,
      };
    }
    
    socket.emit('state_sync', syncData);
  });

  // ── Player joins the matchmaking lobby ──────────────────────────────────
  socket.on('join_lobby', ({ deviceId, username, sessionToken, isTournament }) => {
    if (isRateLimited(socket.id, 'join_lobby', 3, 10000)) {
      return recordViolation(socket, 'Rate limit: join_lobby');
    }
    if (!deviceId || !username || typeof username !== 'string') {
      return recordViolation(socket, 'Missing/invalid join_lobby fields');
    }
    if (username.length > 30) {
      return recordViolation(socket, 'Username too long');
    }

    // GUARD: Check if player is already in an active match
    if (playersInMatch.has(deviceId)) {
      console.log(`[join_lobby] ${username} is already in a match — rejecting`);
      socket.emit('already_in_match', { 
        message: 'You are already in an active match.',
        deviceId 
      });
      return;
    }
    
    // GUARD: If tournament is ACTIVE (started), don't allow new lobby joins
    // Instead, check if they're eliminated or if there's a champion
    if (tournamentConfig.tournamentStarted) {
      const registered = registeredPlayers.get(deviceId);
      
      // Check if there's already a champion (tournament over)
      const champion = [...registeredPlayers.values()].find(p => p.status === 'champion');
      if (champion) {
        socket.emit('tournament_ended_info', {
          message: 'Tournament has ended!',
          championUsername: champion.username,
        });
        console.log(`[join_lobby] ${username} tried to join but tournament ended (champion: ${champion.username})`);
        return;
      }
      
      // If registered and eliminated, tell them
      if (registered && registered.status === 'eliminated') {
        socket.emit('tournament_eliminated', {
          message: 'You have been eliminated from this tournament.',
          round: registered.round || 1,
        });
        console.log(`[join_lobby] ${username} tried to rejoin but was eliminated`);
        return;
      }
      
      // If registered and in waiting/active status, update their socket
      if (registered) {
        registered.socketId = socket.id;
        console.log(`[join_lobby] ${username} reconnected during active tournament`);
        
        // Check if they're in winnersQueue waiting for next match
        if (winnersQueue.has(deviceId)) {
          socket.emit('tournament_round_won', {
            message: 'Waiting for your next opponent...',
            round: registered.round,
          });
        }
        return;
      }
      
      // Not registered and tournament started — can't join
      socket.emit('tournament_in_progress', {
        message: 'Tournament is already in progress. Please wait for the next one.',
      });
      console.log(`[join_lobby] ${username} tried to join active tournament — rejected`);
      return;
    }

    socket.data.deviceId = deviceId;
    socket.data.username = username;
    socket.data.sessionToken = sessionToken;
    devices.set(deviceId, socket.id);

    // Session uniqueness check
    if (sessionToken) {
      const ok = validateSession(socket, sessionToken, deviceId);
      if (!ok) {
        socket.emit('security_duplicate_session', {
          message: 'Another session is already active. Only one active game per device is allowed.',
        });
        return;
      }
    }

    pruneLobby();

    // ── Tournament waiting path ──
    // A player belongs to the tournament if they are already registered
    // (added via /api/users with forTournament=true), or they explicitly
    // pass isTournament:true on this join. Casual players bypass this branch.
    if (isTournament || registeredPlayers.has(deviceId)) {
      // Refuse if tournament not in a registration state
      if (tournamentConfig.tournamentStarted) {
        socket.emit('tournament_in_progress', { message: 'Tournament is already in progress.' });
        return;
      }

      // Auto-register on socket if explicit flag (so the player doesn't need a separate REST call)
      if (!registeredPlayers.has(deviceId)) {
        if (registeredPlayers.size >= tournamentConfig.maxPlayers) {
          socket.emit('registration_error', {
            error: `Tournament is full (${tournamentConfig.maxPlayers}/${tournamentConfig.maxPlayers}).`,
            code: 'TOURNAMENT_FULL',
          });
          return;
        }
        registeredPlayers.set(deviceId, {
          username, deviceId, joinedAt: Date.now(),
          socketId: socket.id, wins: 0, round: 1, status: 'waiting',
        });
        if (!leaderboard.has(username)) {
          leaderboard.set(username, { username, wins: 0, stage: 'waiting' });
        }
        broadcastToSpectators('player_joined', { username, waitingCount: registeredPlayers.size });
      } else {
        // Reattach socketId for already-registered players
        const rp = registeredPlayers.get(deviceId);
        rp.socketId = socket.id;
      }

      const activeCount = getActivePlayerCount();
      socket.emit('tournament_waiting', {
        message: 'You are registered! Waiting for tournament to start...',
        waitingCount: registeredPlayers.size,
        activeCount,
        max: tournamentConfig.maxPlayers,
        rewardAmount: tournamentConfig.rewardAmount,
        scheduledDate: tournamentConfig.scheduledDate,
      });
      io.emit('waiting_count', { count: registeredPlayers.size, max: tournamentConfig.maxPlayers });
      io.emit('active_count', { count: activeCount, registered: registeredPlayers.size });

      console.log(`[tournament] ${username} waiting (${registeredPlayers.size}/${tournamentConfig.maxPlayers}, ${activeCount} active)`);

      // Auto-start the moment we hit the cap
      if (registeredPlayers.size >= tournamentConfig.maxPlayers) {
        console.log(`[tournament] 🚀 Reached max — auto-starting`);
        io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
        setImmediate(() => attemptTournamentStart());
      }
      return;
    }

    // Track in leaderboard
    if (!leaderboard.has(username)) {
      leaderboard.set(username, { username, wins: 0, stage: 'lobby' });
    }

    // Broadcast to view screens
    broadcastToSpectators('player_joined', { username, lobbyCount: lobby.size + 1 });
    broadcastLobbyCount();

    // Check if already in a match (reconnect scenario)
    for (const [matchId, match] of matches) {
      if (match.players[deviceId] && match.active) {
        // Reconnect — update socket reference
        match.players[deviceId].socketId = socket.id;
        match.players[deviceId].connected = true;
        socket.join(matchId);
        const opponent = Object.values(match.players).find(p => p.deviceId !== deviceId);
        socket.emit('match_rejoin', {
          matchId: match.matchId,
          seed: match.seed,
          questionIds: (match.questions || []).map(q => q.id),
          questionIndex: match.questionIndex,
          opponent: { username: opponent?.username, deviceId: opponent?.deviceId },
        });
        // Notify opponent the player is back
        socket.to(matchId).emit('opponent_reconnected');
        console.log(`[reconnect] ${username} rejoined ${matchId}`);
        return;
      }
    }

    // Try to pair with someone already waiting
    let paired = null;
    for (const [waitingDeviceId, entry] of lobby) {
      if (waitingDeviceId !== deviceId) {
        paired = entry;
        lobby.delete(waitingDeviceId);
        break;
      }
    }

    if (paired) {
      const p1 = { deviceId: paired.deviceId, username: paired.username, socketId: paired.socketId };
      const p2 = { deviceId, username, socketId: socket.id };
      const match = createMatch(p1, p2);

      socket.join(match.matchId);
      const p1Socket = io.sockets.sockets.get(paired.socketId);
      if (p1Socket) p1Socket.join(match.matchId);

      const payload = (myDeviceId) => {
        const opp = Object.values(match.players).find(p => p.deviceId !== myDeviceId);
        return {
          matchId: match.matchId,
          seed: match.seed,
          questionIds: (match.questions || []).map(q => q.id),
          opponent: { username: opp.username, deviceId: opp.deviceId },
        };
      };

      socket.emit('match_found', payload(deviceId));
      if (p1Socket) p1Socket.emit('match_found', payload(paired.deviceId));
      console.log(`[match] ${match.matchId}  ${paired.username} vs ${username}`);

      // Broadcast to view screens
      broadcastToSpectators('match_started', {
        matchId: match.matchId,
        p1: { username: p1.username, deviceId: p1.deviceId },
        p2: { username: p2.username, deviceId: p2.deviceId },
      });
      broadcastToSpectators('match_update', {
        matchId: match.matchId,
        players: {
          [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: null },
          [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: null },
        },
      });
      broadcastLobbyCount();
    } else {
      lobby.set(deviceId, { socketId: socket.id, username, deviceId, joinedAt: Date.now() });
      socket.emit('waiting_for_opponent');
      io.emit('lobby_count', { count: lobby.size });
      console.log(`[lobby] ${username} (${deviceId}) waiting…`);
    }
  });

  // ── NEW: Explicit queue join for tournament matchmaking ─────────────────
  socket.on('join_queue', ({ deviceId, username }) => {
    if (isRateLimited(socket.id, 'join_queue', 3, 5000)) {
      return recordViolation(socket, 'Rate limit: join_queue');
    }
    
    // Validate
    if (!deviceId || !username) {
      socket.emit('queue_error', { error: 'Missing deviceId or username' });
      return;
    }
    
    // GUARD: Can't join queue if already in match
    if (playersInMatch.has(deviceId)) {
      socket.emit('already_in_match', { message: 'You are already in an active match.' });
      return;
    }
    
    // GUARD: Already in queue
    if (waitingQueue.has(deviceId) || winnersQueue.has(deviceId)) {
      socket.emit('already_in_queue', { 
        message: 'You are already in the matchmaking queue.',
        queueSize: waitingQueue.size + winnersQueue.size
      });
      return;
    }
    
    // Add to waiting queue
    waitingQueue.set(deviceId, {
      deviceId,
      username,
      socketId: socket.id,
      round: 1,
      queuedAt: Date.now(),
      wins: 0,
    });
    
    console.log(`[waitingQueue] ${username} joined (${waitingQueue.size} waiting)`);
    socket.emit('queue_joined', { 
      position: waitingQueue.size,
      message: 'Looking for opponent...'
    });
    
    // Try instant pairing
    tryInstantQueuePair();
  });

  // ── Player submits answer ───────────────────────────────────────────────
  socket.on('submit_answer', ({ matchId, deviceId, answer, timeLeft, clientTimestamp }) => {
    if (isRateLimited(socket.id, 'submit_answer', 10, 15000)) {
      return recordViolation(socket, 'Rate limit: submit_answer');
    }

    const match = matches.get(matchId);
    if (!match || !match.active) return;

    const player = match.players[deviceId];
    if (!player || player.answer !== null) return; // already answered

    // Validate answer value
    const validOptions = [null, 'A', 'B', 'C', 'D'];
    if (!validOptions.includes(answer)) {
      return recordViolation(socket, `Invalid answer value: ${answer}`);
    }

    // Server-side timing check
    if (clientTimestamp && match.questionStartTime) {
      const elapsed = clientTimestamp - match.questionStartTime;
      if (elapsed < MIN_ANSWER_MS) {
        recordViolation(socket, `Answer too fast: ${elapsed}ms`);
        // Don't disconnect — just nullify the answer (treat as wrong)
        answer = null;
      }
    }

    player.answer    = answer;
    player.answerTime = Math.max(0, TOURNAMENT_PACING.QUESTION_TIME_SECONDS - (timeLeft || 0));

    socket.to(matchId).emit('opponent_answered');

    const playerList = Object.values(match.players);
    if (playerList.every(p => p.answer !== null)) evaluateRound(match, io);
  });

  // ── Timeout: player didn't answer in time ─────────────────────────────
  socket.on('answer_timeout', ({ matchId, deviceId }) => {
    if (isRateLimited(socket.id, 'answer_timeout', 10, 15000)) return;
    const match = matches.get(matchId);
    if (!match || !match.active) return;
    const player = match.players[deviceId];
    if (!player || player.answer !== null) return;
    player.answer = null;
    player.answerTime = TOURNAMENT_PACING.QUESTION_TIME_SECONDS;

    const playerList = Object.values(match.players);
    if (playerList.every(p => p.answer !== null)) evaluateRound(match, io);
  });

  // ── Back-navigation / visibility violation report ─────────────────────
  socket.on('report_violation', ({ matchId, type }) => {
    const deviceId = socket.data.deviceId;
    console.warn(`[⚠️  CLIENT VIOLATION] ${deviceId} — ${type} in match ${matchId}`);
    recordViolation(socket, `client_report: ${type}`);
  });

  // ── Admin live channel (real-time winner-submission notifications) ─────
  socket.on('admin_join', ({ token }) => {
    if (!token) return;
    try {
      jwt.verify(token, process.env.JWT_SECRET || 'dev-secret');
      adminSockets.add(socket.id);
      socket.emit('admin_joined', { ok: true });
      console.log(`[admin-socket] ${socket.id} joined admin channel`);
    } catch (_) {
      socket.emit('admin_joined', { ok: false, error: 'Invalid token' });
    }
  });

  // Update adminSockets cleanup on disconnect — handled below in the existing
  // disconnect handler via the wrapping cleanup pattern.
  socket.on('disconnect', () => {
    adminSockets.delete(socket.id);
  });
});

function broadcastToAdmins(event, data) {
  for (const sid of adminSockets) {
    const s = io.sockets.sockets.get(sid);
    if (s) s.emit(event, data);
  }
}

// ─── Round evaluation (server-authoritative) ──────────────────────────────────
function evaluateRound(match, io) {
  const [p1, p2] = Object.values(match.players);

  // Determine which question we're on
  const qIndex  = match.questionIndex;
  const question = match.questions ? match.questions[qIndex] : null;

  // If questions are from the frontend bank (question === null), we rely on
  // the frontend to evaluate — server just relays both answers
  if (!question) {
    // Relay both answers — use room broadcast but real socket for bots scenario
    const roundAnswersPayload = {
      questionIndex: qIndex,
      answers: {
        [p1.deviceId]: p1.answer,
        [p2.deviceId]: p2.answer,
      },
    };
    // Send to real players only (bots have no socket)
    [p1, p2].forEach(p => {
      if (!p.isBot) {
        const sock = io.sockets.sockets.get(p.socketId);
        if (sock) sock.emit('round_answers', roundAnswersPayload);
      }
    });
    // Broadcast to view screens
    broadcastToSpectators('match_update', {
      matchId: match.matchId,
      players: {
        [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: p1.answer ? '✓' : null },
        [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: p2.answer ? '✓' : null },
      },
    });
    // Reset for next question
    p1.answer = null; p1.answerTime = null;
    p2.answer = null; p2.answerTime = null;
    match.questionIndex++;
    return;
  }

  // Server-authoritative evaluation
  const p1Correct = p1.answer === question.correct;
  const p2Correct = p2.answer === question.correct;

  let p1Result, p2Result, matchOver = false;

  if (p1Correct && p2Correct) {
    // Both correct — continue with another question (no speed tiebreak)
    match.bothCorrectCount = (match.bothCorrectCount || 0) + 1;
    
    // Check if we've exhausted all questions in current set
    if (match.questionIndex >= match.questions.length - 1) {
      // Need more questions — fetch additional ones from the bank
      const usedIds = new Set(match.questions.map(q => q.id));
      const availableQuestions = questionBank.filter(q => !usedIds.has(q.id));
      
      if (availableQuestions.length > 0) {
        // Add 5 more questions (or however many are available)
        const newQuestions = seededShuffle(availableQuestions, match.matchId + '_extra_' + match.bothCorrectCount)
          .slice(0, 5);
        match.questions = [...match.questions, ...newQuestions];
        console.log(`[match] ${match.matchId} both correct ${match.bothCorrectCount}x — added ${newQuestions.length} more questions`);
      } else {
        // Truly exhausted all questions — use speed tiebreak as last resort
        console.log(`[match] ${match.matchId} exhausted all ${questionBank.length} questions — speed tiebreak`);
        p1Result = p1.answerTime <= p2.answerTime ? 'win' : 'lose';
        p2Result = p1Result === 'win' ? 'lose' : 'win';
        matchOver = true;
      }
    }
    
    if (!matchOver) {
      p1Result = 'both_correct';
      p2Result = 'both_correct';
      match.questionIndex++;
      match.questionStartTime = Date.now();
      
      // Reset answers BEFORE sending next question
      p1.answer = null; p1.answerTime = null;
      p2.answer = null; p2.answerTime = null;
      
      // Restart server timer for next question
      cleanupMatchTimer(match.matchId);
      startMatchTimer(match);
      
      // Send the next question to both players (inline the question object so
      // clients don't depend on their local bank cache being loaded).
      const nextQuestion = match.questions[match.questionIndex];
      const nextQuestionPayload = {
        questionIndex: match.questionIndex,
        questionId: nextQuestion.id,
        question: {
          id: nextQuestion.id,
          question: nextQuestion.question,
          options: nextQuestion.options,
          category: nextQuestion.category || 'General',
        },
        bothCorrectCount: match.bothCorrectCount,
        totalQuestions: match.questions.length,
        message: 'Both correct! Here\'s another question.',
        isTournament: !!match.tournamentRound,
      };
      
      [p1, p2].forEach(player => {
        const sock = io.sockets.sockets.get(player.socketId);
        if (sock) sock.emit('next_question', nextQuestionPayload);
      });
      
      // Don't emit round_result for both_correct — next_question is sufficient
      // Just broadcast to spectators and return early
      broadcastToSpectators('both_correct', {
        matchId: match.matchId,
        p1: p1.username,
        p2: p2.username,
        questionIndex: match.questionIndex,
      });
      
      return; // Exit early — don't emit round_result
    }
  } else if (p1Correct) {
    p1Result = 'win'; p2Result = 'lose'; matchOver = true;
  } else if (p2Correct) {
    p1Result = 'lose'; p2Result = 'win'; matchOver = true;
  } else {
    // Both wrong
    if (match.tournamentRound) {
      // Tournament: give ONE more chance; if both wrong again, eliminate both
      match.bothWrongCount = (match.bothWrongCount || 0) + 1;

      if (match.bothWrongCount >= 2) {
        console.log(`[match] ${match.matchId} both wrong ${match.bothWrongCount}x — eliminating both`);
        p1Result = 'gameover'; p2Result = 'gameover'; matchOver = true;
      } else if (match.questionIndex >= match.questions.length - 1) {
        const usedIds = new Set(match.questions.map(q => q.id));
        const availableQuestions = questionBank.filter(q => !usedIds.has(q.id));

        if (availableQuestions.length > 0) {
          const newQuestions = seededShuffle(availableQuestions, match.matchId + '_bw_' + match.bothWrongCount)
            .slice(0, 5);
          match.questions = [...match.questions, ...newQuestions];
          console.log(`[match] ${match.matchId} both wrong ${match.bothWrongCount}x — added ${newQuestions.length} more questions`);
        } else {
          // Truly exhausted all questions — eliminate both as absolute last resort
          console.log(`[match] ${match.matchId} exhausted all ${questionBank.length} questions — eliminating both`);
          p1Result = 'gameover'; p2Result = 'gameover'; matchOver = true;
        }
      }
      
      if (!matchOver) {
        p1Result = 'both_wrong';
        p2Result = 'both_wrong';
        
        // Save answers before resetting (needed for round_result emission)
        const p1OrigAnswer = p1.answer;
        const p2OrigAnswer = p2.answer;
        
        match.questionIndex++;
        match.questionStartTime = Date.now();
        
        // Reset answers
        p1.answer = null; p1.answerTime = null;
        p2.answer = null; p2.answerTime = null;
        
        // Restart server timer for next question
        cleanupMatchTimer(match.matchId);
        startMatchTimer(match);
        
        // Send the next question to both players. Include the full question
        // object (sans `correct`) so the client doesn't depend on its local
        // bank cache — avoids "no question shown" race.
        const nextQuestion = match.questions[match.questionIndex];
        const nextQuestionPayload = {
          questionIndex: match.questionIndex,
          questionId: nextQuestion.id,
          question: {
            id: nextQuestion.id,
            question: nextQuestion.question,
            options: nextQuestion.options,
            category: nextQuestion.category || 'General',
          },
          bothWrongCount: match.bothWrongCount,
          totalQuestions: match.questions.length,
          message: 'Both wrong! Try another question.',
          isTournament: true,
        };
        
        // Emit round_result so players see red highlight, then send next question after a delay
        const emitBothWrong = (player, myOrigAnswer, oppOrigAnswer) => {
          const sock = io.sockets.sockets.get(player.socketId);
          if (sock) {
            sock.emit('round_result', {
              result: 'both_wrong',
              questionIndex: qIndex,
              correctAnswer: question.correct,
              myAnswer: myOrigAnswer,
              opponentAnswer: oppOrigAnswer,
              matchOver: false,
              isTournament: true,
            });
            // After 2s delay, send the next question
            setTimeout(() => {
              sock.emit('next_question', nextQuestionPayload);
            }, 2000);
          }
        };
        emitBothWrong(p1, p1OrigAnswer, p2OrigAnswer);
        emitBothWrong(p2, p2OrigAnswer, p1OrigAnswer);
        
        broadcastToSpectators('both_wrong', {
          matchId: match.matchId,
          p1: p1.username,
          p2: p2.username,
          questionIndex: match.questionIndex,
          bothWrongCount: match.bothWrongCount,
        });
        
        return; // Exit early — match continues
      }
    } else {
      // Non-tournament: both wrong ends the match
      p1Result = 'gameover'; p2Result = 'gameover'; matchOver = true;
    }
  }

  // Emit result to each player
  const emit = (player, result) => {
    const sock = io.sockets.sockets.get(player.socketId);
    if (sock) {
      sock.emit('round_result', {
        result,
        questionIndex: qIndex,
        correctAnswer: question.correct,
        myAnswer: player.answer,
        opponentAnswer: Object.values(match.players).find(p => p.deviceId !== player.deviceId).answer,
        matchOver,
        isTournament: !!match.tournamentRound,
      });
    }
  };
  emit(p1, p1Result);
  emit(p2, p2Result);

  // Broadcast answer progress to view screens (anonymised)
  broadcastToSpectators('match_update', {
    matchId: match.matchId,
    players: {
      [p1.deviceId]: { username: p1.username, deviceId: p1.deviceId, answer: p1.answer ? '✓' : null },
      [p2.deviceId]: { username: p2.username, deviceId: p2.deviceId, answer: p2.answer ? '✓' : null },
    },
  });

  // At this point, matchOver is true (both_correct and tournament both_wrong return early above)
  const winner = p1Result === 'win' ? p1 : p2Result === 'win' ? p2 : null;
  const loser  = p1Result === 'lose' ? p1 : p2Result === 'lose' ? p2 : null;

  // Update leaderboard
  if (winner) {
    const wb = leaderboard.get(winner.username) || { username: winner.username, wins: 0, totalTime: 0 };
    wb.wins = (wb.wins || 0) + 1;
    const winnerAnswerTime = winner.answerTime || 0;
    wb.totalTime = (wb.totalTime || 0) + winnerAnswerTime;
    leaderboard.set(winner.username, wb);
    broadcastLeaderboard();
  }

  // Broadcast elimination + match-ended to view screens
  if (loser) {
    broadcastToSpectators('player_eliminated', { username: loser.username });
  } else if (p1Result === 'gameover' && p2Result === 'gameover') {
    // Both eliminated (2-strike both-wrong) — notify view screens of BOTH
    broadcastToSpectators('player_eliminated', { username: p1.username });
    broadcastToSpectators('player_eliminated', { username: p2.username });
  }
  broadcastToSpectators('match_ended', {
    matchId: match.matchId,
    winner: winner?.username ?? null,
    loser:  loser?.username ?? null,
  });

  match.active = false;
  
  // Clean up match timer
  cleanupMatchTimer(match.matchId);
  
  // IMMEDIATELY remove players from playersInMatch (allows re-queueing)
  playersInMatch.delete(p1.deviceId);
  playersInMatch.delete(p2.deviceId);
  
  setTimeout(() => matches.delete(match.matchId), 30000); // clean up after 30s (reduced from 2min)

  // ── Tournament elimination bracket logic ──────────────────────────────
  // Data updates happen immediately; socket emissions are delayed so players see answer feedback
  if (match.tournamentRound) {
    const RESULT_DISPLAY_MS = 2000; // 2s for players to see correct/incorrect answer highlight
    const round = match.tournamentRound;

    // Update data immediately (so admin API shows correct stats)
    if (loser) {
      const lp = registeredPlayers.get(loser.deviceId);
      if (lp) lp.status = 'eliminated';
      waitingQueue.delete(loser.deviceId);
      winnersQueue.delete(loser.deviceId);
      TournamentPlayer.findOneAndUpdate(
        { deviceId: loser.deviceId, tournamentId: tournamentConfig.scheduledDate },
        { status: 'eliminated' }
      ).catch(e => console.error('[bracket] DB evict error:', e.message));
    }

    if (winner) {
      const wp = registeredPlayers.get(winner.deviceId);
      if (wp) {
        wp.wins = (wp.wins || 0) + 1;
        wp.round = round + 1;
        wp.status = 'waiting';
      }
      TournamentPlayer.findOneAndUpdate(
        { deviceId: winner.deviceId, tournamentId: tournamentConfig.scheduledDate },
        { $inc: { wins: 1 }, round: round + 1 }
      ).catch(e => console.error('[bracket] DB winner update error:', e.message));
    } else {
      // Both wrong AND all questions exhausted (extreme edge case) — eliminate both
      const lp1 = registeredPlayers.get(p1.deviceId);
      const lp2 = registeredPlayers.get(p2.deviceId);
      if (lp1) lp1.status = 'eliminated';
      if (lp2) lp2.status = 'eliminated';
      waitingQueue.delete(p1.deviceId);
      waitingQueue.delete(p2.deviceId);
      winnersQueue.delete(p1.deviceId);
      winnersQueue.delete(p2.deviceId);
    }

    // Delay socket emissions so players see the answer highlight for 2s
    setTimeout(() => {
      if (loser) {
        const loserSocket = io.sockets.sockets.get(loser.socketId);
        if (loserSocket) loserSocket.emit('tournament_eliminated', {
          message: 'You have been eliminated from the tournament.',
          round,
        });
        console.log(`[tournament R${round}] Eliminated: ${loser.username}`);
      }

      if (winner) {
        const wp = registeredPlayers.get(winner.deviceId);
        const winnerSocket = io.sockets.sockets.get(winner.socketId);
        if (winnerSocket) {
          winnerSocket.emit('tournament_round_won', {
            message: `You won Round ${round}! Waiting for next round...`,
            round,
            nextRound: round + 1,
            wins: wp?.wins || 1,
          });
        }

        // Queue winner for next round. Carry the match duration so that, if
        // the next round has an odd count (e.g. a forfeit), the SLOWEST
        // winner is the one dropped rather than a random pick.
        const matchDurationMs = match.startTime ? Date.now() - match.startTime : Number.MAX_SAFE_INTEGER;
        queueWinnerForNextRound(
          {
            deviceId: winner.deviceId,
            username: winner.username,
            socketId: winner.socketId,
            wins: (wp?.wins || 1),
            matchDurationMs,
          },
          round
        );
      } else {
        // Both wrong AND all questions exhausted — eliminate both (extreme edge case)
        console.log(`[tournament R${round}] Both wrong & all questions exhausted — eliminating ${p1.username} and ${p2.username}`);
        const s1 = io.sockets.sockets.get(p1.socketId);
        const s2 = io.sockets.sockets.get(p2.socketId);
        if (s1) s1.emit('tournament_eliminated', {
          message: 'Both players answered incorrectly. You have been eliminated.',
          round,
        });
        if (s2) s2.emit('tournament_eliminated', {
          message: 'Both players answered incorrectly. You have been eliminated.',
          round,
        });

        // Check if round is now complete
        const activeRoundMatches = [...matches.values()].filter(m => m.tournamentRound === round && m.active);
        const waitingWinners = bracketWinners.get(round) || [];

        if (activeRoundMatches.length === 0) {
          if (waitingWinners.length >= 2) advanceToNextRound(round);
          else if (waitingWinners.length === 1) declareTournamentChampion(waitingWinners[0]);
          else {
            io.emit('tournament_no_winner', { round, message: 'All players eliminated — no champion this round.' });
          }
        }
      }
    }, RESULT_DISPLAY_MS);
  }
}

// ─── Tournament player registration (save username + deviceId to MongoDB) ──────
// Called from the frontend when a user wants to join the tournament.
// Also saves to the persistent User collection for general user tracking.
app.post('/api/users', async (req, res) => {
  try {
    let { username, deviceId } = req.body;

    if (!username || !deviceId) {
      return res.status(400).json({ error: 'username and deviceId are required' });
    }

    // Normalize username: trim whitespace and convert to lowercase
    username = String(username).trim().toLowerCase();

    // Validate username
    if (username.length < 3) {
      return res.status(400).json({ error: 'Username must be at least 3 characters' });
    }
    if (username.length > 30) {
      return res.status(400).json({ error: 'Username must be 30 characters or less' });
    }
    // Only allow alphanumeric characters, underscores, and hyphens
    if (!/^[a-z0-9_-]+$/.test(username)) {
      return res.status(400).json({ error: 'Username can only contain letters, numbers, underscores, and hyphens' });
    }
    // Check for reserved/inappropriate usernames
    const reservedUsernames = ['admin', 'administrator', 'system', 'bot', 'null', 'undefined', 'test'];
    if (reservedUsernames.includes(username)) {
      return res.status(400).json({ error: 'This username is not allowed' });
    }

    const forTournament = !!req.body.forTournament;
    const hasMongo = mongoUp();

    // Hard block: tournament already running → no new joiners.
    // (Existing registered players reconnecting hit the socket path, not this.)
    if (forTournament && tournamentConfig.tournamentStarted) {
      return res.status(409).json({
        error: 'Tournament is already in progress. Please wait for the next one.',
        code: 'TOURNAMENT_IN_PROGRESS',
      });
    }

    // ── Username/device uniqueness checks ──
    let existingUser = null;
    if (hasMongo) {
      existingUser = await User.findOne({ deviceId });
      if (!existingUser) {
        const takenByName = await User.findOne({ username });
        if (takenByName) {
          return res.status(409).json({ error: 'Username is already taken. Please choose another.' });
        }
      }
    } else {
      // In-memory fallback when Mongo is down: check across known registeredPlayers + lobby + leaderboard
      for (const p of registeredPlayers.values()) {
        if (p.deviceId === deviceId) { existingUser = { username: p.username, deviceId }; break; }
        if (p.username === username) {
          return res.status(409).json({ error: 'Username is already taken. Please choose another.' });
        }
      }
    }

    // Create user record (Mongo) — skipped without Mongo
    let user = existingUser;
    if (!existingUser && hasMongo) {
      user = await User.create({ username, deviceId });
    } else if (!existingUser) {
      user = { username, deviceId, _ephemeral: true };
    }

    // ── Tournament registration (only when caller asked for it) ──
    if (forTournament && !tournamentConfig.tournamentStarted) {
      if (!registeredPlayers.has(deviceId)) {
        if (registeredPlayers.size >= tournamentConfig.maxPlayers) {
          return res.status(409).json({
            error: `Tournament is full (${tournamentConfig.maxPlayers}/${tournamentConfig.maxPlayers}). Please wait for the next one.`,
            code: 'TOURNAMENT_FULL',
          });
        }

        if (hasMongo && tournamentConfig.scheduledDate) {
          await TournamentPlayer.findOneAndUpdate(
            { deviceId, tournamentId: tournamentConfig.scheduledDate },
            { username, deviceId, tournamentId: tournamentConfig.scheduledDate, status: 'waiting', wins: 0, round: 1 },
            { upsert: true, returnDocument: 'after', runValidators: true }
          ).catch(e => console.error('[api/users] TournamentPlayer upsert error:', e.message));
        }

        registeredPlayers.set(deviceId, {
          username, deviceId, joinedAt: Date.now(),
          socketId: null, wins: 0, round: 1, status: 'waiting',
        });

        if (!leaderboard.has(username)) {
          leaderboard.set(username, { username, wins: 0, stage: 'waiting' });
        }

        broadcastToSpectators('player_joined', { username, waitingCount: registeredPlayers.size });
        io.emit('waiting_count', { count: registeredPlayers.size, max: tournamentConfig.maxPlayers });

        console.log(`[tournament] ${username} registered via REST (${registeredPlayers.size}/${tournamentConfig.maxPlayers})`);

        if (registeredPlayers.size >= tournamentConfig.maxPlayers) {
          console.log(`[tournament] 🚀 Reached max ${tournamentConfig.maxPlayers} — auto-starting`);
          io.emit('tournament_countdown', { secondsRemaining: 0, message: 'Tournament starting NOW!' });
          setImmediate(() => attemptTournamentStart());
        }
      }

      return res.status(200).json({
        ok: true,
        registered: true,
        alreadyExists: !!existingUser,
        waitingCount: registeredPlayers.size,
        max: tournamentConfig.maxPlayers,
        rewardAmount: tournamentConfig.rewardAmount,
        scheduledDate: tournamentConfig.scheduledDate,
        user: { username, deviceId },
        message: existingUser ? "You're already in!" : 'Registered! Waiting for tournament to start.',
      });
    }

    return res.status(existingUser ? 200 : 201).json({
      ok: true,
      registered: false,
      alreadyExists: !!existingUser,
      user: { username: user.username, deviceId: user.deviceId },
      message: existingUser ? "You're already in!" : 'User saved.',
    });
  } catch (err) {
    console.error('[api/users] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get all players
app.get('/api/users', async (req, res) => {
  try {
    if (mongoUp()) {
      const users = await User.find({}, { username: 1, deviceId: 1, createdAt: 1, _id: 0 })
        .sort({ createdAt: -1 });
      return res.json({ ok: true, count: users.length, users });
    }
    // No Mongo: return current in-memory tournament + leaderboard players
    const users = [...registeredPlayers.values()].map(p => ({ username: p.username, deviceId: p.deviceId }));
    res.json({ ok: true, count: users.length, users });
  } catch (err) {
    console.error('[api/users] GET all error:', err.message);
    res.json({ ok: true, count: 0, users: [] });
  }
});

// Get total number of registered players
// NOTE: This must come BEFORE /api/users/:deviceId to avoid "count" being treated as a deviceId
app.get('/api/users/count', async (req, res) => {
  try {
    if (mongoUp()) {
      const count = await User.countDocuments();
      return res.json({ ok: true, count });
    }
    // No Mongo: report in-memory registered count
    res.json({ ok: true, count: registeredPlayers.size });
  } catch (err) {
    console.error('[api/users/count] Error:', err.message);
    res.json({ ok: true, count: registeredPlayers.size });
  }
});

// Get user by username (for frontend validation of cached users)
// NOTE: This must come BEFORE /api/users/:deviceId to avoid "username" being treated as a deviceId
app.get('/api/users/username/:username', async (req, res) => {
  try {
    // Normalize username to lowercase for case-insensitive lookup
    const username = String(req.params.username).trim().toLowerCase();
    const user = await User.findOne({ username });
    if (!user) return res.status(404).json({ error: 'User not found' });
    res.json({ ok: true, user: { username: user.username, deviceId: user.deviceId, createdAt: user.createdAt } });
  } catch (err) {
    console.error('[api/users/username] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Get user by deviceId
app.get('/api/users/:deviceId', async (req, res) => {
  try {
    const user = await User.findOne({ deviceId: req.params.deviceId });
    if (!user) return res.status(404).json({ error: 'User not found' });
    res.json(user);
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// ─── Admin login ──────────────────────────────────────────────────────────────
app.post('/admin/login', (req, res) => {
  const { email, password } = req.body;

  if (!email || !password) {
    return res.status(400).json({ error: 'email and password are required' });
  }

  if (email !== ADMIN_EMAIL || password !== ADMIN_PASSWORD) {
    return res.status(401).json({ error: 'Invalid credentials' });
  }

  const token = jwt.sign(
    { email },
    process.env.JWT_SECRET || 'dev-secret',
    { expiresIn: '24h' }
  );

  res.json({ ok: true, token, admin: { email } });
});

// ─── Admin auth middleware ────────────────────────────────────────────────────
function requireAdmin(req, res, next) {
  const authHeader = req.headers.authorization;
  if (!authHeader || !authHeader.startsWith('Bearer ')) {
    return res.status(401).json({ error: 'No token provided' });
  }
  try {
    const token = authHeader.split(' ')[1];
    const decoded = jwt.verify(token, process.env.JWT_SECRET || 'dev-secret');
    req.admin = decoded;
    next();
  } catch {
    return res.status(401).json({ error: 'Invalid or expired token' });
  }
}

// ─── Question Bank ───────────────────────────────────────────────────────────
// Questions live in MongoDB and are mirrored to an in-memory cache for fast,
// synchronous reads during matchmaking. Population paths:
//   1. Direct DB inserts (mongosh / Compass / `node seedQuestions.js`)
//      then call `POST /admin/questions/refresh` to reload the cache.
//   2. `POST /admin/questions` to replace the entire bank from the admin panel
//      (writes to DB if connected, always updates the in-memory cache).

// Body: { questions: [ { id, question, options:{A,B,C,D}, correct, category } ] }
app.post('/admin/questions', requireAdmin, async (req, res) => {
  const { questions } = req.body || {};
  if (!Array.isArray(questions)) {
    return res.status(400).json({ error: 'questions must be an array' });
  }
  // Validate basic shape
  for (const q of questions) {
    if (!q || !q.id || !q.question || !q.options ||
        !['A','B','C','D'].includes(q.correct)) {
      return res.status(400).json({ error: 'Invalid question shape', offender: q?.id || null });
    }
  }

  // Persist to MongoDB when connected (replace strategy)
  if (mongoUp()) {
    try {
      await Question.deleteMany({});
      if (questions.length > 0) {
        await Question.insertMany(questions, { ordered: false });
      }
      console.log(`[admin] Persisted ${questions.length} questions to MongoDB`);
    } catch (e) {
      console.error('[admin] Failed to persist questions to MongoDB:', e.message);
      return res.status(500).json({ error: 'Failed to persist to database', detail: e.message });
    }
  }

  // Update the in-memory cache. Done after DB write so the cache reflects DB state.
  questionBank = questions;
  io.emit('question_bank_updated', { count: questionBank.length });
  broadcastToAdmins('question_bank_updated', { count: questionBank.length });
  console.log(`[admin] Question bank updated — ${questionBank.length} questions in memory`);
  res.json({ ok: true, count: questionBank.length, persistedToDb: mongoUp() });
});

// Manually reload the in-memory cache. Uses MongoDB when connected,
// otherwise falls back to `questions.example.json`. Use this after editing
// the DB or the JSON file — no server restart needed.
app.post('/admin/questions/refresh', requireAdmin, async (_req, res) => {
  let count;
  if (mongoUp()) {
    count = await loadQuestionBankFromDB();
    if (count === 0) count = loadQuestionBankFromFile();
  } else {
    count = loadQuestionBankFromFile();
  }
  io.emit('question_bank_updated', { count });
  broadcastToAdmins('question_bank_updated', { count });
  res.json({ ok: true, count, source: mongoUp() && count > 0 ? 'mongo+file' : (mongoUp() ? 'mongo' : 'file') });
});

app.get('/api/questions/count', (_, res) => res.json({ count: questionBank.length }));
app.get('/admin/questions', requireAdmin, (_, res) => res.json({ count: questionBank.length, questions: questionBank }));

// Public: returns the bank without the `correct` field so clients can render
// questions locally during matches. Server still validates answers against
// its own (full) copy of the bank.
app.get('/api/questions', (_, res) => {
  const sanitized = questionBank.map(q => ({
    id: q.id,
    question: q.question,
    options: q.options,
    category: q.category || 'General',
  }));
  res.json({ count: sanitized.length, questions: sanitized });
});

// ─── Admin: set tournament reward amount ─────────────────────────────────────
app.post('/admin/tournament/reward', requireAdmin, (req, res) => {
  const { rewardAmount } = req.body || {};
  if (typeof rewardAmount !== 'string') {
    return res.status(400).json({ error: 'rewardAmount must be a string (e.g. "₦20,000")' });
  }
  tournamentConfig.rewardAmount = rewardAmount.slice(0, 80);
  io.emit('tournament_config_updated', {
    rewardAmount: tournamentConfig.rewardAmount,
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    maxPlayers: tournamentConfig.maxPlayers,
  });
  console.log(`[admin] Reward amount set: ${tournamentConfig.rewardAmount}`);
  res.json({ ok: true, rewardAmount: tournamentConfig.rewardAmount });
});

// In-memory store used when Mongo is not connected
const inMemoryWinnerSubs = []; // [{ _id, ...fields }]

// ─── Winner submission: only the champion can submit their reward details ────
app.post('/api/tournament/winner-submit', async (req, res) => {
  try {
    const { deviceId, accountNumber, accountName, bankName, message } = req.body || {};
    if (!deviceId || !accountNumber) {
      return res.status(400).json({ error: 'deviceId and accountNumber are required' });
    }
    const player = registeredPlayers.get(deviceId);
    if (!player || player.status !== 'champion') {
      return res.status(403).json({ error: 'Only the tournament champion can submit reward details.' });
    }
    const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || 'live';

    const payload = {
      tournamentId,
      username: player.username,
      deviceId,
      accountNumber: String(accountNumber).trim().slice(0, 40),
      accountName: String(accountName || '').trim().slice(0, 80),
      bankName: String(bankName || '').trim().slice(0, 80),
      message: String(message || '').trim().slice(0, 500),
      rewardAmount: tournamentConfig.rewardAmount || '',
    };

    let doc;
    if (mongoUp()) {
      doc = await WinnerSubmission.findOneAndUpdate(
        { deviceId, tournamentId },
        payload,
        { upsert: true, new: true, runValidators: true }
      );
    } else {
      // In-memory fallback: upsert into the local array
      const existingIdx = inMemoryWinnerSubs.findIndex(s => s.deviceId === deviceId && s.tournamentId === tournamentId);
      const now = new Date();
      const record = {
        _id: existingIdx >= 0 ? inMemoryWinnerSubs[existingIdx]._id : 'mem_' + Date.now(),
        ...payload,
        paid: existingIdx >= 0 ? inMemoryWinnerSubs[existingIdx].paid : false,
        createdAt: existingIdx >= 0 ? inMemoryWinnerSubs[existingIdx].createdAt : now,
        updatedAt: now,
      };
      if (existingIdx >= 0) inMemoryWinnerSubs[existingIdx] = record;
      else inMemoryWinnerSubs.unshift(record);
      doc = record;
    }

    broadcastToAdmins('winner_submission', {
      submission: {
        _id: doc._id,
        tournamentId: doc.tournamentId,
        username: doc.username,
        deviceId: doc.deviceId,
        accountNumber: doc.accountNumber,
        accountName: doc.accountName,
        bankName: doc.bankName,
        message: doc.message,
        rewardAmount: doc.rewardAmount,
        createdAt: doc.createdAt,
      },
    });
    console.log(`[winner-submit] ${player.username} submitted account details for ${tournamentId}`);
    res.json({ ok: true, submission: doc });
  } catch (err) {
    console.error('[winner-submit] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: list all winner submissions
app.get('/admin/tournament/winners', requireAdmin, async (_req, res) => {
  try {
    if (mongoUp()) {
      const list = await WinnerSubmission.find({}).sort({ createdAt: -1 }).limit(200);
      return res.json({ ok: true, count: list.length, submissions: list });
    }
    res.json({ ok: true, count: inMemoryWinnerSubs.length, submissions: inMemoryWinnerSubs });
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: mark a winner submission as paid
app.post('/admin/tournament/winners/:id/paid', requireAdmin, async (req, res) => {
  try {
    if (mongoUp()) {
      const doc = await WinnerSubmission.findByIdAndUpdate(req.params.id, { paid: true }, { new: true });
      if (!doc) return res.status(404).json({ error: 'Submission not found' });
      broadcastToAdmins('winner_submission_updated', { id: doc._id, paid: doc.paid });
      return res.json({ ok: true, submission: doc });
    }
    const idx = inMemoryWinnerSubs.findIndex(s => s._id === req.params.id);
    if (idx < 0) return res.status(404).json({ error: 'Submission not found' });
    inMemoryWinnerSubs[idx] = { ...inMemoryWinnerSubs[idx], paid: true };
    broadcastToAdmins('winner_submission_updated', { id: req.params.id, paid: true });
    res.json({ ok: true, submission: inMemoryWinnerSubs[idx] });
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// ─── Winner ⇄ Admin chat ─────────────────────────────────────────────────────
// Messages are appended to the WinnerSubmission doc for the active tournament.
// Both sides get a `chat_message` socket event in real time.

function findSubByDeviceId(deviceId) {
  if (mongoUp()) {
    const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || 'live';
    return WinnerSubmission.findOne({ deviceId, tournamentId });
  }
  const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || 'live';
  return Promise.resolve(
    inMemoryWinnerSubs.find(s => s.deviceId === deviceId && s.tournamentId === tournamentId) || null
  );
}

function emitChatMessage(deviceId, message) {
  // Push to admin sockets
  broadcastToAdmins('chat_message', { deviceId, message });
  // Push to the winner's own socket
  const player = registeredPlayers.get(deviceId);
  if (player && player.socketId) {
    const sock = io.sockets.sockets.get(player.socketId);
    if (sock) sock.emit('chat_message', { deviceId, message });
  }
}

async function appendChatMessage(deviceId, from, text) {
  const cleanText = String(text || '').trim().slice(0, 1000);
  if (!cleanText) return null;
  const message = { from, text: cleanText, createdAt: new Date() };

  if (mongoUp()) {
    const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || 'live';
    const doc = await WinnerSubmission.findOneAndUpdate(
      { deviceId, tournamentId },
      { $push: { messages: message } },
      { new: true }
    );
    if (!doc) return null;
    const saved = doc.messages[doc.messages.length - 1];
    return {
      _id: saved._id,
      from: saved.from,
      text: saved.text,
      createdAt: saved.createdAt,
    };
  }

  // In-memory fallback
  const tournamentId = tournamentConfig.tournamentId || tournamentConfig.scheduledDate || 'live';
  const rec = inMemoryWinnerSubs.find(s => s.deviceId === deviceId && s.tournamentId === tournamentId);
  if (!rec) return null;
  rec.messages = rec.messages || [];
  const stored = { _id: 'mem_msg_' + Date.now() + '_' + Math.random().toString(36).slice(2, 6), ...message };
  rec.messages.push(stored);
  return stored;
}

// Winner sends a chat message. Only the recorded champion device can post.
app.post('/api/tournament/chat', async (req, res) => {
  try {
    const { deviceId, text } = req.body || {};
    if (!deviceId || !text) return res.status(400).json({ error: 'deviceId and text are required' });
    const player = registeredPlayers.get(deviceId);
    if (!player || player.status !== 'champion') {
      return res.status(403).json({ error: 'Only the tournament champion can chat here.' });
    }
    const sub = await findSubByDeviceId(deviceId);
    if (!sub) {
      return res.status(409).json({ error: 'Submit your account details first.' });
    }
    const message = await appendChatMessage(deviceId, 'winner', text);
    if (!message) return res.status(400).json({ error: 'Empty message' });
    emitChatMessage(deviceId, message);
    res.json({ ok: true, message });
  } catch (err) {
    console.error('[chat] winner send error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin sends a chat message to a specific winner.
app.post('/admin/tournament/chat/:deviceId', requireAdmin, async (req, res) => {
  try {
    const { deviceId } = req.params;
    const { text } = req.body || {};
    if (!text) return res.status(400).json({ error: 'text is required' });
    const sub = await findSubByDeviceId(deviceId);
    if (!sub) return res.status(404).json({ error: 'No winner submission for that device.' });
    const message = await appendChatMessage(deviceId, 'admin', text);
    if (!message) return res.status(400).json({ error: 'Empty message' });
    emitChatMessage(deviceId, message);
    res.json({ ok: true, message });
  } catch (err) {
    console.error('[chat] admin send error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Winner fetches their own chat history (after submitting details).
app.get('/api/tournament/chat/:deviceId', async (req, res) => {
  try {
    const sub = await findSubByDeviceId(req.params.deviceId);
    if (!sub) return res.json({ ok: true, messages: [] });
    res.json({ ok: true, messages: sub.messages || [] });
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin fetches chat thread for a specific winner.
app.get('/admin/tournament/chat/:deviceId', requireAdmin, async (req, res) => {
  try {
    const sub = await findSubByDeviceId(req.params.deviceId);
    if (!sub) return res.json({ ok: true, submission: null, messages: [] });
    res.json({
      ok: true,
      submission: {
        _id: sub._id,
        username: sub.username,
        deviceId: sub.deviceId,
        rewardAmount: sub.rewardAmount,
        paid: sub.paid,
        accountNumber: sub.accountNumber,
        accountName: sub.accountName,
        bankName: sub.bankName,
      },
      messages: sub.messages || [],
    });
  } catch (err) {
    res.status(500).json({ error: 'Server error' });
  }
});

// ─── Leaderboard REST endpoint ────────────────────────────────────────────────
app.get('/leaderboard', (_, res) => res.json(getLeaderboardArray()));

// ─── Debug/Diagnostic endpoint ────────────────────────────────────────────────
// Returns current state of all queues and matches for debugging
app.get('/debug/state', (_, res) => {
  const activeMatches = [...matches.values()].filter(m => m.active);
  
  res.json({
    timestamp: new Date().toISOString(),
    queues: {
      waitingQueue: {
        size: waitingQueue.size,
        players: [...waitingQueue.values()].map(p => ({
          username: p.username,
          deviceId: p.deviceId.slice(0, 8) + '...',
          queuedAt: new Date(p.queuedAt).toISOString(),
          round: p.round,
        })),
      },
      winnersQueue: {
        size: winnersQueue.size,
        players: [...winnersQueue.values()].map(p => ({
          username: p.username,
          deviceId: p.deviceId.slice(0, 8) + '...',
          round: p.round,
          wins: p.wins,
        })),
      },
    },
    matches: {
      total: matches.size,
      active: activeMatches.length,
      activeList: activeMatches.map(m => ({
        matchId: m.matchId,
        round: m.tournamentRound,
        questionIndex: m.questionIndex,
        players: Object.values(m.players).map(p => ({
          username: p.username,
          answered: p.answer !== null,
          connected: p.connected,
        })),
      })),
    },
    playersInMatch: playersInMatch.size,
    bracketWinners: [...bracketWinners.entries()].map(([round, players]) => ({
      round,
      count: players.length,
      players: players.map(p => p.username),
    })),
    matchTimers: matchTimers.size,
    tournament: {
      scheduledDate: tournamentConfig.scheduledDate,
      started: tournamentConfig.tournamentStarted,
      registeredCount: registeredPlayers.size,
      activeCount: getActivePlayerCount(),
      currentRound,
    },
    lobby: lobby.size,
  });
});

// ─── Tournament REST endpoints ───────────────────────────────────────────────
// Get tournament status (public)
app.get('/tournament/status', (_, res) => {
  const activePlayers = getActivePlayers();
  res.json({
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    registrationOpen: isRegistrationMode(),
    registeredCount: registeredPlayers.size,
    activeCount: activePlayers.length,
    maxPlayers: tournamentConfig.maxPlayers,
    rewardAmount: tournamentConfig.rewardAmount,
    tournamentId: tournamentConfig.tournamentId || tournamentConfig.scheduledDate || null,
    currentRound,
    questionBankSize: questionBank.length,
    players: [...registeredPlayers.values()].map(p => {
      const socket = p.socketId ? io.sockets.sockets.get(p.socketId) : null;
      const isOnline = socket && socket.connected;
      return { username: p.username, joinedAt: p.joinedAt, isOnline, status: p.status };
    }),
  });
});

// Get scheduled date and check if it's time to start (public)
app.get('/tournament/schedule', (_, res) => {
  const scheduledDate = tournamentConfig.scheduledDate;
  
  if (!scheduledDate) {
    return res.json({
      ok: true,
      scheduled: false,
      scheduledDate: null,
      timeUntilStart: null,
      isTimeToStart: false,
      tournamentStarted: tournamentConfig.tournamentStarted,
    });
  }

  const now = Date.now();
  const startTime = new Date(scheduledDate).getTime();
  const timeUntilStart = startTime - now; // milliseconds until start (negative if past)
  const isTimeToStart = timeUntilStart <= 0;

  res.json({
    ok: true,
    scheduled: true,
    scheduledDate,
    scheduledDateFormatted: new Date(scheduledDate).toLocaleString(),
    timeUntilStart,                          // ms until start (negative = already past)
    timeUntilStartSeconds: Math.floor(timeUntilStart / 1000),
    isTimeToStart,                           // true when now >= scheduledDate
    tournamentStarted: tournamentConfig.tournamentStarted,
    registrationOpen: isRegistrationMode(),
    registeredCount: registeredPlayers.size,
  });
});

// Admin: Set the tournament date & time — opens registration
// Protected: requires admin JWT
// Body: { date: '2026-03-20', time: '18:00' }  OR  { scheduledDate: '<ISO string>' }
app.post('/admin/tournament/set-schedule', requireAdmin, async (req, res) => {
  try {
    const { date, time, scheduledDate: isoOverride } = req.body;

    let scheduledDate = isoOverride || null;

    if (!scheduledDate) {
      if (!date || !time) {
        return res.status(400).json({ error: 'Provide either { date, time } or { scheduledDate } (ISO string)' });
      }
      // Combine date (YYYY-MM-DD) + time (HH:MM) into a full ISO string
      scheduledDate = new Date(`${date}T${time}:00`).toISOString();
    }

    if (isNaN(new Date(scheduledDate).getTime())) {
      return res.status(400).json({ error: 'Invalid date/time value' });
    }

    // Save to MongoDB
    await TournamentSchedule.findOneAndUpdate(
      { status: 'scheduled' },
      { scheduledDate: new Date(scheduledDate), status: 'scheduled', registeredCount: 0 },
      { upsert: true, returnDocument: 'after' }
    );

    tournamentConfig.scheduledDate = scheduledDate;
    tournamentConfig.tournamentStarted = false;
    registeredPlayers.clear();
    bracketWinners.clear();
    currentRound = 1;

    scheduleAutoStart(scheduledDate);

    io.emit('tournament_config_updated', {
      scheduledDate,
      registrationOpen: true,
      tournamentStarted: false,
    });

    console.log(`[tournament] Scheduled for ${scheduledDate} — registration open (saved to DB)`);
    res.json({ ok: true, scheduledDate, message: 'Tournament scheduled! Registration is now open.' });
  } catch (err) {
    console.error('[admin/tournament/set-schedule] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: Schedule a tournament (legacy alias — kept for backward compat)
app.post('/admin/tournament/schedule', requireAdmin, async (req, res) => {
  try {
    const { scheduledDate } = req.body;
    if (!scheduledDate) {
      return res.status(400).json({ error: 'scheduledDate is required (ISO string)' });
    }

    // Save to MongoDB
    await TournamentSchedule.findOneAndUpdate(
      { status: 'scheduled' },
      { scheduledDate: new Date(scheduledDate), status: 'scheduled', registeredCount: 0 },
      { upsert: true, returnDocument: 'after' }
    );

    // Update in-memory config
    tournamentConfig.scheduledDate = scheduledDate;
    tournamentConfig.tournamentStarted = false;
    registeredPlayers.clear();
    bracketWinners.clear();
    currentRound = 1;
    scheduleAutoStart(scheduledDate);
    io.emit('tournament_config_updated', { scheduledDate, registrationOpen: true, tournamentStarted: false });
    console.log(`[tournament] Scheduled for ${scheduledDate} — registration open (saved to DB)`);
    res.json({ ok: true, scheduledDate, message: 'Registration is now open!' });
  } catch (err) {
    console.error('[admin/tournament/schedule] Error:', err.message);
    res.status(500).json({ error: 'Server error' });
  }
});

// Admin: Get all registered players
app.get('/admin/tournament/players', (_, res) => {
  res.json({
    players: [...registeredPlayers.values()],
    count: registeredPlayers.size,
    config: tournamentConfig,
  });
});

// Debug: Check tournament timer status
app.get('/admin/tournament/debug', (_, res) => {
  const now = Date.now();
  const scheduledTime = tournamentConfig.scheduledDate ? new Date(tournamentConfig.scheduledDate).getTime() : null;
  const timeUntilStart = scheduledTime ? scheduledTime - now : null;
  
  res.json({
    serverTime: new Date(now).toISOString(),
    scheduledDate: tournamentConfig.scheduledDate,
    tournamentStarted: tournamentConfig.tournamentStarted,
    autoStartTimerActive: autoStartTimer !== null,
    timeUntilStartMs: timeUntilStart,
    timeUntilStartSeconds: timeUntilStart ? Math.round(timeUntilStart / 1000) : null,
    timeUntilStartMinutes: timeUntilStart ? Math.round(timeUntilStart / 60000) : null,
    registeredCount: registeredPlayers.size,
    activeCount: getActivePlayerCount(),
    autoStartRetryCount,
    pacing: TOURNAMENT_PACING,
  });
});

// Admin: Update tournament pacing settings
app.post('/admin/tournament/pacing', (req, res) => {
  const { questionTime, preMatchCountdown, betweenRoundsDelay, postMatchDelay } = req.body;
  
  if (questionTime !== undefined) TOURNAMENT_PACING.QUESTION_TIME_SECONDS = Math.max(5, Math.min(30, questionTime));
  if (preMatchCountdown !== undefined) TOURNAMENT_PACING.PRE_MATCH_COUNTDOWN = Math.max(0, Math.min(30, preMatchCountdown));
  if (betweenRoundsDelay !== undefined) TOURNAMENT_PACING.BETWEEN_ROUNDS_DELAY = Math.max(0, Math.min(10, betweenRoundsDelay));
  if (postMatchDelay !== undefined) TOURNAMENT_PACING.POST_MATCH_DELAY = Math.max(0, Math.min(10, postMatchDelay));
  
  console.log('[admin] Tournament pacing updated:', TOURNAMENT_PACING);
  res.json({ ok: true, pacing: TOURNAMENT_PACING });
});

// Admin: Start the tournament (begin pairing)
app.post('/admin/tournament/start', (req, res) => {
  if (!tournamentConfig.scheduledDate) {
    return res.status(400).json({ error: 'No tournament scheduled. Set a date first.' });
  }

  // Clear auto-start timer since admin is starting manually
  if (autoStartTimer) {
    clearTimeout(autoStartTimer);
    autoStartTimer = null;
  }

  const result = startTournament();
  if (result.error) {
    return res.status(400).json(result);
  }
  res.json(result);
});

// Check if device has already joined special session
app.get('/api/check-joined/:deviceId', (req, res) => {
  const { deviceId } = req.params;
  const hasJoined = registeredPlayers.has(deviceId);
  const playerInfo = registeredPlayers.get(deviceId);
  res.json({ 
    hasJoined,
    username: playerInfo?.username || null,
    joinedAt: playerInfo?.joinedAt || null
  });
});

// ─── POLLING FALLBACK: Get current match/tournament state for a device ───────
// Clients can poll this every 2-3 seconds as a fallback when WebSocket fails
app.get('/api/state/:deviceId', (req, res) => {
  const { deviceId } = req.params;
  
  // Find if player is in an active match
  let matchState = null;
  for (const [matchId, match] of matches) {
    if (match.players[deviceId] && match.active) {
      const myPlayer = match.players[deviceId];
      const opponent = Object.values(match.players).find(p => p.deviceId !== deviceId);
      matchState = {
        matchId,
        questionIndex: match.questionIndex,
        totalQuestions: match.questions?.length || 5,
        questionIds: (match.questions || []).map(q => q.id),
        currentQuestionId: match.questions?.[match.questionIndex]?.id || null,
        myAnswer: myPlayer.answer,
        opponentHasAnswered: opponent?.answer !== null,
        round: match.tournamentRound || 1,
        timeLeft: match.questionStartTime 
          ? Math.max(0, 10 - Math.floor((Date.now() - match.questionStartTime) / 1000))
          : 10,
      };
      break;
    }
  }
  
  // Get player registration status
  const registered = registeredPlayers.get(deviceId);
  const isInWinnersQueue = winnersQueue.has(deviceId);
  const isInWaitingQueue = waitingQueue.has(deviceId);
  const isInMatch = playersInMatch.has(deviceId);
  
  res.json({
    serverTime: Date.now(),
    tournamentStarted: tournamentConfig.tournamentStarted,
    scheduledDate: tournamentConfig.scheduledDate,
    registered: !!registered,
    username: registered?.username || null,
    status: matchState ? 'in_match' 
          : isInWinnersQueue ? 'waiting_next_round'
          : isInWaitingQueue ? 'waiting_match'
          : registered ? 'registered'
          : 'not_registered',
    match: matchState,
    currentRound,
    registeredCount: registeredPlayers.size,
    activeCount: getActivePlayerCount(),
  });
});

// ─── POLLING: Submit answer via REST (fallback when socket fails) ────────────
app.post('/api/answer', (req, res) => {
  const { deviceId, matchId, answer, questionIndex } = req.body;
  
  if (!deviceId || !matchId || answer === undefined) {
    return res.status(400).json({ error: 'Missing required fields' });
  }
  
  const match = matches.get(matchId);
  if (!match || !match.active) {
    return res.status(404).json({ error: 'Match not found or inactive' });
  }
  
  const player = match.players[deviceId];
  if (!player) {
    return res.status(403).json({ error: 'Not a player in this match' });
  }
  
  // Check if already answered
  if (player.answer !== null) {
    return res.json({ ok: true, alreadyAnswered: true });
  }
  
  // Record answer
  const now = Date.now();
  const elapsed = match.questionStartTime ? (now - match.questionStartTime) / 1000 : 0;
  player.answer = answer;
  player.answerTime = Math.min(elapsed, 10);
  
  console.log(`[REST answer] ${player.username} answered ${answer} in ${player.answerTime.toFixed(2)}s`);
  
  // Check if both answered
  const [p1, p2] = Object.values(match.players);
  if (p1.answer !== null && p2.answer !== null) {
    evaluateRound(match, io);
  }
  
  res.json({ ok: true, recorded: true });
});

// Admin: Reset tournament (clear schedule + all registrations → back to normal mode)
app.post('/admin/tournament/reset', requireAdmin, (req, res) => {
  registeredPlayers.clear();
  tournamentConfig.scheduledDate = null;
  tournamentConfig.tournamentStarted = false;
  tournamentConfig.tournamentId = null;
  tournamentConfig.initialPlayerCount = 0;
  lobby.clear();

  // Clear new queues
  waitingQueue.clear();
  winnersQueue.clear();
  playersInMatch.clear();
  bracketWinners.clear();
  currentRound = 1;

  // Clear all match timers
  for (const [matchId] of matchTimers) {
    cleanupMatchTimer(matchId);
  }

  io.emit('tournament_reset', { message: 'Tournament has been reset' });
  console.log('[tournament] Reset — back to normal mode');
  res.json({ ok: true });
});

// Admin: Full reset — clears ALL data (tournament, matches, leaderboard, lobby)
app.post('/admin/reset-all', (req, res) => {
  // Clear tournament
  registeredPlayers.clear();
  tournamentConfig.scheduledDate = null;
  tournamentConfig.tournamentStarted = false;
  
  // Clear matches & lobby
  lobby.clear();
  matches.clear();
  
  // Clear new queues
  waitingQueue.clear();
  winnersQueue.clear();
  playersInMatch.clear();
  bracketWinners.clear();
  
  // Clear all match timers
  for (const [matchId] of matchTimers) {
    cleanupMatchTimer(matchId);
  }
  
  // Clear leaderboard
  leaderboard.clear();
  
  // Clear device tracking
  devices.clear();
  sessions.clear();
  violations.clear();
  rateLimits.clear();
  
  // Notify all clients
  io.emit('tournament_reset', { message: 'Game has been fully reset' });
  io.emit('force_reload', { message: 'Admin reset the game' });
  
  console.log('[admin] FULL RESET — all data cleared');
  res.json({ ok: true, message: 'All data cleared' });
});
const DEMO_NAMES = [
  'AkintundeB','FunmilatoA','KayodeM','BisiO','TundeF',
  'AdaobiC','EmekaN','NgoziU','YemiA','TopeS',
  'LaraB','IfeoluwaK','SeunO','RotimiA','DamiR',
  'BisodunM','FeranmiT','GbengaJ','KemiL','OluwaseunP',
];

// Active demo bots: deviceId → { username, deviceId, wins, totalTime }
const demoBots = new Map();
let demoEnabled = false;
let demoPairInterval = null;

// Make a bot "join" the lobby and immediately be available for pairing
function addBotToLobby(name, idx) {
  const deviceId = `demo_bot_${idx}`;
  if (lobby.has(deviceId)) return; // already waiting
  const fakeSocketId = `bot_socket_${idx}_${Date.now()}`;
  lobby.set(deviceId, {
    socketId: fakeSocketId,
    username: name,
    deviceId,
    joinedAt: Date.now(),
    isBot: true,
  });
  if (!leaderboard.has(name)) {
    leaderboard.set(name, { username: name, wins: 0, totalTime: 0, stage: 'playing' });
  }
  if (!demoBots.has(deviceId)) {
    demoBots.set(deviceId, { username: name, deviceId, wins: 0, totalTime: 0 });
  }
}

// When a bot is in a match, simulate it answering after a short random delay
function simulateBotAnswer(match, botDeviceId) {
  const bot = match.players[botDeviceId];
  if (!bot) return;
  // Bot answers after 1–5 seconds, gets it right ~55% of the time
  const delay = 1000 + Math.floor(Math.random() * 4000);
  setTimeout(() => {
    const m = matches.get(match.matchId);
    if (!m || !m.active) return;
    if (m.players[botDeviceId].answer !== null) return; // already answered

    const options = ['A','B','C','D'];
    const question = m.questions ? m.questions[m.questionIndex] : null;
    let answer;
    if (question) {
      answer = Math.random() < 0.55 ? question.correct : options.filter(o => o !== question.correct)[Math.floor(Math.random() * 3)];
    } else {
      answer = options[Math.floor(Math.random() * 4)];
    }
    const answerTime = Math.round(delay / 1000);
    m.players[botDeviceId].answer = answer;
    m.players[botDeviceId].answerTime = answerTime;

    // Notify the real opponent that bot has answered
    const opponent = Object.values(m.players).find(p => p.deviceId !== botDeviceId);
    if (opponent && opponent.socketId) {
      const oppSocket = io.sockets.sockets.get(opponent.socketId);
      if (oppSocket) oppSocket.emit('opponent_answered');
    }

    // If both answered, evaluate
    if (Object.values(m.players).every(p => p.answer !== null)) {
      evaluateRound(m, io);
    }
  }, delay);
}

// After evaluateRound, if the bot won, put it back in the lobby after a short pause
function reQueueBot(botDeviceId) {
  const bot = demoBots.get(botDeviceId);
  if (!bot || !demoEnabled) return;
  setTimeout(() => {
    if (!demoEnabled) return;
    const idx = [...demoBots.keys()].indexOf(botDeviceId);
    addBotToLobby(bot.username, idx);
    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });
    broadcastToSpectators('lobby_count', { count: lobby.size });
    // Try to pair with any waiting real player
    tryPairBotsWithWaiting();
  }, 2000 + Math.random() * 3000);
}

// Scan the lobby: pair bots with real players
function tryPairBotsWithWaiting() {
  const realPlayers = [];
  const botPlayers  = [];
  for (const [did, entry] of lobby) {
    if (entry.isBot) botPlayers.push(entry);
    else realPlayers.push(entry);
  }
  // Pair each real player with a bot
  for (const real of realPlayers) {
    if (botPlayers.length === 0) break;
    const bot = botPlayers.shift();
    lobby.delete(real.deviceId);
    lobby.delete(bot.deviceId);

    const p1 = { deviceId: real.deviceId, username: real.username, socketId: real.socketId };
    const p2 = { deviceId: bot.deviceId,  username: bot.username,  socketId: bot.socketId };
    const match = createMatch(p1, p2);

    // Notify real player
    const realSocket = io.sockets.sockets.get(real.socketId);
    if (realSocket) {
      realSocket.join(match.matchId);
      realSocket.emit('match_found', {
        matchId: match.matchId,
        seed: match.seed,
        questionIds: (match.questions || []).map(q => q.id),
        opponent: { username: bot.username, deviceId: bot.deviceId },
      });
    }

    console.log(`[demo] bot ${bot.username} paired with ${real.username}`);

    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: p1.username, deviceId: p1.deviceId },
      p2: { username: p2.username, deviceId: p2.deviceId },
    });

    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });
    broadcastToSpectators('lobby_count', { count: lobby.size });

    // Bot starts answering questions
    simulateBotAnswer(match, bot.deviceId);
  }

  // Also pair bots with each other for visual activity on view screen
  while (botPlayers.length >= 2) {
    const b1 = botPlayers.shift();
    const b2 = botPlayers.shift();
    lobby.delete(b1.deviceId);
    lobby.delete(b2.deviceId);

    const match = createMatch(
      { deviceId: b1.deviceId, username: b1.username, socketId: b1.socketId },
      { deviceId: b2.deviceId, username: b2.username, socketId: b2.socketId }
    );

    broadcastToSpectators('match_started', {
      matchId: match.matchId,
      p1: { username: b1.username, deviceId: b1.deviceId },
      p2: { username: b2.username, deviceId: b2.deviceId },
    });

    broadcastLobbyCount();
    io.emit('lobby_count', { count: lobby.size });

    simulateBotAnswer(match, b1.deviceId);
    simulateBotAnswer(match, b2.deviceId);
  }
}

app.post('/admin/demo/start', (req, res) => {
  const count = Math.min(Math.max(parseInt(req.body.count) || 10, 2), 20);
  demoEnabled = true;

  // Add bots to lobby
  for (let i = 0; i < count; i++) {
    addBotToLobby(DEMO_NAMES[i % DEMO_NAMES.length], i);
  }

  broadcastLeaderboard();
  broadcastLobbyCount();
  io.emit('lobby_count', { count: lobby.size });
  broadcastToSpectators('lobby_count', { count: lobby.size });

  // Pair bots among themselves immediately for view screen activity
  tryPairBotsWithWaiting();

  // Keep lobby topped up: every 5s, if demo is on, add bots back up to count
  if (demoPairInterval) clearInterval(demoPairInterval);
  demoPairInterval = setInterval(() => {
    if (!demoEnabled) { clearInterval(demoPairInterval); return; }
    let inLobby = 0;
    for (const [, e] of lobby) if (e.isBot) inLobby++;
    const need = Math.max(0, 2 - inLobby); // keep at least 2 bots in lobby
    for (let i = 0; i < need; i++) {
      const idx = Math.floor(Math.random() * count);
      addBotToLobby(DEMO_NAMES[idx % DEMO_NAMES.length], idx);
    }
    if (need > 0) {
      tryPairBotsWithWaiting();
      broadcastLobbyCount();
      io.emit('lobby_count', { count: lobby.size });
    }
  }, 5000);

  res.json({ ok: true, count });
});

app.post('/admin/demo/stop', (req, res) => {
  demoEnabled = false;
  if (demoPairInterval) { clearInterval(demoPairInterval); demoPairInterval = null; }

  // Remove all bots from lobby
  for (const [did] of demoBots) lobby.delete(did);
  demoBots.clear();

  broadcastLobbyCount();
  io.emit('lobby_count', { count: lobby.size });
  broadcastToSpectators('lobby_count', { count: lobby.size });
  broadcastLeaderboard();
  res.json({ ok: true });
});

// ─── Start ────────────────────────────────────────────────────────────────────
const PORT = process.env.PORT || 4000;

let mongoConnected = false;

async function connectMongo(retryCount = 0) {
  const maxRetries = 5;
  try {
    await mongoose.connect(process.env.MONGO_URI);
    mongoConnected = true;
    console.log('✅ Connected to MongoDB');

    // Load the question bank from MongoDB into the in-memory cache.
    // Matches read from `questionBank` (synchronous), so there is no DB hit per question.
    await loadQuestionBankFromDB();

    // Load persisted tournament schedule from MongoDB on startup
    try {
      const savedSchedule = await TournamentSchedule.findOne({ status: 'scheduled' });
      if (savedSchedule && savedSchedule.scheduledDate) {
        const isoDate = savedSchedule.scheduledDate.toISOString();
        tournamentConfig.scheduledDate = isoDate;
        tournamentConfig.tournamentStarted = false;
        console.log(`✅ Loaded tournament schedule from DB: ${isoDate}`);

        // Re-schedule auto-start if the time hasn't passed yet
        scheduleAutoStart(isoDate);
      }
    } catch (scheduleErr) {
      console.error('⚠️ Could not load tournament schedule:', scheduleErr.message);
    }

    return true;
  } catch (err) {
    console.error(`❌ MongoDB connection error (attempt ${retryCount + 1}/${maxRetries}):`, err.message);
    
    if (retryCount < maxRetries - 1) {
      console.log(`   Retrying in 5 seconds...`);
      await new Promise(resolve => setTimeout(resolve, 5000));
      return connectMongo(retryCount + 1);
    }
    
    console.error('❌ MongoDB connection failed after max retries. Server will run without DB.');
    return false;
  }
}

async function startServer() {
  // Try to connect to MongoDB, but don't fail if it doesn't work
  await connectMongo();

  // If Mongo brought no questions (or Mongo never connected), fall back to the JSON file.
  if (questionBank.length === 0) {
    const loaded = loadQuestionBankFromFile();
    if (loaded === 0) {
      console.log('⚠️  Question bank is EMPTY — tournament cannot start until questions are added.');
    }
  }

  server.listen(PORT, () => {
    console.log(`\n🚀 QuizDuel server listening on http://localhost:${PORT}`);
    if (!mongoConnected) {
      console.log('⚠️  Running without MongoDB - some features may be limited\n');
    } else {
      console.log('');
    }
  });
}

startServer();
