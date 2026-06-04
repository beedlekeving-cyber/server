#!/usr/bin/env node
/**
 * Seed the MongoDB `questions` collection from a JSON file.
 *
 * Usage:
 *   node seedQuestions.js <path-to-questions.json> [--append]
 *
 * Default behaviour replaces the entire collection. Pass --append to add
 * questions on top of whatever is already in the DB.
 *
 * Expected JSON shape (an array of objects):
 *   [
 *     {
 *       "id": "q1",
 *       "question": "What is the capital of France?",
 *       "options": { "A": "Madrid", "B": "Berlin", "C": "Paris", "D": "Rome" },
 *       "correct": "C",
 *       "category": "Geography"
 *     },
 *     ...
 *   ]
 */
require('dotenv').config();
const mongoose = require('mongoose');
const fs       = require('fs');
const path     = require('path');
const Question = require('./models/Question');

async function main() {
  const args = process.argv.slice(2).filter(Boolean);
  const append = args.includes('--append');
  const fileArg = args.find(a => !a.startsWith('--'));

  if (!fileArg) {
    console.error('Usage: node seedQuestions.js <path-to-questions.json> [--append]');
    process.exit(1);
  }

  const filePath = path.resolve(fileArg);
  if (!fs.existsSync(filePath)) {
    console.error(`File not found: ${filePath}`);
    process.exit(1);
  }

  let questions;
  try {
    questions = JSON.parse(fs.readFileSync(filePath, 'utf8'));
  } catch (e) {
    console.error('Failed to parse JSON:', e.message);
    process.exit(1);
  }

  if (!Array.isArray(questions)) {
    console.error('JSON root must be an array of question objects');
    process.exit(1);
  }

  // Quick validation
  const invalid = questions.find(q => !q?.id || !q?.question || !q?.options ||
    !['A','B','C','D'].includes(q?.correct));
  if (invalid) {
    console.error('Invalid question shape found:', invalid?.id || invalid);
    process.exit(1);
  }

  if (!process.env.MONGO_URI) {
    console.error('MONGO_URI is not set in .env');
    process.exit(1);
  }

  console.log(`Connecting to MongoDB…`);
  await mongoose.connect(process.env.MONGO_URI);
  console.log('Connected.');

  if (!append) {
    const cleared = await Question.deleteMany({});
    console.log(`Cleared existing questions (${cleared.deletedCount}).`);
  } else {
    console.log('Append mode — keeping existing questions.');
  }

  const inserted = await Question.insertMany(questions, { ordered: false });
  console.log(`✅ Inserted ${inserted.length} questions into MongoDB`);

  const total = await Question.countDocuments();
  console.log(`Total in collection: ${total}`);

  await mongoose.disconnect();
  console.log('Disconnected.');
}

main().catch(err => {
  console.error('Seed failed:', err.message);
  process.exit(1);
});
