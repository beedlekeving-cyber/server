const mongoose = require('mongoose');

const chatMessageSchema = new mongoose.Schema(
  {
    from: { type: String, enum: ['admin', 'winner'], required: true },
    text: { type: String, required: true, trim: true, maxlength: 1000 },
  },
  { timestamps: { createdAt: true, updatedAt: false } }
);

const winnerSubmissionSchema = new mongoose.Schema(
  {
    tournamentId: { type: String, required: true },
    username:     { type: String, required: true, trim: true, maxlength: 30 },
    deviceId:     { type: String, required: true },
    accountNumber:{ type: String, required: true, trim: true, maxlength: 40 },
    accountName:  { type: String, trim: true, maxlength: 80, default: '' },
    bankName:     { type: String, trim: true, maxlength: 80, default: '' },
    message:      { type: String, trim: true, maxlength: 500, default: '' },
    rewardAmount: { type: String, default: '' },
    paid:         { type: Boolean, default: false },
    messages:     { type: [chatMessageSchema], default: [] },
  },
  { timestamps: true }
);

// One submission per device per tournament
winnerSubmissionSchema.index({ deviceId: 1, tournamentId: 1 }, { unique: true });

module.exports = mongoose.model('WinnerSubmission', winnerSubmissionSchema);
