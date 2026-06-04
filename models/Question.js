const mongoose = require('mongoose');

const questionSchema = new mongoose.Schema(
  {
    id:       { type: String, required: true, unique: true, trim: true, maxlength: 40 },
    question: { type: String, required: true, trim: true, maxlength: 500 },
    options:  {
      A: { type: String, required: true, trim: true, maxlength: 200 },
      B: { type: String, required: true, trim: true, maxlength: 200 },
      C: { type: String, required: true, trim: true, maxlength: 200 },
      D: { type: String, required: true, trim: true, maxlength: 200 },
    },
    correct:  { type: String, required: true, enum: ['A', 'B', 'C', 'D'] },
    category: { type: String, default: 'General', trim: true, maxlength: 40 },
  },
  { timestamps: true }
);

module.exports = mongoose.model('Question', questionSchema);
