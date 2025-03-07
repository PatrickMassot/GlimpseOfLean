import Mathlib.Data.ENNReal.Operations

lemma ENNReal.mul_self_eq_self_iff (a : ENNReal) : a * a = a ↔ a = 0 ∨ a = 1 ∨ a = ⊤ := by
  by_cases h : a = 0
  · simp [h]
  by_cases h' : a = ⊤
  · simp [h']
  simp only [h, h', or_false, false_or]
  constructor
  · intro h''
    nth_rw 3 [← one_mul a] at h''
    exact (ENNReal.mul_left_inj h h').mp h''
  · intro h''
    simp [h'']
