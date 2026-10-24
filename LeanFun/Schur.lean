import Mathlib

theorem schur : ∀ r: ℕ, ∀ c: ℕ → Fin r, ∃ x y z, x < y → y < z → x + y = z ∧ c x = c y ∧ c y = c z := by
  intro r c
  sorry







