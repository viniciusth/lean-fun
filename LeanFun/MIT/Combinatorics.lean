import Mathlib
set_option diagnostics true

-- The Pigeonhole Principle:
-- If we have a function f mapping 'n' items to 'm' items,
-- and n > m, then there must be two distinct items x and y
-- such that f x = f y.
theorem pigeonhole_principle (n m : ℕ) (h : m < n) (f : Fin n → Fin m) :
  ∃ x y : Fin n, x ≠ y ∧ f x = f y :=
by
  by_contra hc
  push_neg at hc

  have h_inj : Function.Injective f := by
    intro x y h_eq
    by_contra h_neq
    exact hc x y h_neq h_eq

  have h_le : Fintype.card (Fin n) ≤ Fintype.card (Fin m) :=
    Fintype.card_le_of_injective f h_inj

  simp at h_le

  linarith








