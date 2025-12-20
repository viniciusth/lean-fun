import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Init.Data.Function

set_option diagnostics true

variable {α : Type*} [DecidableEq α]

/-
Theorem 1.1. [Pigeon-hole Principle] Let n and k be positive integers,
and let n > k. Suppose we have to place n identical balls into k identical
boxes. Then there will be at least one box in which we place at least two
balls.
-/
theorem Pigeonhole {a b : Finset α} (h : a.card > b.card) (f : α → α) (map : ∀x ∈ a, f x ∈ b) :
  ¬Function.Injective f := by
    revert b
    induction a using Finset.induction_on with
    | empty => {
      intro _ a
      contradiction
    }
    | insert x y z ih => {
      intro b cmp nmap
      set fs := insert x y
      sorry
    }







