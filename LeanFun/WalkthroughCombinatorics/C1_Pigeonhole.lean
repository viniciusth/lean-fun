import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Init.Data.Function

-- set_option diagnostics true
set_option linter.style.longLine false

variable {α : Type*} [DecidableEq α]

/-
Theorem 1.1. [Pigeon-hole Principle] Let n and k be positive integers,
and let n > k. Suppose we have to place n identical balls into k identical
boxes. Then there will be at least one box in which we place at least two
balls.

assumptions: Finite sets, functions and injection
-/
theorem Pigeonhole {a b : Finset α} (h : b.card < a.card) (f : α → α) (map : ∀ x ∈ a, f x ∈ b) :
  ¬Function.Injective f := by
    revert b -- revert b so we can modify it in the induction
    induction a using Finset.induction_on with
    | empty => { -- ∅.card > something
      intro _ ctr
      contradiction
    }
    | insert el a el_not_mem_a ih => { -- given an element that is not in a, prove that it is true for the set (insert el a) = big_a
      intro b h' map' -- given the new b, the hypothesis over big_a, and the map over big_a

      by_cases col : ∃ c ∈ a, f c = f el -- does el create a collision?
      · rcases col with ⟨c, c_mem_a, f_collides⟩ -- yes, the domain element is c
        rw [Function.Injective]
        have neq : c ≠ el := ne_of_mem_of_not_mem c_mem_a el_not_mem_a -- member difference <-> neq
        push_neg
        use c, el
      · push_neg at col -- no, so el maps to a different element than anyone from a
        -- then we can use our IH: given any image set with cardinality less than domain, the function is not injective
        -- the goal should be using b without f el, since our IH is over a, not big_a
        apply ih (b := b.erase (f el))
        -- first: cardinality must be valid
        · apply lt_of_lt_of_le (b := b.card) -- b.erase < b <= a < big_a
          · exact Finset.card_erase_lt_of_mem (map' el (Finset.mem_insert_self el a)) -- el belongs to a, so b.erase < b
          · rw [Finset.card_insert_of_notMem el_not_mem_a] at h' -- big_a.card = a.card + 1
            exact Nat.le_of_lt_succ h'
        -- then, mapping function must exist
        · intro x x_mem_a
          set fx_mem_b := map' x (Finset.mem_insert_of_mem x_mem_a)
          set fx_ne_fel := col x x_mem_a
          exact Finset.mem_erase_of_ne_of_mem fx_ne_fel fx_mem_b















    }







