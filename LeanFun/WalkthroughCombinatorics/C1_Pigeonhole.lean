import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Card
import Init.Data.Function

-- set_option diagnostics true
set_option linter.style.longLine false

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-
Theorem 1.1. [Pigeon-hole Principle] Let n and k be positive integers,
and let n > k. Suppose we have to place n identical balls into k identical
boxes. Then there will be at least one box in which we place at least two
balls.

assumptions: Finite sets, functions and injection
-/
theorem pigeonhole {a : Finset α} {b : Finset β} (h : b.card < a.card) (f : α → β) (map : ∀ x ∈ a, f x ∈ b) :
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


theorem general_pigeonhole (r : ℕ) (a : Finset α) (b : Finset β) (h : r * b.card < a.card) (f : α → β)
  (map : ∀ x ∈ a, f x ∈ b) : ∃ y ∈ b, (a.filter (fun x ↦ f x = y)).card ≥ r + 1 := by
  revert b
  induction a using Finset.induction_on with
  | empty => {
    intro _ ctr
    contradiction
  }
  | insert el a el_not_mem_a ih => {
    intro b h' map'
    -- same logic again, but now we have a filter in the middle
    sorry
  }


-- Exercises

/-
1.
A busy airport sees 1500 takeoffs per day.
Prove that there are two planes that must take off within a minute of each other.
-/
def minutes_per_day : ℕ := 24 * 60
example (planes minutes : Finset ℕ) (h : planes.card = 1500) (h' : minutes.card = minutes_per_day) (takeoff_minute : ℕ → ℕ)
  (map : ∀ x ∈ planes, takeoff_minute x ∈ minutes) :
  ∃ a b, takeoff_minute a = takeoff_minute b ∧ a ≠ b := by
  have card_lt : minutes.card < planes.card := by
    rw [h, h']
    unfold minutes_per_day
    simp
  have nInj : ¬Function.Injective takeoff_minute := pigeonhole card_lt takeoff_minute map
  rw [Function.Injective] at nInj
  push_neg at nInj
  exact nInj

/-
2.
Find all triples of positive integers a < b < c for which 1/a + 1/b + 1/c = 1 holds.

bc + ac + ab = abc
bc + a(b+c) = abc
a(b+c) = abc - bc
a(b+c) = bc(a-1)
-/









