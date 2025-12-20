import Mathlib

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl


example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor
  · intro h a sh
    simp only [image] at h
    rw [preimage]
    have elin : f a ∈ v := by
      apply h
      use a
    exact elin

  · intro h b sh
    rcases sh with ⟨a, as, ya⟩
    rw [preimage] at h
    have hf : f a ∈ v := h as
    rw [ya] at hf
    assumption














