import MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  rintro ⟨x, xs| xt, rfl⟩
  left; use x
  right; use x
  rintro (⟨x, xs, rfl⟩  | ⟨x, xt, rfl⟩)
  use x, Or.inl xs
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor

  rintro h x hx
  have : f x ∈ f '' s :=  mem_image_of_mem f hx
  apply h this

  intro h y ⟨x, xs, fxeq⟩
    -- f '' s ⊆ v
  rw [← fxeq]
  apply h xs

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  rintro x ⟨y, hy, fyx⟩
  apply h at fyx
  rw [← fyx]
  assumption

example : f '' (f ⁻¹' u) ⊆ u := by
  rintro y ⟨x, hx, rfl⟩
  exact hx

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  rintro x hx
  -- f x ∈ f '' u
  rcases h x with ⟨y, hy⟩
  use y
  constructor
  simp; rw [hy]; assumption
  assumption


example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  rintro y ⟨x, xs, rfl⟩
  use x, h xs


example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  intro y
  apply h

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  ext y; constructor; intro hy
  simp at hy
  apply hy
  intro hy
  simp at hy
  apply hy

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  rintro y ⟨x, ⟨xs, xt⟩, rfl⟩
  constructor
  use x, xs
  use x, xt


example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  rintro y ⟨⟨x1, x1s, fx1⟩ , ⟨x2, x2t, fx2⟩⟩
  have: f x1 = f x2 := by
    rw [fx1, fx2]
  apply h at this
  use x1
  constructor; constructor; exact x1s; rw [this]; exact x2t
  assumption

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y; simp; constructor

  rintro ⟨x, ⟨i, hi⟩ , rfl⟩
  use i, x

  rintro ⟨i, x, hx, fxy⟩
  exact ⟨x, ⟨i, hx⟩, fxy⟩



example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
  Iff.refl _

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos hxy
  simp at xpos ypos
  apply sq_sqrt at xpos
  apply sq_sqrt at ypos
  rw [← xpos, ← ypos, hxy]





example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  sorry

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  sorry

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  sorry

end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical

def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function

example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor

  intro finj x
  apply finj
  apply inverse_spec
  use x

  intro li
  intro x y fxy
  rw [← li x, ← li y, fxy]

example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor

  intro surjF x
  apply inverse_spec
  apply surjF x

  intro h b
  use (inverse f) b
  apply h



end

section
variable {α : Type*}
open Function

theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩

  by_cases contra: j ∈ S

  have h1: j ∉ f j := by
    apply contra
  rw [h] at h1
  contradiction

  have h1: j ∉ f j := by
    rwa [h]
  have h3: j ∈ S := by
    exact h1
  contradiction





  -- have h₁ : j ∉ f j := by
  --   intro h'
  --   have : j ∉ f j := by rwa [h] at h'
  --   contradiction
  -- have h₂ : j ∈ S := h₁
  -- have h₃ : j ∉ S := by rwa [h] at h₁
  -- contradiction

-- COMMENTS: TODO: improve this
end
