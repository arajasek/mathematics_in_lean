import Mathlib.Data.Fintype.BigOperators
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β] (s t : Finset α) (f : α → β)

example : #(s ×ˢ t) = #s * #t := by rw [card_product]
example : #(s ×ˢ t) = #s * #t := by simp

example : #(s ∪ t) = #s + #t - #(s ∩ t) := by rw [card_union]

example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by rw [card_union_of_disjoint h]
example (h : Disjoint s t) : #(s ∪ t) = #s + #t := by simp [h]

example (h : Function.Injective f) : #(s.image f) = #s := by rw [card_image_of_injective _ h]

example (h : Set.InjOn f s) : #(s.image f) = #s := by rw [card_image_of_injOn h]

section
open Fintype

variable {α β : Type*} [Fintype α] [Fintype β]

example : card (α × β) = card α * card β := by simp

example : card (α ⊕ β) = card α + card β := by simp

example (n : ℕ) : card (Fin n → α) = (card α)^n := by simp

variable {n : ℕ} {γ : Fin n → Type*} [∀ i, Fintype (γ i)]

example : card ((i : Fin n) → γ i) = ∏ i, card (γ i) := by simp

example : card (Σ i, γ i) = ∑ i, card (γ i) := by simp

end

#check Disjoint

example (m n : ℕ) (h : m ≥ n) :
    card (range n ∪ (range n).image (fun i ↦ m + i)) = 2 * n := by
  rw [card_union_of_disjoint, card_range, card_image_of_injective, card_range]; omega
  . apply add_right_injective
  . simp [disjoint_iff_ne]; omega

def triangle (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range (n+1) ×ˢ range (n+1) | p.1 < p.2}

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n = (range (n+1)).biUnion (fun j ↦ (range j).image (., j)) := by
    ext p
    simp only [triangle, mem_filter, mem_product, mem_range, mem_biUnion, mem_image]
    constructor
    . rintro ⟨⟨hp1, hp2⟩, hp3⟩
      use p.2, hp2, p.1, hp3
    . rintro ⟨p1, hp1, p2, hp2, rfl⟩
      omega
  rw [this, card_biUnion]; swap
  · -- take care of disjointness first
    intro x _ y _ xney
    simp [disjoint_iff_ne, xney]
  -- continue the calculation
  transitivity (∑ i ∈ range (n + 1), i)
  · congr; ext i
    rw [card_image_of_injective, card_range]
    intros i1 i2; simp
  rw [sum_range_id]; rfl

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  have : triangle n ≃ Σ i : Fin (n + 1), Fin i.val :=
    { toFun := by
        rintro ⟨⟨i, j⟩, hp⟩
        simp [triangle] at hp
        exact ⟨⟨j, hp.1.2⟩, ⟨i, hp.2⟩⟩
      invFun := by
        rintro ⟨i, j⟩
        use ⟨j, i⟩
        simp [triangle]
        exact j.isLt.trans i.isLt
      left_inv := by intro i; rfl
      right_inv := by intro i; rfl }
  rw [←Fintype.card_coe]
  trans; apply (Fintype.card_congr this)
  rw [Fintype.card_sigma, sum_fin_eq_sum_range]
  convert Finset.sum_range_id (n + 1)
  simp_all

example (n : ℕ) : #(triangle n) = (n + 1) * n / 2 := by
  apply Nat.eq_div_of_mul_eq_right (by norm_num)
  let turn (p : ℕ × ℕ) : ℕ × ℕ := (n - 1 - p.1, n - p.2)
  calc 2 * #(triangle n)
      = #(triangle n) + #(triangle n) := by
          apply two_mul
    _ = #(triangle n) + #(triangle n |>.image turn) := by
          rw [card_image_of_injOn]
          simp [triangle, turn]
          intro (x1, y1) ⟨⟨x1ltnp1, y1ltnp1⟩, x1lty1⟩ (x2, y2) ⟨⟨x2ltnp1, y2ltnp1⟩, x2lty2⟩ hturn
          simp at x1ltnp1 y1ltnp1 x1lty1 x2ltnp1 y2ltnp1 x2lty2
          simp [turn] at hturn
          rcases hturn with ⟨hx, hy⟩
          simp
          omega
          -- LOL all of this was only needed because omega doesn't like thinking about (x1, y1) = (x2, y2),
          -- but can perfectly handle x1 = y1 ∧ x2 = y2
          -- apply Nat.le_of_lt_succ at x1ltnp1
          -- apply Nat.le_of_lt_succ at y1ltnp1
          -- apply Nat.le_of_lt_succ at x2ltnp1
          -- apply Nat.le_of_lt_succ at y2ltnp1
          -- have yeq : y1 = y2 := by
          --   apply (Nat.sub_eq_iff_eq_add y1ltnp1).mp at hy
          --   rw [← Nat.sub_add_comm y2ltnp1] at hy
          --   symm at hy
          --   apply (Nat.sub_eq_iff_eq_add (Nat.le_add_right_of_le y2ltnp1)).mp at hy
          --   exact Nat.add_left_cancel hy
          -- have x1lenminus1 : x1 ≤ n - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le x1lty1 y1ltnp1)
          -- have x2lenminus1 : x2 ≤ n - 1 := Nat.le_sub_one_of_lt (Nat.lt_of_lt_of_le x2lty2 y2ltnp1)
          -- have xeq: x1 = x2 := by
          --   apply (Nat.sub_eq_iff_eq_add x1lenminus1).mp at hx
          --   rw [← Nat.sub_add_comm x2lenminus1] at hx
          --   symm at hx
          --   apply (Nat.sub_eq_iff_eq_add (Nat.le_add_right_of_le x2lenminus1)).mp at hx
          --   exact Nat.add_left_cancel hx
          -- exact Prod.ext xeq yeq
    _ = #(range n ×ˢ range (n + 1)) := by
      have: Disjoint (triangle n) (triangle n |>.image turn) := by
        rw [disjoint_iff_ne]
        intro (x1, y1) h1 (x2, y2) h2
        simp [triangle] at h1
        simp [triangle, turn] at h2
        rcases h2 with ⟨a, b, ha, hb⟩
        -- you can do this with a rfl somehow
        intro contra
        rcases contra
        omega
      rw [← card_union_of_disjoint this]
      -- didn't need this, congr is precisely the tactic you want!
      apply card_bijective id Function.bijective_id

      intro (x, y); constructor
      simp [mem_union, triangle, turn]
      rintro (h | h)
      omega
      omega

      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      simp [mem_union, triangle, turn]
      rcases lt_or_ge x y with xlty | ylex
      left
      omega

      right
      use n - x - 1, n - y
      omega

    _ = (n + 1) * n := by
      simp; rw[mul_comm]

def triangle' (n : ℕ) : Finset (ℕ × ℕ) := {p ∈ range n ×ˢ range n | p.1 ≤ p.2}

example (n : ℕ) : #(triangle' n) = #(triangle n) := by
  let shove (p : ℕ × ℕ) : ℕ × ℕ := (p.1, p.2 + 1)
  have inj : Function.Injective shove := by
    intro x y; simp[shove]; intro h1 h2; exact Prod.ext h1 h2
  rw [← card_image_of_injective _ inj]
  congr; ext x; constructor
  simp[triangle, triangle', shove]
  rintro a b c d e ⟨f, g⟩
  omega
  simp[triangle, triangle', shove]
  rintro a b c
  use x.1, x.2 - 1
  constructor; omega
  apply Prod.ext; simp; simp; omega

section
open Classical
variable (s t : Finset Nat) (a b : Nat)

theorem doubleCounting {α β : Type*} (s : Finset α) (t : Finset β)
    (r : α → β → Prop)
    (h_left : ∀ a ∈ s, 3 ≤ #{b ∈ t | r a b})
    (h_right : ∀ b ∈ t, #{a ∈ s | r a b} ≤ 1) :
    3 * #(s) ≤ #(t) := by
  calc 3 * #(s)
      = ∑ a ∈ s, 3                               := by simp [sum_const_nat, mul_comm]
    _ ≤ ∑ a ∈ s, #({b ∈ t | r a b})              := sum_le_sum h_left
    _ = ∑ a ∈ s, ∑ b ∈ t, if r a b then 1 else 0 := by simp
    _ = ∑ b ∈ t, ∑ a ∈ s, if r a b then 1 else 0 := sum_comm
    _ = ∑ b ∈ t, #({a ∈ s | r a b})              := by simp
    _ ≤ ∑ b ∈ t, 1                               := sum_le_sum h_right
    _ ≤ #(t)                                     := by simp

example (m k : ℕ) (h : m ≠ k) (h' : m / 2 = k / 2) : m = k + 1 ∨ k = m + 1 := by omega

example {n : ℕ} (A : Finset ℕ)
    (hA : #(A) = n + 1)
    (hA' : A ⊆ range (2 * n)) :
    ∃ m ∈ A, ∃ k ∈ A, Nat.Coprime m k := by
  have : ∃ t ∈ range n, 1 < #({u ∈ A | u / 2 = t}) := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to

    intro a ha
    apply hA' at ha
    simp at ha
    simp
    omega

    simp; omega
  rcases this with ⟨t, ht, ht'⟩
  simp only [one_lt_card, mem_filter] at ht'
  rcases ht' with ⟨a, ⟨haA, hat⟩, b, ⟨hbA, hbt⟩, anb⟩
  have : a = b + 1 ∨ b = a + 1 := by omega
  use a, haA
  use b, hbA
  rcases this with rfl|rfl
  simp
  simp
