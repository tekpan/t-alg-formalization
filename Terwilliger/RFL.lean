/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.DistanceMatrix

/-!
# Terwilliger Algebra

A Lean 4 formalization of results from
*Lecture Note on Terwilliger Algebra*
by P. Terwilliger, edited by H. Suzuki.

Original notes:
https://icu-hsuzuki.github.io/t-algebra/

Original source repository: CC0-1.0.
-/

/-!
# The raising, flat and lowering matrices `R, F, L` (Chapters 30–31)

For a graph `Γ` and a vertex `x`, the notes split the adjacency matrix into

* `R = ∑ᵢ E*_{i+1} A E*ᵢ` (raising),
* `F = ∑ᵢ E*_i A E*ᵢ` (flat),
* `L = ∑ᵢ E*_{i-1} A E*ᵢ` (lowering),

so that `A = R + L + F` (because `E*_i A E*_j = 0` for `|i - j| > 1`, Lemma 4.3),
`R(E*_iV) ⊆ E*_{i+1}V`, `L(E*_iV) ⊆ E*_{i-1}V`, `F(E*_iV) ⊆ E*_iV`.

Chapter 31 constructs the partial inverse `R⁻¹` of `R`, the unique matrix in
`T(x)` acting as `v ↦ v` on `R E*_iV` for `i < d` and killing `ker L`.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [Fintype X] [DecidableEq X]

variable (G : SimpleGraph X) (x : X)

/-- **Chapter 30.** The lowering matrix `L = ∑_{i ≥ 1} E*_{i-1} A E*_i`. -/
def lowering (D : ℕ) : Matrix X X 𝕜 :=
  ∑ i ∈ Finset.Icc 1 D, subconst (𝕜 := 𝕜) G x (i - 1) * adj G * subconst G x i

/-- **Chapter 30.** The flat matrix `F = ∑ᵢ E*_i A E*_i`. -/
def flat (D : ℕ) : Matrix X X 𝕜 :=
  ∑ i ∈ Finset.range (D + 1), subconst (𝕜 := 𝕜) G x i * adj G * subconst G x i

/-- **Chapter 30.** The raising matrix `R = ∑ᵢ E*_{i+1} A E*ᵢ`. -/
def raising (D : ℕ) : Matrix X X 𝕜 :=
  ∑ i ∈ Finset.range D, subconst (𝕜 := 𝕜) G x (i + 1) * adj G * subconst G x i

/-- The `(i,j)`-block `Eᵢ*(x) A Eⱼ*(x)` of the adjacency matrix. -/
private def adjBlock {G : SimpleGraph X} {x : X} (i j : ℕ) : Matrix X X 𝕜 :=
  subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G * subconst (𝕜 := 𝕜) G x j

/-- Off the band `|i - j| ≤ 1` the blocks vanish (Lemma 4.3). -/
private lemma adjBlock_eq_zero_of_ne {G : SimpleGraph X} {x : X} {i j : ℕ} (hij : i ≠ j)
    (hji : j + 1 ≠ i) (hij' : i + 1 ≠ j) : adjBlock (𝕜 := 𝕜) (G := G) (x := x) i j = 0 := by
  refine subconst_mul_adj_mul_subconst_eq_zero (𝕜 := 𝕜) (G := G) (x := x) ?_
  omega

/-- Multiplying a block `Eⱼ*(x) M` by a vector of the `i`-th subconstituent: only the
diagonal block `i = j` survives, and then the projection `Eᵢ*(x)` is absorbed. -/
private lemma mulVec_block {G : SimpleGraph X} {x : X} (i j : ℕ) (M : Matrix X X 𝕜) (v : X → 𝕜) :
    ((M * subconst (𝕜 := 𝕜) G x j) *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v))
      = if j = i then (M * subconst (𝕜 := 𝕜) G x i) *ᵥ v else 0 := by
  by_cases h : j = i
  · subst h
    rw [if_pos rfl, Matrix.mulVec_mulVec, mul_assoc, subconst_mul_self]
  · rw [if_neg h, Matrix.mulVec_mulVec, mul_assoc, subconst_mul_subconst, if_neg h, mul_zero,
      Matrix.zero_mulVec]

/-- `Eᵢ*(x)` fixes the vectors of the block `Eᵢ*(x) A Eⱼ*(x)`. -/
private lemma subconst_mulVec_block {G : SimpleGraph X} {x : X} (i j : ℕ) (v : X → 𝕜) :
    subconst (𝕜 := 𝕜) G x i *ᵥ ((subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G
        * subconst (𝕜 := 𝕜) G x j) *ᵥ v)
      = (subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G * subconst (𝕜 := 𝕜) G x j) *ᵥ v := by
  rw [Matrix.mulVec_mulVec, ← mul_assoc, ← mul_assoc, subconst_mul_self]

/-- `A = R + F + L`: every block `Eᵢ*(x) A Eⱼ*(x)` off the band `|i - j| ≤ 1` vanishes
(Lemma 4.3), and the remaining ones are precisely the raising, flat and lowering blocks. -/
theorem adj_eq_raising_add_flat_add_lowering {D : ℕ}
    (hD : ∀ y, G.dist x y ≤ D) :
    adj (𝕜 := 𝕜) G = raising (𝕜 := 𝕜) G x D + flat (𝕜 := 𝕜) G x D
      + lowering (𝕜 := 𝕜) G x D := by
  have h1 : ∑ i ∈ Finset.range (D + 1), subconst (𝕜 := 𝕜) G x i = 1 :=
    sum_subconst_eq_one G x D hD
  -- `A = (∑ E*_i) A (∑ E*_j)`
  have key : adj (𝕜 := 𝕜) G
      = ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
          adjBlock (𝕜 := 𝕜) (G := G) (x := x) i j := by
    calc adj (𝕜 := 𝕜) G
        = (∑ i ∈ Finset.range (D + 1), subconst (𝕜 := 𝕜) G x i) * adj G
            * (∑ j ∈ Finset.range (D + 1), subconst (𝕜 := 𝕜) G x j) := by
          rw [h1, one_mul, mul_one]
      _ = ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
            subconst (𝕜 := 𝕜) G x i * adj G * subconst G x j := by
          rw [Finset.sum_mul]
          simp only [Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
  rw [key]
  -- the three bands, as finsets of pairs of indices
  set A : Finset (ℕ × ℕ) := (Finset.range (D + 1)).image (fun i => (i, i)) with hA
  set B : Finset (ℕ × ℕ) := (Finset.range D).image (fun j => (j + 1, j)) with hB
  set C : Finset (ℕ × ℕ) := (Finset.Icc 1 D).image (fun k => (k - 1, k)) with hC
  -- every pair of `range (D+1) × range (D+1)` is on one of the three bands, or vanishes
  have hcover : ∀ p ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1),
      p ∈ A ∪ B ∪ C ∨ adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 = 0 := by
    rintro ⟨i, j⟩ hp
    obtain ⟨hi, hj⟩ := Finset.mem_product.1 hp
    rw [Finset.mem_range] at hi hj
    rcases lt_trichotomy i j with hij | hij | hji
    · rcases lt_or_ge (i + 1) j with hlt | hge
      · exact Or.inr (adjBlock_eq_zero_of_ne (by omega) (by omega) (by omega))
      · refine Or.inl (Finset.mem_union_right _ ?_)
        refine Finset.mem_image.2 ⟨j, ?_, ?_⟩
        · rw [Finset.mem_Icc]; exact ⟨by omega, by omega⟩
        · refine Prod.ext_iff.2 ⟨?_, rfl⟩
          omega
    · subst hij
      refine Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
      exact Finset.mem_image.2 ⟨i, by simpa using hi, rfl⟩
    · rcases lt_or_ge (j + 1) i with hlt | hge
      · exact Or.inr (adjBlock_eq_zero_of_ne (by omega) (by omega) (by omega))
      · refine Or.inl (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
        refine Finset.mem_image.2 ⟨j, ?_, ?_⟩
        · rw [Finset.mem_range]; omega
        · refine Prod.ext_iff.2 ⟨?_, rfl⟩
          omega
  have hsub : A ∪ B ∪ C ⊆ Finset.range (D + 1) ×ˢ Finset.range (D + 1) := by
    intro p hp
    rcases Finset.mem_union.1 hp with hp | hp
    · rcases Finset.mem_union.1 hp with hp | hp
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hp
        exact Finset.mem_product.2 ⟨hi, hi⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hp
        rw [Finset.mem_range] at hj
        exact Finset.mem_product.2
          ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hp
      rw [Finset.mem_Icc] at hk
      obtain ⟨hk1, hk2⟩ := hk
      exact Finset.mem_product.2
        ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  have hvanish : ∀ p ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1), p ∉ A ∪ B ∪ C →
      adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 = 0 := by
    intro p hp hpB
    exact (hcover p hp).resolve_left hpB
  have hmerged : ∑ p ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1),
        adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
      = ∑ p ∈ A ∪ B ∪ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 :=
    (Finset.sum_subset hsub hvanish).symm
  have hdAB : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro p hpA hpB
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hpA
    obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hpB
    have e1 : i = p.1 := congrArg Prod.fst hi
    have e2 : i = p.2 := congrArg Prod.snd hi
    have e3 : j + 1 = p.1 := congrArg Prod.fst hj
    have e4 : j = p.2 := congrArg Prod.snd hj
    omega
  have hdABC : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.2 ?_
    intro p hp hpC
    obtain ⟨k, hk, hkC⟩ := Finset.mem_image.1 hpC
    rw [Finset.mem_Icc] at hk
    obtain ⟨hk1, hk2⟩ := hk
    have e1 : k - 1 = p.1 := congrArg Prod.fst hkC
    have e2 : k = p.2 := congrArg Prod.snd hkC
    rcases Finset.mem_union.1 hp with hp | hp
    · obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hp
      have e3 : i = p.1 := congrArg Prod.fst hi
      have e4 : i = p.2 := congrArg Prod.snd hi
      omega
    · obtain ⟨j, -, hj⟩ := Finset.mem_image.1 hp
      have e3 : j + 1 = p.1 := congrArg Prod.fst hj
      have e4 : j = p.2 := congrArg Prod.snd hj
      omega
  have hunion : ∑ p ∈ A ∪ B ∪ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
      = ∑ p ∈ A, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
        + ∑ p ∈ B, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
        + ∑ p ∈ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 := by
    rw [Finset.sum_union hdABC, Finset.sum_union hdAB]
  have hA' : ∑ p ∈ A, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 = flat (𝕜 := 𝕜) G x D := by
    rw [Finset.sum_image (f := fun p : ℕ × ℕ => adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2)
      (g := fun i => (i, i)) (s := Finset.range (D + 1))]
    · rfl
    · intro i _ i' _ h
      exact congrArg Prod.fst h
  have hB' : ∑ p ∈ B, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 = raising (𝕜 := 𝕜) G x D := by
    rw [Finset.sum_image (f := fun p : ℕ × ℕ => adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2)
      (g := fun j => (j + 1, j)) (s := Finset.range D)]
    · rfl
    · intro j _ j' _ h
      exact congrArg Prod.snd h
  have hC' : ∑ p ∈ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 = lowering (𝕜 := 𝕜) G x D := by
    rw [Finset.sum_image (f := fun p : ℕ × ℕ => adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2)
      (g := fun k => (k - 1, k)) (s := Finset.Icc 1 D)]
    · rfl
    · intro k _ k' _ h
      exact congrArg Prod.snd h
  have hprod : ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        adjBlock (𝕜 := 𝕜) (G := G) (x := x) i j
      = ∑ p ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1),
          adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 :=
    (Finset.sum_product (Finset.range (D + 1)) (Finset.range (D + 1))
      (fun p : ℕ × ℕ => adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2)).symm
  calc ∑ i ∈ Finset.range (D + 1), ∑ j ∈ Finset.range (D + 1),
        adjBlock (𝕜 := 𝕜) (G := G) (x := x) i j
      = ∑ p ∈ Finset.range (D + 1) ×ˢ Finset.range (D + 1),
          adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 := hprod
    _ = ∑ p ∈ A ∪ B ∪ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 := hmerged
    _ = ∑ p ∈ A, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
        + ∑ p ∈ B, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2
        + ∑ p ∈ C, adjBlock (𝕜 := 𝕜) (G := G) (x := x) p.1 p.2 := hunion
    _ = raising (𝕜 := 𝕜) G x D + flat (𝕜 := 𝕜) G x D + lowering (𝕜 := 𝕜) G x D := by
        rw [hA', hB', hC']
        abel

/-- The raising matrix maps `E*_iV` into `E*_{i+1}V`. -/
theorem raising_mem {D : ℕ} {i : ℕ} (v : X → 𝕜) (hv : v ∈ (⊤ : Submodule 𝕜 (X → 𝕜))) :
    raising (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      ∈ Submodule.span 𝕜 {w : X → 𝕜 | subconst (𝕜 := 𝕜) G x (i + 1) *ᵥ w = w} := by
  have hvtop : v ∈ (⊤ : Submodule 𝕜 (X → 𝕜)) := hv
  have hcollapse : raising (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      = if i ∈ Finset.range D then
          ((subconst (𝕜 := 𝕜) G x (i + 1) * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0 := by
    rw [raising, Matrix.sum_mulVec]
    trans ∑ j ∈ Finset.range D,
        (if j = i then
          ((subconst (𝕜 := 𝕜) G x (i + 1) * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0)
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_block (𝕜 := 𝕜) (G := G) (x := x) i j
        (subconst (𝕜 := 𝕜) G x (j + 1) * adj (𝕜 := 𝕜) G) v]
      by_cases h : j = i
      · subst h; rfl
      · rw [if_neg h, if_neg h]
    · rw [Finset.sum_ite_eq']
  rw [hcollapse]
  by_cases hi : i ∈ Finset.range D
  · rw [if_pos hi]
    refine Submodule.subset_span ?_
    exact subconst_mulVec_block (𝕜 := 𝕜) (G := G) (x := x) (i + 1) i v
  · rw [if_neg hi]
    simp

/-- The lowering matrix maps `E*_iV` into `E*_{i-1}V`. -/
theorem lowering_mem {D : ℕ} {i : ℕ} (v : X → 𝕜) :
    lowering (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      ∈ Submodule.span 𝕜 {w : X → 𝕜 | subconst (𝕜 := 𝕜) G x (i - 1) *ᵥ w = w} := by
  have hcollapse : lowering (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      = if i ∈ Finset.Icc 1 D then
          ((subconst (𝕜 := 𝕜) G x (i - 1) * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0 := by
    rw [lowering, Matrix.sum_mulVec]
    trans ∑ k ∈ Finset.Icc 1 D,
        (if k = i then
          ((subconst (𝕜 := 𝕜) G x (i - 1) * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0)
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVec_block (𝕜 := 𝕜) (G := G) (x := x) i k
        (subconst (𝕜 := 𝕜) G x (k - 1) * adj (𝕜 := 𝕜) G) v]
      by_cases h : k = i
      · subst h; rfl
      · rw [if_neg h, if_neg h]
    · rw [Finset.sum_ite_eq']
  rw [hcollapse]
  by_cases hi : i ∈ Finset.Icc 1 D
  · rw [if_pos hi]
    refine Submodule.subset_span ?_
    exact subconst_mulVec_block (𝕜 := 𝕜) (G := G) (x := x) (i - 1) i v
  · rw [if_neg hi]
    simp

/-- The flat matrix preserves each `E*_iV`. -/
theorem flat_mem {D : ℕ} {i : ℕ} (v : X → 𝕜) :
    flat (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      ∈ Submodule.span 𝕜 {w : X → 𝕜 | subconst (𝕜 := 𝕜) G x i *ᵥ w = w} := by
  have hcollapse : flat (𝕜 := 𝕜) G x D *ᵥ (subconst (𝕜 := 𝕜) G x i *ᵥ v)
      = if i ∈ Finset.range (D + 1) then
          ((subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0 := by
    rw [flat, Matrix.sum_mulVec]
    trans ∑ j ∈ Finset.range (D + 1),
        (if j = i then
          ((subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G) * subconst (𝕜 := 𝕜) G x i) *ᵥ v
        else 0)
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [mulVec_block (𝕜 := 𝕜) (G := G) (x := x) i j
        (subconst (𝕜 := 𝕜) G x j * adj (𝕜 := 𝕜) G) v]
      by_cases h : j = i
      · subst h; rfl
      · rw [if_neg h, if_neg h]
    · rw [Finset.sum_ite_eq']
  rw [hcollapse]
  by_cases hi : i ∈ Finset.range (D + 1)
  · rw [if_pos hi]
    refine Submodule.subset_span ?_
    exact subconst_mulVec_block (𝕜 := 𝕜) (G := G) (x := x) i i v
  · rw [if_neg hi]
    simp

/-! ## The Hermitian form over a general `RCLike` field -/

theorem star_dotProduct_self_eq_zero_rclike {u : X → 𝕜} (h : star u ⬝ᵥ u = 0) : u = 0 := by
  have h1 : star u ⬝ᵥ u = ((∑ x, ‖u x‖ ^ 2 : ℝ) : 𝕜) := by
    rw [dotProduct, RCLike.ofReal_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.star_apply]
    show (starRingEnd 𝕜) (u x) * u x = ((‖u x‖ ^ 2 : ℝ) : 𝕜)
    rw [RCLike.ofReal_pow]
    exact RCLike.conj_mul (u x)
  rw [h1] at h
  have h2 : ((∑ x, ‖u x‖ ^ 2 : ℝ) : 𝕜) = ((0 : ℝ) : 𝕜) := by
    rw [h, RCLike.ofReal_zero]
  have h3 : (∑ x, ‖u x‖ ^ 2 : ℝ) = 0 := RCLike.ofReal_injective h2
  have h4 := (Finset.sum_eq_zero_iff_of_nonneg (fun x (_ : x ∈ Finset.univ) => by positivity)).mp h3
  funext x
  have h5 : ‖u x‖ ^ 2 = 0 := h4 x (Finset.mem_univ x)
  simpa using h5

theorem star_mulVec_dotProduct_rclike (a : Matrix X X 𝕜) (u v : X → 𝕜) :
    star u ⬝ᵥ (a *ᵥ v) = star (star a *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec]
  have h3 : (star a)ᴴ = a := by rw [← Matrix.star_eq_conjTranspose, star_star]
  rw [h3]

theorem selfAdj_star_dotProduct_rclike {a : Matrix X X 𝕜} (ha : star a = a) (u v : X → 𝕜) :
    star (a *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (a *ᵥ v) := by
  rw [star_mulVec_dotProduct_rclike, ha]

variable {G : SimpleGraph X} {x : X}

theorem sum_range_succ_eq_sum_Icc {M : Type*} [AddCommMonoid M] (f : ℕ → M) (D : ℕ) :
    ∑ i ∈ Finset.range D, f (i + 1) = ∑ k ∈ Finset.Icc 1 D, f k := by
  induction D with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega) f]

theorem lowering_eq_sum_range {G : SimpleGraph X} {x : X} (D : ℕ) :
    lowering (𝕜 := 𝕜) G x D
      = ∑ i ∈ Finset.range D,
          subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G * subconst (𝕜 := 𝕜) G x (i + 1) := by
  rw [lowering]
  rw [← sum_range_succ_eq_sum_Icc (f := fun k => subconst (𝕜 := 𝕜) G x (k - 1) * adj (𝕜 := 𝕜) G
    * subconst (𝕜 := 𝕜) G x k)]
  exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_sub_cancel]

theorem star_raising {G : SimpleGraph X} {x : X} {D : ℕ} : star (raising (𝕜 := 𝕜) G x D) = lowering (𝕜 := 𝕜) G x D := by
  rw [lowering_eq_sum_range, raising, star_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [star_mul, star_mul, star_adj, star_subconst, star_subconst, mul_assoc]

theorem star_lowering {G : SimpleGraph X} {x : X} {D : ℕ} : star (lowering (𝕜 := 𝕜) G x D) = raising (𝕜 := 𝕜) G x D := by
  rw [← star_raising, star_star]

theorem star_raising_mul_lowering {G : SimpleGraph X} {x : X} {D : ℕ} :
    star (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D)
      = raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D := by
  rw [star_mul, star_raising, star_lowering]

theorem lowering_eq_zero_of_mul_eq_zero {G : SimpleGraph X} {x : X} {D : ℕ} {v : X → 𝕜}
    (h : (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D) *ᵥ v = 0) :
    lowering (𝕜 := 𝕜) G x D *ᵥ v = 0 := by
  have hstep : star v ⬝ᵥ (raising (𝕜 := 𝕜) G x D *ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v))
      = star (lowering (𝕜 := 𝕜) G x D *ᵥ v) ⬝ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v) := by
    rw [star_mulVec_dotProduct_rclike, star_raising]
  have hzero : star v ⬝ᵥ (raising (𝕜 := 𝕜) G x D *ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v)) = 0 := by
    rw [Matrix.mulVec_mulVec, h, dotProduct_zero]
  rw [hstep] at hzero
  exact star_dotProduct_self_eq_zero_rclike hzero

/-! ## From linear maps to matrices -/

theorem matrix_eq_of_mulVec_eq {M N : Matrix X X 𝕜} (h : ∀ v : X → 𝕜, M *ᵥ v = N *ᵥ v) :
    M = N := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, Matrix.mulVec_single_one, Matrix.col_apply, Matrix.col_apply] at h1

theorem toMatrix'_mulVec (f : (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) (v : X → 𝕜) :
    LinearMap.toMatrix' f *ᵥ v = f v := by
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

theorem toMatrix'_comp (f g : (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) :
    LinearMap.toMatrix' (f.comp g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  rw [toMatrix'_mulVec, LinearMap.comp_apply, ← Matrix.mulVec_mulVec, toMatrix'_mulVec,
    toMatrix'_mulVec]

theorem toMatrix'_one : LinearMap.toMatrix' (1 : (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) = 1 := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  rw [toMatrix'_mulVec, Matrix.one_mulVec]
  rfl

theorem toMatrix'_mulVecLin (M : Matrix X X 𝕜) :
    LinearMap.toMatrix' M.mulVecLin = M := by
  refine matrix_eq_of_mulVec_eq fun v => ?_
  rw [toMatrix'_mulVec, Matrix.mulVecLin_apply]

/-- Every map of the form `v ↦ ∑ cᵢ Tⁱ v` is a matrix. -/
theorem toMatrix'_mul (f g : (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) :
    LinearMap.toMatrix' (f * g) = LinearMap.toMatrix' f * LinearMap.toMatrix' g := by
  rw [Module.End.mul_eq_comp, toMatrix'_comp]

theorem toMatrix'_comp_pow (T : Matrix X X 𝕜) (k : ℕ) :
    LinearMap.toMatrix' (T.mulVecLin ^ k) = T ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero]; exact toMatrix'_one
  | succ n ih =>
    rw [pow_succ, pow_succ, toMatrix'_mul, ih, toMatrix'_mulVecLin]

/-! ## The inverse of an invertible endomorphism lies in the span of its powers -/

theorem linearEquiv_symm_mem_span_pow {W : Type*} [AddCommGroup W] [Module 𝕜 W]
    [FiniteDimensional 𝕜 W] (u : W ≃ₗ[𝕜] W) :
    (u.symm : W →ₗ[𝕜] W) ∈ Submodule.span 𝕜 (Set.range (fun k : ℕ => (u : W →ₗ[𝕜] W) ^ k)) := by
  classical
  set B : Submodule 𝕜 (W →ₗ[𝕜] W) :=
    Submodule.span 𝕜 (Set.range (fun k : ℕ => (u : W →ₗ[𝕜] W) ^ k)) with hB
  have hpow : ∀ k : ℕ, ((u : W →ₗ[𝕜] W) ^ k) ∈ B := fun k => Submodule.subset_span ⟨k, rfl⟩
  have hBmul : ∀ y ∈ B, (u : W →ₗ[𝕜] W) * y ∈ B := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      rw [← pow_succ']
      exact hpow (k + 1)
    | zero => simp
    | add a b _ _ iha ihb => rw [mul_add]; exact Submodule.add_mem _ iha ihb
    | smul c a _ iha => rw [mul_smul_comm]; exact Submodule.smul_mem _ c iha
  have hsu : (u.symm : W →ₗ[𝕜] W) * (u : W →ₗ[𝕜] W) = 1 := by
    ext x
    rw [Module.End.mul_apply]
    simp
  let φ : ↥B →ₗ[𝕜] ↥B :=
    { toFun := fun y => ⟨(u : W →ₗ[𝕜] W) * (y : W →ₗ[𝕜] W), hBmul y y.2⟩
      map_add' := by intro a b; ext; simp [mul_add]
      map_smul' := by intro c a; ext; simp }
  have hφ_inj : Function.Injective φ := by
    intro a b hab
    have h1 : (u : W →ₗ[𝕜] W) * (a : W →ₗ[𝕜] W) = (u : W →ₗ[𝕜] W) * (b : W →ₗ[𝕜] W) := by
      have h2 := congrArg (fun z : ↥B => (z : W →ₗ[𝕜] W)) hab
      simpa only [φ, LinearMap.coe_mk, AddHom.coe_mk] using h2
    have h3 : (a : W →ₗ[𝕜] W) = (b : W →ₗ[𝕜] W) := by
      calc (a : W →ₗ[𝕜] W)
          = ((u.symm : W →ₗ[𝕜] W) * (u : W →ₗ[𝕜] W)) * (a : W →ₗ[𝕜] W) := by rw [hsu, one_mul]
        _ = (u.symm : W →ₗ[𝕜] W) * ((u : W →ₗ[𝕜] W) * (a : W →ₗ[𝕜] W)) := by rw [mul_assoc]
        _ = (u.symm : W →ₗ[𝕜] W) * ((u : W →ₗ[𝕜] W) * (b : W →ₗ[𝕜] W)) := by rw [h1]
        _ = ((u.symm : W →ₗ[𝕜] W) * (u : W →ₗ[𝕜] W)) * (b : W →ₗ[𝕜] W) := by rw [mul_assoc]
        _ = (b : W →ₗ[𝕜] W) := by rw [hsu, one_mul]
    exact Subtype.ext h3
  have hφ_surj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφ_inj
  obtain ⟨y, hy⟩ := hφ_surj ⟨(1 : W →ₗ[𝕜] W), hpow 0⟩
  have hy1 : (u : W →ₗ[𝕜] W) * (y : W →ₗ[𝕜] W) = 1 := by
    have h2 := congrArg (fun z : ↥B => (z : W →ₗ[𝕜] W)) hy
    simpa only [φ, LinearMap.coe_mk, AddHom.coe_mk] using h2
  have hfin : (u.symm : W →ₗ[𝕜] W) = (y : W →ₗ[𝕜] W) := by
    conv_lhs => rw [← mul_one (u.symm : W →ₗ[𝕜] W), ← hy1]
    rw [← mul_assoc, hsu, one_mul]
  rw [hfin]
  exact y.2

theorem mem_span_range_map {W₁ W₂ : Type*} [AddCommGroup W₁] [Module 𝕜 W₁]
    [AddCommGroup W₂] [Module 𝕜 W₂] (Φ : W₁ →ₗ[𝕜] W₂) (f : ℕ → W₁) {x : W₁}
    (hx : x ∈ Submodule.span 𝕜 (Set.range f)) :
    Φ x ∈ Submodule.span 𝕜 (Set.range (fun k => Φ (f k))) := by
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨k, rfl⟩ := hy; exact Submodule.subset_span ⟨k, rfl⟩
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

/-! ## The kernel and the range of `R L` -/

theorem ker_mulVecLin_raising_mul_lowering {G : SimpleGraph X} {x : X} (D : ℕ) :
    (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.ker
      = (lowering (𝕜 := 𝕜) G x D).mulVecLin.ker := by
  set R := raising (𝕜 := 𝕜) G x D with hR
  set L := lowering (𝕜 := 𝕜) G x D with hL
  set Tm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := (R * L).mulVecLin with hTm
  set Lm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := L.mulVecLin with hLm
  have hTm_apply : ∀ v : X → 𝕜, Tm v = (R * L) *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  have hLm_apply : ∀ v : X → 𝕜, Lm v = L *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hTm_apply] at hv
    rw [hLm_apply]
    exact lowering_eq_zero_of_mul_eq_zero (G := G) (x := x)
      (by rw [← hTm_apply]; exact hv)
  · intro v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hLm_apply] at hv
    rw [hTm_apply, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

theorem isCompl_ker_range_mulVecLin_raising_mul_lowering {G : SimpleGraph X} {x : X} (D : ℕ) :
    IsCompl (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.ker
      (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.range := by
  set R := raising (𝕜 := 𝕜) G x D with hR
  set L := lowering (𝕜 := 𝕜) G x D with hL
  set Tm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := (R * L).mulVecLin with hTm
  set Lm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := L.mulVecLin with hLm
  have hTm_apply : ∀ v : X → 𝕜, Tm v = (R * L) *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  have hself : star (R * L) = R * L := by rw [hR, hL]; exact star_raising_mul_lowering
  have hdisj : Disjoint Tm.ker Tm.range := by
    refine disjoint_iff_inf_le.mpr ?_
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvk, hvr⟩ := hv
    have hvk' : Tm v = 0 := LinearMap.mem_ker.mp hvk
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hvr
    have h1 : Tm (Tm w) = 0 := by rw [hw]; exact hvk'
    have h2 : (R * L) *ᵥ ((R * L) *ᵥ w) = 0 := by
      have e1 : Tm (Tm w) = (R * L) *ᵥ (Tm w) := hTm_apply (Tm w)
      have e2 : Tm w = (R * L) *ᵥ w := hTm_apply w
      rw [e2] at e1
      rw [← e1]; exact h1
    have h3 : star ((R * L) *ᵥ w) ⬝ᵥ ((R * L) *ᵥ w) = 0 := by
      rw [selfAdj_star_dotProduct_rclike hself w ((R * L) *ᵥ w), h2, dotProduct_zero]
    have h4 : (R * L) *ᵥ w = 0 := star_dotProduct_self_eq_zero_rclike h3
    rw [Submodule.mem_bot, ← hw, hTm_apply, h4]
  have hcompl : IsCompl Tm.ker Tm.range := by
    refine (Submodule.isCompl_iff_disjoint _ _ ?_).mpr hdisj
    have h := LinearMap.finrank_range_add_finrank_ker Tm
    omega
  exact hcompl

theorem ker_sup_range_mulVecLin_raising_mul_lowering {G : SimpleGraph X} {x : X} (D : ℕ) :
    (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.ker
        ⊔ (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.range = ⊤ :=
  (isCompl_ker_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D).sup_eq_top

theorem ker_inf_range_mulVecLin_raising_mul_lowering {G : SimpleGraph X} {x : X} (D : ℕ) :
    (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.ker
        ⊓ (raising (𝕜 := 𝕜) G x D * lowering (𝕜 := 𝕜) G x D).mulVecLin.range = ⊥ :=
  (isCompl_ker_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D).inf_eq_bot

theorem lowering_mem_subconstituentAlgebra {G : SimpleGraph X} {x : X} (D : ℕ) :
    lowering (𝕜 := 𝕜) G x D ∈ (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra := by
  rw [lowering_eq_sum_range]
  refine Subalgebra.sum_mem _ ?_
  intro i _
  exact mul_mem (mul_mem
    (StarSubalgebra.mem_toSubalgebra.mpr (subconst_mem_subconstituentAlgebra G x i))
    (StarSubalgebra.mem_toSubalgebra.mpr (adj_mem_subconstituentAlgebra G x)))
    (StarSubalgebra.mem_toSubalgebra.mpr (subconst_mem_subconstituentAlgebra G x (i + 1)))

theorem raising_mem_subconstituentAlgebra {G : SimpleGraph X} {x : X} (D : ℕ) :
    raising (𝕜 := 𝕜) G x D ∈ (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra := by
  rw [raising]
  refine Subalgebra.sum_mem _ ?_
  intro i _
  exact mul_mem (mul_mem
    (StarSubalgebra.mem_toSubalgebra.mpr (subconst_mem_subconstituentAlgebra G x (i + 1)))
    (StarSubalgebra.mem_toSubalgebra.mpr (adj_mem_subconstituentAlgebra G x)))
    (StarSubalgebra.mem_toSubalgebra.mpr (subconst_mem_subconstituentAlgebra G x i))

/-! ## Lemma 31.1: `R⁻¹` -/

private theorem exists_raising_inverse_mem {G : SimpleGraph X} {x : X} (D : ℕ) :
    ∃ Rinv : Matrix X X 𝕜,
      (∀ v : X → 𝕜, lowering (𝕜 := 𝕜) G x D *ᵥ v = 0 → Rinv *ᵥ v = 0) ∧
      (∀ v : X → 𝕜, Rinv *ᵥ (raising (𝕜 := 𝕜) G x D *ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v))
        = lowering (𝕜 := 𝕜) G x D *ᵥ v) ∧
      Rinv ∈ subconstituentAlgebra (𝕜 := 𝕜) G x := by
  set R := raising (𝕜 := 𝕜) G x D with hR
  set L := lowering (𝕜 := 𝕜) G x D with hL
  set T := R * L with hT
  set Tm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := T.mulVecLin with hTm
  set Lm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := L.mulVecLin with hLm
  have hTm_apply : ∀ v : X → 𝕜, Tm v = T *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  have hLm_apply : ∀ v : X → 𝕜, Lm v = L *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  have hmv : ∀ (v : X → 𝕜), T *ᵥ v = R *ᵥ (L *ᵥ v) := by
    intro v; rw [hT, Matrix.mulVec_mulVec]
  have hker : Tm.ker = Lm.ker := by
    rw [hTm, hLm]
    exact ker_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  have hsup : Tm.ker ⊔ Tm.range = ⊤ := by
    rw [hTm]
    exact ker_sup_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  have hinf : Tm.ker ⊓ Tm.range = ⊥ := by
    rw [hTm]
    exact ker_inf_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  -- the restricted map `T : range T → range T` is bijective
  set Tmr : (X → 𝕜) →ₗ[𝕜] Tm.range :=
    Tm.codRestrict Tm.range (fun c => LinearMap.mem_range.mpr ⟨c, rfl⟩) with hTmr
  have hTmr_apply : ∀ v : X → 𝕜, ((Tmr v : Tm.range) : X → 𝕜) = Tm v := by
    intro v
    rw [hTmr]
    exact LinearMap.codRestrict_apply _ _ v
  set TR : Tm.range →ₗ[𝕜] Tm.range :=
    (Tm.domRestrict Tm.range).codRestrict Tm.range
      (fun c => LinearMap.mem_range.mpr ⟨(c : X → 𝕜), rfl⟩) with hTR
  have hTR_apply : ∀ y : Tm.range, ((TR y : Tm.range) : X → 𝕜) = Tm (y : X → 𝕜) := by
    intro y
    rw [hTR, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply]
  have hTR_inj : Function.Injective TR := by
    intro a b hab
    have h1 : Tm ((a : X → 𝕜) - (b : X → 𝕜)) = 0 := by
      have h2 : Tm (a : X → 𝕜) = Tm (b : X → 𝕜) := by
        have h3 := congrArg (fun z : Tm.range => (z : X → 𝕜)) hab
        rw [hTR_apply, hTR_apply] at h3
        exact h3
      rw [map_sub, h2, sub_self]
    have h2' : ((a : X → 𝕜) - (b : X → 𝕜)) ∈ Tm.ker := LinearMap.mem_ker.mpr h1
    have h4 : ((a : X → 𝕜) - (b : X → 𝕜)) ∈ Tm.ker ⊓ Tm.range :=
      ⟨h2', Submodule.sub_mem _ a.2 b.2⟩
    have h5 : ((a : X → 𝕜) - (b : X → 𝕜)) = 0 := by
      have h6 : ((a : X → 𝕜) - (b : X → 𝕜)) ∈ (⊥ : Submodule 𝕜 (X → 𝕜)) := by
        rw [← hinf]
        exact h4
      simpa using h6
    exact Subtype.ext (sub_eq_zero.mp h5)
  have hTR_bij : Function.Bijective TR :=
    ⟨hTR_inj, LinearMap.injective_iff_surjective.mp hTR_inj⟩
  set e : Tm.range ≃ₗ[𝕜] Tm.range := LinearEquiv.ofBijective TR hTR_bij with he
  have he_val : ∀ y : Tm.range, ((e y : Tm.range) : X → 𝕜) = Tm (y : X → 𝕜) := by
    intro y
    rw [he, LinearEquiv.ofBijective_apply, hTR_apply]
  set pT : (X → 𝕜) →ₗ[𝕜] Tm.range := e.symm.toLinearMap.comp Tmr with hpT
  have hpT_apply : ∀ v : X → 𝕜, pT v = e.symm ⟨Tm v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ := by
    intro v
    rw [hpT]
    simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
    rfl
  have hpT_range : ∀ y : Tm.range, pT (y : X → 𝕜) = y := by
    intro y
    have h1 : pT (y : X → 𝕜) = e.symm (e y) := by
      rw [hpT_apply]
      congr 1
    rw [h1]
    exact LinearEquiv.symm_apply_apply e y
  have hTm_pT : ∀ v : X → 𝕜, Tm (pT v : X → 𝕜) = Tm v := by
    intro v
    have h1 : Tm (pT v : X → 𝕜)
        = ((e (e.symm ⟨Tm v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩) : Tm.range) : X → 𝕜) := by
      rw [hpT_apply]
      exact (he_val _).symm
    rw [h1, LinearEquiv.apply_symm_apply]
  set RinvLin : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) :=
    Lm.comp (Tm.range.subtype.comp (e.symm.toLinearMap.comp pT)) with hRinvLin
  have hRinvLin_apply : ∀ v : X → 𝕜,
      RinvLin v = L *ᵥ ((e.symm (pT v) : Tm.range) : X → 𝕜) := by
    intro v
    rw [hRinvLin]
    simp only [LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hLm_apply]
    rfl
  have key : ∀ u : X → 𝕜,
      L *ᵥ ((e.symm (pT (R *ᵥ (L *ᵥ u))) : Tm.range) : X → 𝕜) = L *ᵥ u := by
    intro u
    have hu : (R *ᵥ (L *ᵥ u)) ∈ Tm.range := by
      have h1 : Tm u = R *ᵥ (L *ᵥ u) := by rw [hTm_apply, hmv]
      rw [← h1]; exact LinearMap.mem_range_self Tm u
    have hpT_hu : pT (R *ᵥ (L *ᵥ u)) = ⟨R *ᵥ (L *ᵥ u), hu⟩ :=
      hpT_range ⟨R *ᵥ (L *ᵥ u), hu⟩
    rw [hpT_hu]
    have hxT : Tm ((e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜) = Tm u := by
      have h1 : Tm ((e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜)
          = ((e (e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩) : Tm.range) : X → 𝕜) := (he_val _).symm
      rw [h1, LinearEquiv.apply_symm_apply]
      have h2 : ((⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜) = R *ᵥ (L *ᵥ u) := rfl
      rw [h2, hTm_apply, hmv]
    have hx : ((e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜) - u ∈ Tm.ker := by
      rw [LinearMap.mem_ker, map_sub, hxT, sub_self]
    have hxL : L *ᵥ (((e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜) - u) = 0 := by
      rw [hker] at hx
      have hx' : Lm (((e.symm ⟨R *ᵥ (L *ᵥ u), hu⟩ : Tm.range) : X → 𝕜) - u) = 0 := hx
      rwa [hLm_apply] at hx'
    rw [Matrix.mulVec_sub, sub_eq_zero] at hxL
    exact hxL
  -- `R⁻¹` satisfies the two conditions
  have hia : ∀ v : X → 𝕜, L *ᵥ v = 0 → LinearMap.toMatrix' RinvLin *ᵥ v = 0 := by
    intro v hv
    rw [toMatrix'_mulVec, hRinvLin_apply]
    have hvT : Tm v = 0 := by rw [hTm_apply, hmv, hv, Matrix.mulVec_zero]
    have h1 : pT v = 0 := by
      have h2 : (⟨Tm v, LinearMap.mem_range.mpr ⟨v, rfl⟩⟩ : Tm.range) = 0 := Subtype.ext hvT
      rw [hpT_apply, h2, map_zero]
    rw [h1]
    simp
  have hib : ∀ v : X → 𝕜,
      LinearMap.toMatrix' RinvLin *ᵥ (R *ᵥ (L *ᵥ v)) = L *ᵥ v := by
    intro v
    rw [toMatrix'_mulVec, hRinvLin_apply]
    exact key v
  -- `R⁻¹` lies in `T(x)`: it is a limit of powers of `T`
  have hmem : LinearMap.toMatrix' RinvLin ∈ subconstituentAlgebra (𝕜 := 𝕜) G x := by
    -- (1) `e.symm` lies in the span of the powers of `e`
    have hspan : (e.symm : Tm.range →ₗ[𝕜] Tm.range)
        ∈ Submodule.span 𝕜 (Set.range (fun k : ℕ => e.toLinearMap ^ k)) :=
      linearEquiv_symm_mem_span_pow e
    -- (2) `e` acts on `Tm` and on `pT` as expected
    have he_Tmr : ∀ v : X → 𝕜, e.toLinearMap (Tmr v) = Tmr (Tm v) := by
      intro v
      apply Subtype.ext
      exact (he_val (Tmr v)).trans (hTmr_apply (Tm v)).symm
    have he_pT : ∀ v : X → 𝕜, e.toLinearMap (pT v) = Tmr v := by
      intro v
      apply Subtype.ext
      exact (he_val (pT v)).trans (hTm_pT v)
    -- (3) the powers of `e` on the image of `Tm`
    have hpow : ∀ (k : ℕ) (v : X → 𝕜),
        (e.toLinearMap ^ k) (Tmr v) = Tmr ((Tm ^ k) v) := by
      intro k
      induction k with
      | zero => intro v; rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
      | succ n ih =>
        intro v
        rw [pow_succ', Module.End.mul_apply, ih v, he_Tmr ((Tm ^ n) v), pow_succ',
          Module.End.mul_apply]
    -- (4) the composites of the powers of `e` with `Tm`, resp. `pT`
    have hcompTmr : ∀ (k : ℕ) (v : X → 𝕜),
        ((Tm.range.subtype.comp ((e.toLinearMap ^ k).comp Tmr)) :
          (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) v = (Tm ^ (k + 1)) v := by
      intro k v
      rw [LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply, hpow k v,
        hTmr_apply, pow_succ', Module.End.mul_apply]
    have hcomp_pT : ∀ (j : ℕ) (v : X → 𝕜),
        ((Tm.range.subtype.comp ((e.toLinearMap ^ (j + 1)).comp pT)) :
          (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) v = (Tm ^ (j + 1)) v := by
      intro j v
      have h1 : (e.toLinearMap ^ (j + 1)).comp pT = (e.toLinearMap ^ j).comp Tmr := by
        rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_assoc]
        congr 1
        exact LinearMap.ext (fun w => he_pT w)
      rw [h1, LinearMap.comp_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        hpow j v, hTmr_apply, pow_succ', Module.End.mul_apply]
    -- (5) the maps `Φ` and `Ψ`
    set Φ : (Tm.range →ₗ[𝕜] Tm.range) →ₗ[𝕜] ((X → 𝕜) →ₗ[𝕜] (X → 𝕜)) :=
      { toFun := fun y => Lm.comp (Tm.range.subtype.comp (y.comp pT))
        map_add' := by intro a b; ext v; simp
        map_smul' := by intro c a; ext v; simp } with hΦ
    set Ψ : (Tm.range →ₗ[𝕜] Tm.range) →ₗ[𝕜] ((X → 𝕜) →ₗ[𝕜] (X → 𝕜)) :=
      { toFun := fun y => Lm.comp (Tm.range.subtype.comp (y.comp Tmr))
        map_add' := by intro a b; ext v; simp
        map_smul' := by intro c a; ext v; simp } with hΨ
    -- (6) the matrices `Φ (e^k)` and `Ψ (e^k)`
    set matMap : ((X → 𝕜) →ₗ[𝕜] (X → 𝕜)) →ₗ[𝕜] Matrix X X 𝕜 :=
      LinearMap.toMatrix'.toLinearMap with hmatMap
    have hmat_apply : ∀ f : (X → 𝕜) →ₗ[𝕜] (X → 𝕜), matMap f = LinearMap.toMatrix' f :=
      fun f => rfl
    have htoMat : ∀ f : (X → 𝕜) →ₗ[𝕜] (X → 𝕜), matMap (Lm.comp f) = L * matMap f := by
      intro f
      rw [hmat_apply, hmat_apply, toMatrix'_comp, toMatrix'_mulVecLin]
    have hTpow : ∀ j : ℕ, matMap ((Tm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜)) ^ j) = T ^ j := by
      intro j
      rw [hmat_apply, hTm]
      exact toMatrix'_comp_pow T j
    have hΨk : ∀ k : ℕ, matMap (Ψ (e.toLinearMap ^ k)) = L * T ^ (k + 1) := by
      intro k
      have h1 : Ψ (e.toLinearMap ^ k) = Lm.comp (Tm ^ (k + 1)) := by
        rw [hΨ]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [LinearMap.ext (fun w => hcompTmr k w)]
      rw [h1, htoMat, hTpow]
    have hΦ1 : Φ (1 : Tm.range →ₗ[𝕜] Tm.range) = Ψ (e.symm).toLinearMap := by
      rw [hΦ, hΨ, hpT]
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Module.End.one_eq_id, LinearMap.id_comp]
    have hΦj : ∀ j : ℕ, matMap (Φ (e.toLinearMap ^ (j + 1))) = L * T ^ (j + 1) := by
      intro j
      have h1 : Φ (e.toLinearMap ^ (j + 1)) = Lm.comp (Tm ^ (j + 1)) := by
        rw [hΦ]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [LinearMap.ext (fun w => hcomp_pT j w)]
      rw [h1, htoMat, hTpow]
    -- (6b) hence both matrices lie in the span of the `L * T^j`
    have hΨspan : matMap (Ψ (e.symm).toLinearMap)
        ∈ Submodule.span 𝕜 (Set.range (fun j : ℕ => L * T ^ j)) := by
      have h1 := mem_span_range_map Ψ (fun k : ℕ => e.toLinearMap ^ k) hspan
      have h2 := mem_span_range_map matMap (fun k : ℕ => Ψ (e.toLinearMap ^ k)) h1
      refine Submodule.span_le.mpr (fun M hM => ?_) h2
      obtain ⟨k, rfl⟩ := hM
      dsimp only
      rw [hΨk k]
      exact Submodule.subset_span ⟨k + 1, rfl⟩
    have hΦspan : matMap (Φ (e.symm).toLinearMap)
        ∈ Submodule.span 𝕜 (Set.range (fun j : ℕ => L * T ^ j)) := by
      have h1 := mem_span_range_map Φ (fun k : ℕ => e.toLinearMap ^ k) hspan
      have h2 := mem_span_range_map matMap (fun k : ℕ => Φ (e.toLinearMap ^ k)) h1
      refine Submodule.span_le.mpr (fun M hM => ?_) h2
      obtain ⟨k, rfl⟩ := hM
      dsimp only
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        rw [pow_zero, hΦ1]
        exact hΨspan
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rw [hΦj j]
        exact Submodule.subset_span ⟨j + 1, rfl⟩
    -- (7) the span lies in `T(x)`, and `Rinv` is the matrix of `Φ e.symm`
    have hle : Submodule.span 𝕜 (Set.range (fun j : ℕ => L * T ^ j))
        ≤ (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra.toSubmodule := by
      refine Submodule.span_le.mpr ?_
      rintro M ⟨j, rfl⟩
      have hLmem : L ∈ (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra :=
        lowering_mem_subconstituentAlgebra (𝕜 := 𝕜) (G := G) (x := x) D
      have hTmem : T ∈ (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra :=
        mul_mem (raising_mem_subconstituentAlgebra (𝕜 := 𝕜) (G := G) (x := x) D) hLmem
      exact (Subalgebra.mem_toSubmodule _).mpr (mul_mem hLmem (Subalgebra.pow_mem _ hTmem j))
    have hRinvΦ : LinearMap.toMatrix' RinvLin = matMap (Φ (e.symm).toLinearMap) := by
      rw [hmat_apply]
      congr 1
    rw [hRinvΦ, ← StarSubalgebra.mem_toSubalgebra]
    exact (Subalgebra.mem_toSubmodule _).mp (hle hΦspan)
  exact ⟨LinearMap.toMatrix' RinvLin, hia, hib, hmem⟩

/-- **Lemma 31.1.**  The partial inverse `R⁻¹` of the raising matrix: the unique
matrix annihilating `ker L` and inverting `R` on `R L V`.

Parts (ii)–(iv) of the lemma say that `R⁻¹` maps `E*_iV` into `E*_{i-1}V`, has
rational entries, and lies in `T(x)`. -/
theorem existsUnique_raising_inverse {D : ℕ} :
    ∃! Rinv : Matrix X X 𝕜,
      (∀ v : X → 𝕜, lowering (𝕜 := 𝕜) G x D *ᵥ v = 0 → Rinv *ᵥ v = 0) ∧
      (∀ v : X → 𝕜, Rinv *ᵥ (raising (𝕜 := 𝕜) G x D *ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v))
        = lowering (𝕜 := 𝕜) G x D *ᵥ v) := by
  obtain ⟨Rinv, h1, h2, -⟩ := exists_raising_inverse_mem (𝕜 := 𝕜) (G := G) (x := x) D
  refine ⟨Rinv, ⟨h1, h2⟩, ?_⟩
  rintro Rinv' ⟨h1', h2'⟩
  set R := raising (𝕜 := 𝕜) G x D with hR
  set L := lowering (𝕜 := 𝕜) G x D with hL
  set T := R * L with hT
  set Tm : (X → 𝕜) →ₗ[𝕜] (X → 𝕜) := T.mulVecLin with hTm
  have hTm_apply : ∀ v : X → 𝕜, Tm v = T *ᵥ v := fun v => Matrix.mulVecLin_apply _ v
  have hsup : Tm.ker ⊔ Tm.range = ⊤ := by
    rw [hTm]
    exact ker_sup_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  have hinf : Tm.ker ⊓ Tm.range = ⊥ := by
    rw [hTm]
    exact ker_inf_range_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  have hker : Tm.ker = (lowering (𝕜 := 𝕜) G x D).mulVecLin.ker := by
    rw [hTm]
    exact ker_mulVecLin_raising_mul_lowering (𝕜 := 𝕜) (G := G) (x := x) D
  have hmv : ∀ (v : X → 𝕜), Tm v = R *ᵥ (L *ᵥ v) := by
    intro v; rw [hTm_apply, hT, Matrix.mulVec_mulVec]
  refine matrix_eq_of_mulVec_eq fun v => ?_
  have hvsup : v ∈ Tm.ker ⊔ Tm.range := by rw [hsup]; trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hvsup
  obtain ⟨u, hu⟩ := LinearMap.mem_range.mp hb
  have haL : L *ᵥ a = 0 := by
    have h1 : Tm a = 0 := LinearMap.mem_ker.mp ha
    exact lowering_eq_zero_of_mul_eq_zero (G := G) (x := x)
      (by rw [← hTm_apply]; exact h1)
  have hbR : b = R *ᵥ (L *ᵥ u) := by rw [← hu, hmv]
  calc Rinv' *ᵥ v = Rinv' *ᵥ a + Rinv' *ᵥ b := by rw [← hab, Matrix.mulVec_add]
    _ = L *ᵥ u := by rw [h1' a haL, hbR, h2' u, zero_add]
    _ = Rinv *ᵥ a + Rinv *ᵥ b := by rw [h1 a haL, hbR, h2 u, zero_add]
    _ = Rinv *ᵥ v := by rw [← hab, Matrix.mulVec_add]


/-- `R⁻¹ ∈ T(x)`. -/
theorem raising_inverse_mem_subconstituentAlgebra {D : ℕ} :
    ∃ Rinv : Matrix X X 𝕜,
      (∀ v : X → 𝕜, lowering (𝕜 := 𝕜) G x D *ᵥ v = 0 → Rinv *ᵥ v = 0) ∧
      (∀ v : X → 𝕜, Rinv *ᵥ (raising (𝕜 := 𝕜) G x D *ᵥ (lowering (𝕜 := 𝕜) G x D *ᵥ v))
        = lowering (𝕜 := 𝕜) G x D *ᵥ v) ∧
      Rinv ∈ subconstituentAlgebra (𝕜 := 𝕜) G x :=
  exists_raising_inverse_mem (𝕜 := 𝕜) (G := G) (x := x) D

end Terwilliger

