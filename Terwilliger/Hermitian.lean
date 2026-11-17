/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.Basic

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
# The Hermitian pairing on the standard module

Chapter 12 of Terwilliger's notes works with the Hermitian form
`⟨u, v⟩ = ∑ i, conj (u i) * v i` on the standard module `ℂ^X`, written
`star u ⬝ᵥ v` with `Matrix.dotProduct`.  Here we collect the elementary
properties of that form that the argument needs:

* the adjunction identity `⟨u, a v⟩ = ⟨a* u, v⟩` and its self-adjoint case,
* positivity and non-degeneracy of `⟨u, u⟩`, the Euclidean norm `vnorm`,
* the Cauchy–Schwarz inequality,
* orthogonality of vectors with disjoint support and of different
  subconstituents,
* the band lemma `Eᵢ* Aᵐ Eⱼ* = 0` for `|i - j| > m`,
* disjointness of spheres around two vertices (the triangle inequality),
* a hand-rolled orthogonal decomposition `V = W ⊕ W^⊥`.

We deliberately do NOT install an `InnerProductSpace` instance on `X → ℂ`:
the Pi type already carries the sup-norm instance, and the two would clash.
The Cauchy–Schwarz inequality is transported from `EuclideanSpace ℂ X`
(which is the same underlying function type with the ℓ² norm) instead.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The Hermitian pairing on the standard module -/

/-- `⟨u, a v⟩ = ⟨a* u, v⟩`: the adjunction between a matrix and its conjugate
transpose for the Hermitian form. -/
theorem star_mulVec_dotProduct (a : Matrix X X ℂ) (u v : X → ℂ) :
    star u ⬝ᵥ (a *ᵥ v) = star (star a *ᵥ u) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec]
  have h3 : (star a)ᴴ = a := by rw [← Matrix.star_eq_conjTranspose, star_star]
  have h := Matrix.star_mulVec (M := star a) (v := u)
  rw [h3] at h
  rw [← h]

/-- For a self-adjoint matrix `a` the bilinear form is symmetric: `⟨a u, v⟩ = ⟨u, a v⟩`. -/
theorem selfAdj_star_dotProduct {a : Matrix X X ℂ} (ha : star a = a) (u v : X → ℂ) :
    star (a *ᵥ u) ⬝ᵥ v = star u ⬝ᵥ (a *ᵥ v) := by
  rw [star_mulVec_dotProduct, ha]

/-- Conjugate symmetry of the Hermitian form. -/
theorem star_dotProduct_symm (u v : X → ℂ) : star (star u ⬝ᵥ v) = star v ⬝ᵥ u :=
  (Matrix.star_dotProduct v u).symm

/-- `⟨u, u⟩` is a real number. -/
theorem star_dotProduct_self_real (u : X → ℂ) : star (star u ⬝ᵥ u) = star u ⬝ᵥ u :=
  star_dotProduct_symm u u

/-- `⟨u, u⟩ = ∑ i, ‖u i‖²` as a real number. -/
theorem star_dotProduct_self_eq_sum_normSq (u : X → ℂ) :
    star u ⬝ᵥ u = ((∑ x, Complex.normSq (u x) : ℝ) : ℂ) := by
  rw [dotProduct, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Pi.star_apply, Complex.star_def]
  exact (Complex.normSq_eq_conj_mul_self (z := u x)).symm

/-- `⟨u, u⟩` has nonnegative real part. -/
theorem star_dotProduct_self_nonneg (u : X → ℂ) : 0 ≤ (star u ⬝ᵥ u).re := by
  rw [star_dotProduct_self_eq_sum_normSq, Complex.ofReal_re]
  exact Finset.sum_nonneg fun x _ => Complex.normSq_nonneg (u x)

/-- The Hermitian form is non-degenerate. -/
theorem star_dotProduct_self_eq_zero {u : X → ℂ} (h : star u ⬝ᵥ u = 0) : u = 0 := by
  have h1 : (∑ x, Complex.normSq (u x) : ℝ) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zero, ← star_dotProduct_self_eq_sum_normSq]
    exact h
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg
    (fun x (_ : x ∈ Finset.univ) => Complex.normSq_nonneg (u x))).mp h1
  funext x
  exact Complex.normSq_eq_zero.mp (h2 x (Finset.mem_univ x))

/-- The Euclidean norm `‖u‖ = (∑ |uᵢ|²)^½`. -/
noncomputable def vnorm (u : X → ℂ) : ℝ := Real.sqrt ((star u ⬝ᵥ u).re)

theorem vnorm_nonneg (u : X → ℂ) : 0 ≤ vnorm u := Real.sqrt_nonneg _

theorem vnorm_eq_zero {u : X → ℂ} : vnorm u = 0 ↔ u = 0 := by
  rw [vnorm, Real.sqrt_eq_zero (star_dotProduct_self_nonneg u)]
  rw [star_dotProduct_self_eq_sum_normSq, Complex.ofReal_re]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Complex.normSq_nonneg (u x))]
  constructor
  · intro h
    funext x
    exact Complex.normSq_eq_zero.mp (h x (Finset.mem_univ x))
  · intro h x _
    rw [h]
    simp

theorem star_dotProduct_self_re (u : X → ℂ) : (star u ⬝ᵥ u).re = vnorm u * vnorm u := by
  rw [vnorm, Real.mul_self_sqrt (star_dotProduct_self_nonneg u)]

/-- `vnorm` is the ℓ²-norm on the `EuclideanSpace` with the same underlying
function type.  This is the bridge that gives us Cauchy–Schwarz. -/
theorem vnorm_eq_norm (u : X → ℂ) : vnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ X)‖ := by
  rw [vnorm, EuclideanSpace.norm_eq]
  congr 1
  rw [star_dotProduct_self_eq_sum_normSq, Complex.ofReal_re]
  exact Finset.sum_congr rfl fun x _ => Complex.normSq_eq_norm_sq (u x)

/-- **Cauchy–Schwarz inequality** for the Hermitian form. -/
theorem abs_star_dotProduct_le_vnorm (u v : X → ℂ) :
    ‖star u ⬝ᵥ v‖ ≤ vnorm u * vnorm v := by
  have hinner : inner ℂ (WithLp.toLp 2 u : EuclideanSpace ℂ X)
      (WithLp.toLp 2 v : EuclideanSpace ℂ X) = star u ⬝ᵥ v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [dotProduct]
    exact Finset.sum_congr rfl fun x _ => mul_comm _ _
  rw [← hinner, vnorm_eq_norm u, vnorm_eq_norm v]
  exact norm_inner_le_norm _ _

/-- Vectors with disjoint support are orthogonal. -/
theorem star_dotProduct_disjoint {u v : X → ℂ} (h : ∀ i, u i = 0 ∨ v i = 0) :
    star u ⬝ᵥ v = 0 := by
  rw [dotProduct]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases h i with h | h <;> simp [Pi.star_apply, h]

/-! ## Subconstituents and the band lemma -/

/-- `Eᵢ*(x)` fixes its own subconstituent. -/
theorem subconst_mulVec_self {G : SimpleGraph X} {x : X} {i : ℕ} {W : Submodule ℂ (X → ℂ)}
    {v : X → ℂ} (hv : v ∈ subconstImage (𝕜 := ℂ) G x i W) :
    subconst (𝕜 := ℂ) G x i *ᵥ v = v := by
  obtain ⟨t, -, rfl⟩ := mem_matImage.mp hv
  rw [Matrix.mulVec_mulVec, subconst_mul_self]

/-- Vectors in different subconstituents are orthogonal. -/
theorem star_dotProduct_subconstImage_zero {G : SimpleGraph X} {x : X} {i j : ℕ}
    {W W' : Submodule ℂ (X → ℂ)} (hij : i ≠ j) {u v : X → ℂ}
    (hu : u ∈ subconstImage (𝕜 := ℂ) G x i W) (hv : v ∈ subconstImage (𝕜 := ℂ) G x j W') :
    star u ⬝ᵥ v = 0 := by
  obtain ⟨s, -, rfl⟩ := mem_matImage.mp hu
  obtain ⟨t, -, rfl⟩ := mem_matImage.mp hv
  rw [star_mulVec_dotProduct, star_subconst, Matrix.mulVec_mulVec, subconst_mul_subconst,
    if_neg (Ne.symm hij), Matrix.zero_mulVec]
  simp

/-- Entry formula for `Eᵢ*(x) A Eⱼ*(x)`. -/
theorem subconst_mul_adj_mul_subconst_apply' (G : SimpleGraph X) (x : X) (i j : ℕ) (y z : X) :
    (subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j) y z
      = (if G.dist x y = i then 1 else 0) * (if G.Adj y z then 1 else 0)
        * (if G.dist x z = j then 1 else 0) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single z]
  · rw [Matrix.mul_apply, Finset.sum_eq_single y]
    · rw [subconst_apply, if_pos rfl, adj_apply, subconst_apply, if_pos rfl]
    · intro b _ hb
      rw [subconst_apply, if_neg (Ne.symm hb), zero_mul]
    · intro h; exact absurd (Finset.mem_univ y) h
  · intro b _ hb
    rw [subconst_apply, if_neg hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ z) h

/-- **Lemma 4.3 (i)**, the one-step band lemma.  (This is
`Terwilliger.subconst_mul_adj_mul_subconst_eq_zero` of `Subconstituent.lean`,
re-proved here so that this file only depends on `Terwilliger.Basic`.) -/
theorem subconst_mul_adj_mul_subconst_eq_zero' {G : SimpleGraph X} {x : X} {i j : ℕ}
    (h : j + 1 < i ∨ i + 1 < j) :
    subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j = 0 := by
  ext y z
  rw [subconst_mul_adj_mul_subconst_apply', Matrix.zero_apply]
  by_cases hadj : G.Adj y z
  · by_cases h1 : G.dist x y = i
    · by_cases h2 : G.dist x z = j
      · exfalso
        have h3 := hadj.diff_dist_adj (u := x)
        omega
      · simp [h1, h2]
    · simp [h1]
  · simp [hadj]

/-- Splitting a product of matrices along the family `Eₖ*(x)`. -/
theorem sum_subconst_mul {G : SimpleGraph X} {x : X} {D : ℕ}
    (hD : ∀ y, G.dist x y ≤ D) (P Q : Matrix X X ℂ) :
    P * Q = ∑ k ∈ Finset.range (D + 1), (P * subconst (𝕜 := ℂ) G x k) * Q := by
  have hQ : Q = ∑ k ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x k * Q := by
    rw [← Finset.sum_mul, sum_subconst_eq_one (𝕜 := ℂ) G x D hD, one_mul]
  conv_lhs => rw [hQ]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => (mul_assoc P (subconst (𝕜 := ℂ) G x k) Q).symm

/-- **Lemma 4.3 (i), iterated.**  `Aᵐ` moves the `j`-th subconstituent to within
distance `m` of the `i`-th one: `Eᵢ*(x) Aᵐ Eⱼ*(x) = 0` whenever `|i - j| > m`. -/
theorem subconst_mul_adj_pow_mul_subconst_eq_zero {G : SimpleGraph X} {x : X} {i j m : ℕ}
    (hij : j + m < i ∨ i + m < j) :
    subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G ^ m * subconst (𝕜 := ℂ) G x j = 0 := by
  induction m generalizing i j with
  | zero =>
    have hij' : i ≠ j := by omega
    rw [pow_zero, mul_one, subconst_mul_subconst, if_neg hij']
  | succ m ih =>
    set D : ℕ := Finset.univ.sup (fun z : X => G.dist x z) with hDdef
    have hD : ∀ y, G.dist x y ≤ D := fun y => Finset.le_sup (Finset.mem_univ y)
    rcases hij with h | h
    · have hstep : subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G ^ (m + 1)
          * subconst (𝕜 := ℂ) G x j
          = ∑ k ∈ Finset.range (D + 1),
              ((subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G) * subconst (𝕜 := ℂ) G x k)
                * (adj (𝕜 := ℂ) G ^ m * subconst (𝕜 := ℂ) G x j) := by
        rw [pow_succ', ← mul_assoc (subconst (𝕜 := ℂ) G x i) (adj (𝕜 := ℂ) G)
          (adj (𝕜 := ℂ) G ^ m), mul_assoc,
          sum_subconst_mul (G := G) (x := x) hD]
      rw [hstep, Finset.sum_eq_zero]
      intro k _
      by_cases hk : j + m < k
      · have h0 : subconst (𝕜 := ℂ) G x k * adj (𝕜 := ℂ) G ^ m * subconst (𝕜 := ℂ) G x j
            = 0 := ih (i := k) (j := j) (Or.inl hk)
        rw [mul_assoc] at h0
        rw [mul_assoc, h0, mul_zero]
      · have hk' : k + 1 < i := by omega
        have h0 : subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x k = 0 :=
          subconst_mul_adj_mul_subconst_eq_zero' (Or.inl hk')
        rw [h0, zero_mul]
    · have hstep : subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G ^ (m + 1)
          * subconst (𝕜 := ℂ) G x j
          = ∑ k ∈ Finset.range (D + 1),
              ((subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G ^ m) * subconst (𝕜 := ℂ) G x k)
                * (adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j) := by
        rw [pow_succ, ← mul_assoc (subconst (𝕜 := ℂ) G x i) (adj (𝕜 := ℂ) G ^ m)
          (adj (𝕜 := ℂ) G), mul_assoc,
          sum_subconst_mul (G := G) (x := x) hD]
      rw [hstep, Finset.sum_eq_zero]
      intro k _
      by_cases hk : i + m < k
      · have h0 : subconst (𝕜 := ℂ) G x i * adj (𝕜 := ℂ) G ^ m * subconst (𝕜 := ℂ) G x k
            = 0 := ih (i := i) (j := k) (Or.inr hk)
        rw [h0, zero_mul]
      · have hk' : k + 1 < j := by omega
        have h0 : subconst (𝕜 := ℂ) G x k * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j = 0 :=
          subconst_mul_adj_mul_subconst_eq_zero' (Or.inr hk')
        rw [mul_assoc] at h0
        rw [mul_assoc, h0, mul_zero]

/-- The spheres around `x` and around `y` of radii `i` and `j` are disjoint as soon as
`i > ∂(x,y) + j`. -/
theorem not_dist_eq_of_lt {G : SimpleGraph X} (hG : G.Connected) {x y : X} {i j : ℕ}
    (h : G.dist x y + j < i) (z : X) : ¬(G.dist x z = i ∧ G.dist y z = j) := by
  rintro ⟨h1, h2⟩
  have htri : G.dist x z ≤ G.dist x y + G.dist y z := hG.dist_triangle
  omega

/-! ## The orthogonal decomposition of the standard module

We prove `V = W ⊕ W^⊥` by induction on `dim W`, without ever building an
`InnerProductSpace` instance on `X → ℂ`. -/

theorem exists_orthogonal_decomp_aux (n : ℕ) (W : Submodule ℂ (X → ℂ))
    (hW : Module.finrank ℂ ↥W ≤ n) (v : X → ℂ) :
    ∃ h ∈ W, ∀ u ∈ W, star u ⬝ᵥ (v - h) = 0 := by
  induction n generalizing W with
  | zero =>
    have hbot : W = ⊥ := by
      by_contra hne
      obtain ⟨b, hbW, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hle : Submodule.span ℂ ({b} : Set (X → ℂ)) ≤ W :=
        Submodule.span_le.mpr (by simpa using hbW)
      have h1 : Module.finrank ℂ ↥(Submodule.span ℂ ({b} : Set (X → ℂ))) = 1 :=
        finrank_span_singleton (K := ℂ) (V := X → ℂ) hb0
      have h2 : Module.finrank ℂ ↥(Submodule.span ℂ ({b} : Set (X → ℂ)))
          ≤ Module.finrank ℂ ↥W := Submodule.finrank_mono (R := ℂ) hle
      omega
    refine ⟨0, by simp [hbot], ?_⟩
    intro u hu
    have hu0 : u = 0 := by simpa [hbot] using hu
    simp [hu0]
  | succ n ih =>
    by_cases hbot : W = ⊥
    · refine ⟨0, by simp [hbot], ?_⟩
      intro u hu
      have hu0 : u = 0 := by simpa [hbot] using hu
      simp [hu0]
    obtain ⟨b, hbW, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hbs : star b ⬝ᵥ b ≠ 0 := fun h => hb0 (star_dotProduct_self_eq_zero h)
    set W₁ : Submodule ℂ (X → ℂ) :=
      W ⊓ orthCompl (Submodule.span ℂ ({b} : Set (X → ℂ))) with hW₁def
    have hW₁le : W₁ ≤ W := hW₁def ▸ inf_le_left
    have hbP : b ∈ Submodule.span ℂ ({b} : Set (X → ℂ)) :=
      Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩
    have hbW₁ : b ∉ W₁ := by
      intro hb
      exact hbs (mem_orthCompl.mp (Submodule.mem_inf.mp (hW₁def ▸ hb)).2 b hbP)
    have hW₁lt : W₁ < W := lt_of_le_of_ne hW₁le (fun h => hbW₁ (h ▸ hbW))
    have hfr : Module.finrank ℂ ↥W₁ ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hW₁lt
      omega
    obtain ⟨h₁, hh₁, horth₁⟩ := ih W₁ hfr
    have hh₁inf : h₁ ∈ W ⊓ orthCompl (Submodule.span ℂ ({b} : Set (X → ℂ))) :=
      hW₁def ▸ hh₁
    have hh₁W : h₁ ∈ W := (Submodule.mem_inf.mp hh₁inf).1
    have hh₁orth : ∀ x ∈ Submodule.span ℂ ({b} : Set (X → ℂ)), star x ⬝ᵥ h₁ = 0 :=
      fun x hx => (Submodule.mem_inf.mp hh₁inf).2 x hx
    refine ⟨h₁ + (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b, ?_, ?_⟩
    · exact Submodule.add_mem _ hh₁W (Submodule.smul_mem _ _ hbW)
    · intro u hu
      set d : ℂ := star b ⬝ᵥ u / (star b ⬝ᵥ b) with hd
      have hu₁inf : u - d • b ∈ W ⊓ orthCompl (Submodule.span ℂ ({b} : Set (X → ℂ))) := by
        refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hbW), ?_⟩
        intro x hx
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [star_smul, smul_dotProduct, hd, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have hzero : star b ⬝ᵥ u - (star b ⬝ᵥ u / (star b ⬝ᵥ b)) • (star b ⬝ᵥ b) = 0 := by
          rw [smul_eq_mul, div_mul_cancel₀ _ hbs, sub_self]
        rw [hzero, mul_zero]
      have hu₁W₁ : u - d • b ∈ W₁ := hW₁def.symm ▸ hu₁inf
      have hu₁orth : star b ⬝ᵥ (u - d • b) = 0 :=
        mem_orthCompl.mp (Submodule.mem_inf.mp hu₁inf).2 b hbP
      have horth_u₁ : star (u - d • b) ⬝ᵥ (v - h₁) = 0 := horth₁ _ hu₁W₁
      have horth_u₁' : star (u - d • b) ⬝ᵥ b = 0 := by
        rw [← star_dotProduct_symm, hu₁orth, star_zero]
      have hu_split : u = d • b + (u - d • b) := by abel
      have hvsub : v - (h₁ + (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b)
          = (v - h₁) - (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b := by abel
      rw [hvsub, hu_split, star_add, star_smul, add_dotProduct, smul_dotProduct]
      have hb1 : star b ⬝ᵥ ((v - h₁) - (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have hq : star b ⬝ᵥ (v - h₁) - star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b) * (star b ⬝ᵥ b) = 0 := by
          rw [div_mul_cancel₀ _ hbs, sub_self]
        exact hq
      have hb2 : star (u - d • b)
          ⬝ᵥ ((v - h₁) - (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b) = 0 := by
        rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, horth_u₁, horth_u₁', mul_zero,
          sub_zero]
      rw [hb1, hb2, smul_zero, add_zero]

theorem exists_orthogonal_decomp {W : Submodule ℂ (X → ℂ)} (v : X → ℂ) :
    ∃ h ∈ W, ∀ u ∈ W, star u ⬝ᵥ (v - h) = 0 :=
  exists_orthogonal_decomp_aux (Module.finrank ℂ ↥W) W le_rfl v

theorem orthogonal_decomp_unique {W : Submodule ℂ (X → ℂ)} {v h₁ h₂ : X → ℂ}
    (hh₁ : h₁ ∈ W) (hh₂ : h₂ ∈ W) (o₁ : ∀ u ∈ W, star u ⬝ᵥ (v - h₁) = 0)
    (o₂ : ∀ u ∈ W, star u ⬝ᵥ (v - h₂) = 0) : h₁ = h₂ := by
  have hd : h₁ - h₂ ∈ W := Submodule.sub_mem _ hh₁ hh₂
  have k1 : star (h₁ - h₂) ⬝ᵥ (v - h₁) = 0 := o₁ _ hd
  have k2 : star (h₁ - h₂) ⬝ᵥ (v - h₂) = 0 := o₂ _ hd
  have hzero : star (h₁ - h₂) ⬝ᵥ (h₁ - h₂) = 0 := by
    have hd2 : h₁ - h₂ = (v - h₂) - (v - h₁) := by abel
    have key : star (h₁ - h₂) ⬝ᵥ ((v - h₂) - (v - h₁)) = 0 := by
      rw [dotProduct_sub, k2, k1, sub_zero]
    rw [hd2] at key ⊢
    exact key
  exact sub_eq_zero.mp (star_dotProduct_self_eq_zero hzero)

end Terwilliger
