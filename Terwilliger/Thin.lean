/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.DistanceRegular
import Terwilliger.Spectral

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
# The structure of a thin `T(x)`-module (Chapters 9–10)

Let `W` be a thin irreducible `T(x)`-module with endpoint `r` and diameter `d`.
The notes attach to `W` two sequences of scalars

* `aᵢ(W)`, defined by `E*_{r+i} A E*_{r+i}|_{E*_{r+i}W} = aᵢ(W) · 1`, and
* `xᵢ(W)`, defined by `E*_{r+i-1} A E*_{r+i} A E*_{r+i-1}|_{E*_{r+i-1}W} = xᵢ(W) · 1`,

and then prove (Lemma 9.2) that `aᵢ(W)` is real, `xᵢ(W)` is real and positive, and
that for `0 ≠ w₀ ∈ E*_r W`, the vectors `wᵢ = E*_{r+i} Aⁱ w₀` form a basis of `W`
on which `A` is tridiagonal; the characteristic polynomial of that tridiagonal
matrix is the minimal polynomial of `A|_W`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The scalars `aᵢ(W)`: `A` acts on `E*_{r+i}W` by the scalar `a i`. -/
def HasThinA (G : SimpleGraph X) (x : X) (W : Submodule 𝕜 (X → 𝕜)) (r : ℕ)
    (a : ℕ → 𝕜) : Prop :=
  ∀ i v, v ∈ subconstImage (𝕜 := 𝕜) G x (r + i) W →
    subconst (𝕜 := 𝕜) G x (r + i) *ᵥ (adj (𝕜 := 𝕜) G *ᵥ v) = a i • v

/-- The scalars `xᵢ(W)`: `E*_{r+i-1} A E*_{r+i} A` acts on `E*_{r+i-1}W` by the
scalar `x i`. -/
def HasThinX (G : SimpleGraph X) (x : X) (W : Submodule 𝕜 (X → 𝕜)) (r : ℕ)
    (xs : ℕ → 𝕜) : Prop :=
  ∀ i v, 1 ≤ i → v ∈ subconstImage (𝕜 := 𝕜) G x (r + i - 1) W →
    subconst (𝕜 := 𝕜) G x (r + i - 1) *ᵥ
        (adj (𝕜 := 𝕜) G *ᵥ (subconst (𝕜 := 𝕜) G x (r + i) *ᵥ
          (adj (𝕜 := 𝕜) G *ᵥ v)))
      = xs i • v

/-- The polynomial sequence `p₀, p₁, …` of Lemma 9.2 (iv):
`p₀ = 1`, `p₁ = λ - a₀`, `λ pᵢ = p_{i+1} + aᵢ pᵢ + xᵢ p_{i-1}`. -/
def thinPoly (a xs : ℕ → ℂ) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.X - Polynomial.C (a 0)
  | (i + 2) => Polynomial.X * thinPoly a xs (i + 1)
      - Polynomial.C (a (i + 1)) * thinPoly a xs (i + 1)
      - Polynomial.C (xs (i + 1)) * thinPoly a xs i

/-! ## Monicity and degree of the polynomials `pᵢ` -/

/-- **Lemma 9.2 (iv), monicity.** -/
theorem thinPoly_monic_degree (a xs : ℕ → ℂ) (i : ℕ) :
    (thinPoly a xs i).Monic ∧ (thinPoly a xs i).natDegree = i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i with
    | 0 => exact ⟨by simp [thinPoly], by simp [thinPoly]⟩
    | 1 =>
      refine ⟨?_, ?_⟩
      · simpa [thinPoly] using Polynomial.monic_X_sub_C (a 0)
      · simpa [thinPoly] using Polynomial.natDegree_X_sub_C (a 0)
    | (k + 2) =>
      obtain ⟨hm1, hd1⟩ := ih (k + 1) (by omega)
      obtain ⟨hm0, hd0⟩ := ih k (by omega)
      have hfac : thinPoly a xs (k + 2)
          = (Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)
            - Polynomial.C (xs (k + 1)) * thinPoly a xs k := by
        rw [thinPoly, sub_mul]
      have hmon : ((Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)).Monic :=
        (Polynomial.monic_X_sub_C _).mul hm1
      have hdeg : ((Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)).natDegree
          = k + 2 := by
        rw [Polynomial.Monic.natDegree_mul (Polynomial.monic_X_sub_C _) hm1,
          Polynomial.natDegree_X_sub_C, hd1]
        omega
      have hlow : (Polynomial.C (xs (k + 1)) * thinPoly a xs k).natDegree ≤ k := by
        have h := Polynomial.natDegree_mul_le (p := Polynomial.C (xs (k + 1)))
          (q := thinPoly a xs k)
        rw [Polynomial.natDegree_C, hd0] at h
        omega
      have hlow' : (Polynomial.C (xs (k + 1)) * thinPoly a xs k).natDegree
          < ((Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)).natDegree := by
        rw [hdeg]; omega
      refine ⟨?_, ?_⟩
      · rw [hfac]
        exact Polynomial.Monic.sub_of_left hmon (Polynomial.degree_lt_degree hlow')
      · rw [hfac, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlow', hdeg]

/-! ## Vector-level bookkeeping -/

/-- The basis vectors `wᵢ = E*_{r+i}(x) Aⁱ w₀` of Lemma 9.2 (iii). -/
def thinVec (G : SimpleGraph X) (x : X) (r : ℕ) (w₀ : X → ℂ) (i : ℕ) : X → ℂ :=
  subconst (𝕜 := ℂ) G x (r + i) *ᵥ ((adj (𝕜 := ℂ) G) ^ i *ᵥ w₀)

/-- The span of the vectors `w₀, …, w_d`. -/
def thinSpan (G : SimpleGraph X) (x : X) (r d : ℕ) (w₀ : X → ℂ) : Submodule ℂ (X → ℂ) :=
  Submodule.span ℂ (Set.range (fun i : Fin (d + 1) => thinVec G x r w₀ (i : ℕ)))

/-- Each generator `wᵢ` (`i ≤ d`) lies in `thinSpan`. -/
theorem thinVec_mem_thinSpan (G : SimpleGraph X) (x : X) (r d : ℕ) (w₀ : X → ℂ)
    (i : ℕ) (hi : i < d + 1) : thinVec G x r w₀ i ∈ thinSpan G x r d w₀ := by
  rw [thinSpan]
  refine Submodule.subset_span ?_
  exact ⟨⟨i, hi⟩, rfl⟩

variable {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)} {r d : ℕ}
  {a xs : ℕ → ℂ} {w₀ : X → ℂ}

/-- `Aⁱ` lies in `T(x)`. -/
theorem adj_pow_mem_subconstituentAlgebra (G : SimpleGraph X) (x : X) (i : ℕ) :
    adj (𝕜 := ℂ) G ^ i ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra :=
  Subalgebra.pow_mem _ (adj_mem_subconstituentAlgebra G x) i

/-- A vector of the `r`-th subconstituent of `W` lies in `W`. -/
theorem mem_of_mem_subconstImage
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) : w₀ ∈ W := by
  obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hw
  exact hstable _ (subconst_mem_subconstituentAlgebra G x r) t ht

/-- `wᵢ` lies in the `(r+i)`-th subconstituent of `W`. -/
theorem thinVec_mem
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (i : ℕ) :
    thinVec G x r w₀ i ∈ subconstImage (𝕜 := ℂ) G x (r + i) W :=
  mem_matImage.2 ⟨_, hstable _ (Subalgebra.pow_mem _ (adj_mem_subconstituentAlgebra G x) i)
    w₀ (mem_of_mem_subconstImage hstable hw₀), rfl⟩

/-- `wᵢ` itself lies in `W`. -/
theorem thinVec_mem_W
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (i : ℕ) :
    thinVec G x r w₀ i ∈ W := by
  have h := hstable (subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G ^ i)
      (mul_mem (subconst_mem_subconstituentAlgebra G x (r + i))
        (Subalgebra.pow_mem _ (adj_mem_subconstituentAlgebra G x) i))
      w₀ (mem_of_mem_subconstImage hstable hw₀)
  simpa only [thinVec, Matrix.mulVec_mulVec] using h

/-- The `E*_j` act on `wᵢ` as the identity for `j = r + i` and as zero otherwise. -/
theorem subconst_mulVec_thinVec (i j : ℕ) :
    subconst (𝕜 := ℂ) G x j *ᵥ thinVec G x r w₀ i
      = if j = r + i then thinVec G x r w₀ i else 0 := by
  have h : subconst (𝕜 := ℂ) G x j *ᵥ thinVec G x r w₀ i
      = (subconst (𝕜 := ℂ) G x j * subconst (𝕜 := ℂ) G x (r + i)) *ᵥ
          (adj (𝕜 := ℂ) G ^ i *ᵥ w₀) := by
    rw [thinVec, Matrix.mulVec_mulVec]
  rw [h, subconst_mul_subconst]
  by_cases hji : j = r + i
  · rw [if_pos hji, hji, thinVec]; simp
  · rw [if_neg hji, Matrix.zero_mulVec, if_neg hji]

/-- `E*_k(x)` vanishes on the `(r+i)`-th subconstituent once `k > r + i`. -/
theorem subconst_mulVec_adj_pow_w0_eq_zero
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i k : ℕ} (hk : r + i < k) :
    subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G ^ i *ᵥ w₀) = 0 := by
  have hw0' : w₀ = subconst (𝕜 := ℂ) G x r *ᵥ w₀ := (subconst_mulVec_self hw₀).symm
  rw [hw0', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    subconst_mul_adj_pow_mul_subconst_eq_zero (x := x) (i := k) (j := r) (m := i)
      (Or.inl (by omega))]
  exact Matrix.zero_mulVec _

/-- `E*_k = 0` for `k` beyond the eccentricity of `x`. -/
theorem subconst_eq_zero_of_lt {D k : ℕ} (hD : ∀ y, G.dist x y ≤ D) (hk : D < k) :
    subconst (𝕜 := ℂ) G x k = 0 := by
  ext y z
  rw [subconst_apply, Matrix.zero_apply]
  by_cases hyz : y = z
  · subst hyz
    rw [if_pos rfl, if_neg (by have := hD y; omega)]
  · rw [if_neg hyz]

/-- The subconstituent projections resolve the identity on vectors. -/
theorem mulVec_eq_sum_subconst_mulVec {D : ℕ} (hD : ∀ y, G.dist x y ≤ D) (v : X → ℂ) :
    v = ∑ k ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x k *ᵥ v := by
  symm
  calc ∑ k ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x k *ᵥ v
      = (∑ k ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x k) *ᵥ v :=
        (Matrix.sum_mulVec _ _ _).symm
    _ = 1 *ᵥ v := by rw [sum_subconst_eq_one G x D hD]
    _ = v := Matrix.one_mulVec v

/-- The nonvanishing half of `IsDiameter` pins the subconstituents inside the
range of the distance function. -/
theorem le_of_diam {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) {i : ℕ} (hi : i ≤ d) : r + i ≤ D := by
  by_contra hcon
  have hne := hdiam.1 (r + i) (by omega) (by omega)
  have hz : subconst (𝕜 := ℂ) G x (r + i) = 0 := subconst_eq_zero_of_lt (x := x) hD (by omega)
  apply hne
  rw [subconstImage, eq_bot_iff]
  intro v hv
  obtain ⟨t, -, rfl⟩ := mem_matImage.1 hv
  rw [hz, Matrix.zero_mulVec, Submodule.mem_bot]

/-- `wᵢ = 0` beyond the diameter. -/
theorem thinVec_eq_zero_of_lt
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i : ℕ} (hi : d < i) :
    thinVec G x r w₀ i = 0 := by
  have hbot : subconstImage (𝕜 := ℂ) G x (r + i) W = ⊥ := by
    by_contra hne
    have := (hdiam.2 (r + i) hne).2
    omega
  have hmem := thinVec_mem (G := G) (x := x) (W := W) (r := r) hstable hw₀ i
  rw [hbot] at hmem
  simpa using hmem

/-- `E*_k(x)` kills `W` below the endpoint. -/
theorem subconst_mulVec_eq_zero_of_lt_endpoint
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) {v : X → ℂ} (hv : v ∈ W) {k : ℕ} (hk : k < r) :
    subconst (𝕜 := ℂ) G x k *ᵥ v = 0 := by
  have hmem : subconst (𝕜 := ℂ) G x k *ᵥ v ∈ subconstImage (𝕜 := ℂ) G x k W :=
    mem_matImage.2 ⟨v, hv, rfl⟩
  rw [hend.2 k hk] at hmem
  simpa using hmem

/-- **Locality.**  For `j ≥ r + i + 1` the projection `E*_j A` cannot distinguish
`Aⁱ w₀` from its `(r+i)`-th subconstituent `wᵢ`. -/
theorem subconst_mulVec_adj_eq {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i j : ℕ} (hj : r + i + 1 ≤ j)
    (hDi : r + i ≤ D) :
    subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ (adj (𝕜 := ℂ) G ^ i *ᵥ w₀))
      = subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i) := by
  set u : X → ℂ := adj (𝕜 := ℂ) G ^ i *ᵥ w₀ with hu
  have hexp : u = ∑ k ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x k *ᵥ u :=
    mulVec_eq_sum_subconst_mulVec hD u
  have hthin : thinVec G x r w₀ i = subconst (𝕜 := ℂ) G x (r + i) *ᵥ u := rfl
  rw [hthin]
  have hL : subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ u)
      = ∑ k ∈ Finset.range (D + 1),
          (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x k) *ᵥ u := by
    conv_lhs => rw [Matrix.mulVec_mulVec, hexp]
    rw [Matrix.mulVec_sum]
    exact Finset.sum_congr rfl (fun k _ => by rw [Matrix.mulVec_mulVec])
  have hR : subconst (𝕜 := ℂ) G x j *ᵥ
        (adj (𝕜 := ℂ) G *ᵥ (subconst (𝕜 := ℂ) G x (r + i) *ᵥ u))
      = (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G *
          subconst (𝕜 := ℂ) G x (r + i)) *ᵥ u := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hL, hR]
  have hsum : ∑ k ∈ Finset.range (D + 1),
        (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x k) *ᵥ u
      = (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G *
          subconst (𝕜 := ℂ) G x (r + i)) *ᵥ u := by
    refine Finset.sum_eq_single_of_mem (r + i) (Finset.mem_range.2 (by omega)) ?_
    intro k _ hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [subconst_mul_adj_mul_subconst_eq_zero (x := x) (i := j) (j := k) (Or.inl (by omega)),
        Matrix.zero_mulVec]
    · have hstep : (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G) *ᵥ
          (subconst (𝕜 := ℂ) G x k *ᵥ u) = 0 := by
        rw [subconst_mulVec_adj_pow_w0_eq_zero (x := x) hw₀ (i := i) (k := k) (by omega),
          Matrix.mulVec_zero]
      rw [← Matrix.mulVec_mulVec, hstep]
  rw [hsum]

/-- `A w₀ = w₁ + a₀ w₀`. -/
theorem adj_mulVec_thinVec_zero {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) (ha : HasThinA G x W r a)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) :
    adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0
      = thinVec G x r w₀ 1 + a 0 • thinVec G x r w₀ 0 := by
  have hw0 : thinVec G x r w₀ 0 = w₀ := by
    simp only [thinVec, Nat.add_zero, pow_zero, Matrix.one_mulVec]
    exact subconst_mulVec_self hw₀
  have hLHS := mulVec_eq_sum_subconst_mulVec (G := G) (x := x) hD
    (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0)
  have hRHS := mulVec_eq_sum_subconst_mulVec (G := G) (x := x) hD
    (thinVec G x r w₀ 1 + a 0 • thinVec G x r w₀ 0)
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hkD : k ≤ D := by simpa using hk
  rw [Matrix.mulVec_add, Matrix.mulVec_smul,
    subconst_mulVec_thinVec (w₀ := w₀) 1 k, subconst_mulVec_thinVec (w₀ := w₀) 0 k]
  by_cases h1 : k = r
  · have hkey : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0)
        = a 0 • thinVec G x r w₀ 0 := by
      rw [hw0, h1]
      exact ha 0 w₀ hw₀
    rw [hkey, h1]
    simp
  · by_cases h2 : k = r + 1
    · have hkey : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0)
          = thinVec G x r w₀ 1 := by
        rw [h2, hw0]
        simp only [thinVec, pow_one]
      rw [hkey, h2]
      simp [Ne.symm h1]
    · have hle : k < r ∨ r + 1 < k := by omega
      have hz : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0) = 0 := by
        rw [hw0]
        rcases hle with hle | hle
        · exact subconst_mulVec_eq_zero_of_lt_endpoint hstable hend
            (hstable _ (adj_mem_subconstituentAlgebra G x) w₀
              (mem_of_mem_subconstImage hstable hw₀)) hle
        · rw [show w₀ = subconst (𝕜 := ℂ) G x r *ᵥ w₀ from (subconst_mulVec_self hw₀).symm,
            Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            subconst_mul_adj_mul_subconst_eq_zero (x := x) (i := k) (j := r) (Or.inl (by omega)),
            Matrix.zero_mulVec]
      rw [hz]
      simp [h1, h2]

/-- The `xᵢ`-relation in the shape needed for the tridiagonal action: the two
index forms `r + (i-1)` and `r + i - 1` are identified before applying
`HasThinX`. -/
theorem thinVec_adj_mulVec_eq_smul
    (hx : HasThinX G x W r xs)
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i : ℕ}
    (hwi : thinVec G x r w₀ i
      = subconst (𝕜 := ℂ) G x (r + i) *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ (i - 1)))
    (hi : 1 ≤ i) :
    subconst (𝕜 := ℂ) G x (r + (i - 1)) *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i)
      = xs i • thinVec G x r w₀ (i - 1) := by
  have hidx : r + (i - 1) = r + i - 1 := by omega
  have hv : thinVec G x r w₀ (i - 1) ∈ subconstImage (𝕜 := ℂ) G x (r + i - 1) W := by
    rw [← hidx]
    exact thinVec_mem hstable hw₀ (i - 1)
  have hh := hx i (thinVec G x r w₀ (i - 1)) hi hv
  rw [hwi]
  rw [hidx]
  exact hh


/-- `A wᵢ = w_{i+1} + aᵢ wᵢ + xᵢ w_{i-1}` for `1 ≤ i ≤ d`. -/
theorem adj_mulVec_thinVec_succ {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W)
    {i : ℕ} (hi : 1 ≤ i) (hid : i ≤ d) :
    adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i
      = thinVec G x r w₀ (i + 1) + a i • thinVec G x r w₀ i
        + xs i • thinVec G x r w₀ (i - 1) := by
  have hidx : r + (i - 1) = r + i - 1 := by omega
  have e1 : r + (i + 1) ≠ r + i := by omega
  have e2 : r + (i - 1) ≠ r + i := by omega
  have e3 : r + (i + 1) ≠ r + (i - 1) := by omega
  have hpow : adj (𝕜 := ℂ) G ^ i = adj (𝕜 := ℂ) G * adj (𝕜 := ℂ) G ^ (i - 1) := by
    have h := pow_succ' (adj (𝕜 := ℂ) G) (i - 1)
    rwa [Nat.sub_add_cancel hi] at h
  have hwi : thinVec G x r w₀ i
      = subconst (𝕜 := ℂ) G x (r + i) *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ (i - 1)) := by
    rw [thinVec, hpow, ← Matrix.mulVec_mulVec]
    exact subconst_mulVec_adj_eq (W := W) hD hw₀ (i := i - 1) (j := r + i) (by omega)
      (le_of_diam hD hdiam (by omega))
  have hwsucc : thinVec G x r w₀ (i + 1)
      = subconst (𝕜 := ℂ) G x (r + i + 1) *ᵥ
          (adj (𝕜 := ℂ) G *ᵥ (adj (𝕜 := ℂ) G ^ i *ᵥ w₀)) := by
    rw [thinVec, pow_succ', ← Matrix.mulVec_mulVec]
    rfl
  have hLHS := mulVec_eq_sum_subconst_mulVec (G := G) (x := x) hD
    (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i)
  have hRHS := mulVec_eq_sum_subconst_mulVec (G := G) (x := x) hD
    (thinVec G x r w₀ (i + 1) + a i • thinVec G x r w₀ i
      + xs i • thinVec G x r w₀ (i - 1))
  rw [hLHS, hRHS]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    subconst_mulVec_thinVec (i := i + 1) (j := k),
    subconst_mulVec_thinVec (i := i) (j := k),
    subconst_mulVec_thinVec (i := i - 1) (j := k)]
  by_cases h1 : k = r + i
  · have hkey : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i)
        = a i • thinVec G x r w₀ i := by
      rw [h1]
      exact ha i _ (thinVec_mem (r := r) hstable hw₀ i)
    rw [hkey, if_neg (show ¬ (k = r + (i + 1)) from by rw [h1]; exact Ne.symm e1),
      if_pos h1, if_neg (show ¬ (k = r + (i - 1)) from by rw [h1]; exact Ne.symm e2)]
    simp
  · by_cases h2 : k = r + i + 1
    · have hloc := subconst_mulVec_adj_eq (W := W) hD hw₀ (i := i) (j := r + i + 1)
        (le_refl _) (le_of_diam hD hdiam hid)
      have hkey : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i)
          = thinVec G x r w₀ (i + 1) := by
        rw [h2, ← hloc, hwsucc]
      rw [hkey, if_pos (show k = r + (i + 1) from h2),
        if_neg (show ¬ (k = r + i) from by rw [h2]; exact e1),
        if_neg (show ¬ (k = r + (i - 1)) from by rw [h2]; exact e3)]
      simp
    · by_cases h3 : k = r + (i - 1)
      · have hkey := thinVec_adj_mulVec_eq_smul (W := W) hx hstable hw₀ hwi hi
        rw [h3, hkey, if_neg (Ne.symm e3), if_neg e2, if_pos rfl]
        simp
      · have hz : subconst (𝕜 := ℂ) G x k *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i) = 0 := by
          rcases lt_or_ge k r with hlt | hge
          · exact subconst_mulVec_eq_zero_of_lt_endpoint hstable hend
              (hstable _ (adj_mem_subconstituentAlgebra G x) _
                (thinVec_mem_W (r := r) hstable hw₀ i)) hlt
          · have hb : k + 1 < r + i ∨ r + i + 1 < k := by omega
            have hmat : subconst (𝕜 := ℂ) G x k * adj (𝕜 := ℂ) G *
                subconst (𝕜 := ℂ) G x (r + i) = 0 :=
              subconst_mul_adj_mul_subconst_eq_zero (x := x) (i := k) (j := r + i)
                (hb.elim (fun h => Or.inr h) (fun h => Or.inl h))
            rw [hwi, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hmat, Matrix.zero_mulVec]
        rw [hz, if_neg (show ¬ (k = r + (i + 1)) from by omega), if_neg h1, if_neg h3]
        simp

/-- **Stability from generators**: a subspace stable under `A` and under every
`Eᵢ*(x)` is a `T(x)`-module. -/
theorem isStable_of_generators {U : Submodule ℂ (X → ℂ)}
    (hA : ∀ v ∈ U, adj (𝕜 := ℂ) G *ᵥ v ∈ U)
    (hE : ∀ (i : ℕ) (v : X → ℂ), v ∈ U → subconst (𝕜 := ℂ) G x i *ᵥ v ∈ U) :
    IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra U := by
  intro m hm
  have hEq : (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra
      = Algebra.adjoin ℂ (({adj (𝕜 := ℂ) G} ∪ Set.range (subconst (𝕜 := ℂ) G x)) ∪
          star ({adj (𝕜 := ℂ) G} ∪ Set.range (subconst (𝕜 := ℂ) G x))) :=
    StarAlgebra.adjoin_toSubalgebra _ _
  rw [hEq] at hm
  induction hm using Algebra.adjoin_induction with
  | mem a ha =>
      rcases ha with ha | ha
      · rcases ha with ha | ha
        · rw [Set.mem_singleton_iff] at ha
          subst ha
          exact hA
        · obtain ⟨i, rfl⟩ := ha
          exact hE i
      · have ha' : star a ∈ ({adj (𝕜 := ℂ) G} ∪ Set.range (subconst (𝕜 := ℂ) G x)) :=
          Set.mem_star.mp ha
        rcases ha' with ha' | ⟨i, hi⟩
        · rw [Set.mem_singleton_iff] at ha'
          have hstar : a = adj (𝕜 := ℂ) G := by
            rw [← star_star a, ha']
            exact star_adj (𝕜 := ℂ) G
          rw [hstar]
          exact hA
        · have hstar : a = subconst (𝕜 := ℂ) G x i := by
            rw [← star_star a, ← hi]
            exact star_subconst (𝕜 := ℂ) G x i
          rw [hstar]
          exact hE i
  | algebraMap c =>
      intro v hv
      have h1 : (algebraMap ℂ (Matrix X X ℂ)) c *ᵥ v = c • v := by
        funext z
        rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
        rfl
      rw [h1]
      exact Submodule.smul_mem _ c hv
  | add a b _ _ iha ihb =>
      intro v hv
      rw [Matrix.add_mulVec]
      exact Submodule.add_mem _ (iha v hv) (ihb v hv)
  | mul a b _ _ iha ihb =>
      intro v hv
      rw [← Matrix.mulVec_mulVec]
      exact iha _ (ihb v hv)

/-- **Nonvanishing of the connective maps.**  For `r ≤ j < r + d` the map
`E*_{j+1} A` does not kill `E*_j W`; otherwise the span of the subconstituents
`E*_0 W, …, E*_j W` would be a proper nonzero `T(x)`-submodule of `W`. -/
theorem up_nonvanishing
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    {D : ℕ} (hD : ∀ y, G.dist x y ≤ D) {j : ℕ} (hj : r ≤ j) (hjd : j < r + d) :
    ¬ (∀ v ∈ subconstImage (𝕜 := ℂ) G x j W,
        subconst (𝕜 := ℂ) G x (j + 1) *ᵥ (adj (𝕜 := ℂ) G *ᵥ v) = 0) := by
  intro H
  set U : Submodule ℂ (X → ℂ) :=
    Finset.sup (Finset.range (j + 1)) (fun k => subconstImage (𝕜 := ℂ) G x k W) with hU
  have hUk : ∀ k ≤ j, subconstImage (𝕜 := ℂ) G x k W ≤ U := by
    intro k hk
    have h : subconstImage (𝕜 := ℂ) G x k W ≤
        Finset.sup (Finset.range (j + 1)) (fun k => subconstImage (𝕜 := ℂ) G x k W) :=
      Finset.le_sup (b := k) (f := fun k => subconstImage (𝕜 := ℂ) G x k W)
        (Finset.mem_range.2 (by omega))
    rwa [← hU] at h
  have hUW : U ≤ W := by
    rw [hU]
    refine Finset.sup_le (fun k hk v hv => ?_)
    obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hv
    exact hstable _ (subconst_mem_subconstituentAlgebra G x k) t ht
  have hAU : ∀ v ∈ U, adj (𝕜 := ℂ) G *ᵥ v ∈ U := by
    have hKU : U ≤ Submodule.comap (adj (𝕜 := ℂ) G).mulVecLin U := by
      rw [hU]
      refine Finset.sup_le (fun k hk v hv => ?_)
      rw [Finset.mem_range] at hk
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
      have hexp : adj (𝕜 := ℂ) G *ᵥ v
          = ∑ m ∈ Finset.range (D + 1), subconst (𝕜 := ℂ) G x m *ᵥ (adj (𝕜 := ℂ) G *ᵥ v) :=
        mulVec_eq_sum_subconst_mulVec hD _
      rw [hexp]
      refine Submodule.sum_mem _ (fun m hm => ?_)
      rw [Finset.mem_range] at hm
      by_cases hmj : m ≤ j
      · have hmem : subconst (𝕜 := ℂ) G x m *ᵥ (adj (𝕜 := ℂ) G *ᵥ v)
            ∈ subconstImage (𝕜 := ℂ) G x m W :=
          mem_matImage.2 ⟨_, hstable _ (adj_mem_subconstituentAlgebra G x) v (hUW (hUk k (by omega) hv)),
            rfl⟩
        exact hUk m hmj hmem
      · by_cases hmk : m = k + 1
        · subst hmk
          have hkj : k = j := by omega
          subst hkj
          rw [H v hv]
          exact Submodule.zero_mem _
        · obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hv
          have hband : k + 1 < m ∨ m + 1 < k := by omega
          rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
            subconst_mul_adj_mul_subconst_eq_zero (x := x) (i := m) (j := k) hband,
            Matrix.zero_mulVec]
          exact Submodule.zero_mem _
    intro v hv
    exact hKU hv
  have hEU : ∀ (i : ℕ) (v : X → ℂ), v ∈ U → subconst (𝕜 := ℂ) G x i *ᵥ v ∈ U := by
    intro i
    have hKU : U ≤ Submodule.comap (subconst (𝕜 := ℂ) G x i).mulVecLin U := by
      rw [hU]
      refine Finset.sup_le (fun k hk v hv => ?_)
      rw [Finset.mem_range] at hk
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply]
      obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hv
      rw [Matrix.mulVec_mulVec, subconst_mul_subconst]
      by_cases hik : i = k
      · subst hik
        rw [if_pos rfl]
        exact hUk i (by omega) (mem_matImage.2 ⟨t, ht, rfl⟩)
      · rw [if_neg hik, Matrix.zero_mulVec]
        exact Submodule.zero_mem _
    intro v hv
    exact hKU hv
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hle := hUk r hj
    rw [hbot] at hle
    exact hend.1 (le_bot_iff.1 hle)
  have hUeq : U = W := hirr.2 U hUW (isStable_of_generators hAU hEU) hUne
  have hUKer : U ≤ LinearMap.ker (subconst (𝕜 := ℂ) G x (r + d)).mulVecLin := by
    rw [hU]
    refine Finset.sup_le (fun k hk v hv => ?_)
    rw [Finset.mem_range] at hk
    obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, subconst_mul_subconst,
      if_neg (by omega), Matrix.zero_mulVec]
  have hne : subconstImage (𝕜 := ℂ) G x (r + d) W ≠ ⊥ := hdiam.1 (r + d) (by omega) (by omega)
  have hex : ∃ v ∈ subconstImage (𝕜 := ℂ) G x (r + d) W, v ≠ 0 := by
    by_contra h
    apply hne
    rw [Submodule.eq_bot_iff]
    intro v hv
    by_contra hv0
    exact h ⟨v, hv, hv0⟩
  obtain ⟨v, hv, hv0⟩ := hex
  have hvW : v ∈ W := by
    obtain ⟨t, ht, rfl⟩ := mem_matImage.1 hv
    exact hstable _ (subconst_mem_subconstituentAlgebra G x (r + d)) t ht
  have h0 : subconst (𝕜 := ℂ) G x (r + d) *ᵥ v = 0 := hUKer (hUeq ▸ hvW)
  rw [subconst_mulVec_self hv] at h0
  exact hv0 h0

/-- A subspace of dimension at most one is spanned by any nonzero vector of it
(the complex case of `exists_smul_of_finrank_le_one`). -/
theorem exists_smul_of_finrank_le_one_complex {p : Submodule ℂ (X → ℂ)}
    (hfr : Module.finrank ℂ ↥p ≤ 1) {u v : X → ℂ}
    (hu : u ∈ p) (hv : v ∈ p) (hu0 : u ≠ 0) : ∃ c : ℂ, v = c • u := by
  have hspan : Submodule.span ℂ ({u} : Set (X → ℂ)) = p := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      simpa using hu
    · rw [finrank_span_singleton (K := ℂ) (V := X → ℂ) hu0]
      exact hfr
  rw [← hspan] at hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
  exact ⟨c, hc.symm⟩

/-- Thinness makes every subconstituent a line. -/
theorem exists_smul_of_mem_subconstImage (hthin : ThinModule (𝕜 := ℂ) G x W) {i : ℕ}
    {u v : X → ℂ} (hu : u ∈ subconstImage (𝕜 := ℂ) G x i W)
    (hv : v ∈ subconstImage (𝕜 := ℂ) G x i W) (hu0 : u ≠ 0) : ∃ c : ℂ, v = c • u :=
  exists_smul_of_finrank_le_one_complex (hthin i) hu hv hu0

/-- The vectors `wᵢ` do not vanish for `i ≤ d`. -/
theorem thinVec_ne_zero
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    ∀ i, i ≤ d → thinVec G x r w₀ i ≠ 0 := by
  intro i
  induction i with
  | zero =>
      intro _
      rw [show thinVec G x r w₀ 0 = w₀ from by
        simp only [thinVec, Nat.add_zero, pow_zero, Matrix.one_mulVec]
        exact subconst_mulVec_self hw₀]
      exact hw₀ne
  | succ i ih =>
      intro hi
      have hi' : i ≤ d := by omega
      have hprev : thinVec G x r w₀ i ≠ 0 := ih hi'
      have hstep : thinVec G x r w₀ (i + 1)
          = subconst (𝕜 := ℂ) G x (r + i + 1) *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i) := by
        rw [thinVec, pow_succ', ← Matrix.mulVec_mulVec]
        exact subconst_mulVec_adj_eq (W := W) hD hw₀ (i := i) (j := r + i + 1) (by omega)
          (le_of_diam hD hdiam hi')
      intro hzero
      refine up_nonvanishing hstable hirr hend hdiam (D := D) hD (j := r + i) (by omega)
        (by omega) ?_
      intro v hv
      obtain ⟨c, hc⟩ := exists_smul_of_mem_subconstImage (W := W) hthin
        (thinVec_mem (r := r) hstable hw₀ i) hv hprev
      rw [hc, Matrix.mulVec_smul, Matrix.mulVec_smul, ← hstep, hzero, smul_zero]

/-- The span of `w₀, …, w_d` lies in `W`. -/
theorem thinSpan_le
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) :
    thinSpan G x r d w₀ ≤ W := by
  rw [thinSpan, Submodule.span_le]
  rintro v ⟨i, rfl⟩
  exact thinVec_mem_W (r := r) hstable hw₀ (i : ℕ)

/-- The span of `w₀, …, w_d` is nonzero. -/
theorem thinSpan_ne_bot
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    thinSpan G x r d w₀ ≠ ⊥ := by
  intro hbot
  have hmem : thinVec G x r w₀ 0 ∈ thinSpan G x r d w₀ :=
    thinVec_mem_thinSpan G x r d w₀ 0 (by omega)
  rw [hbot] at hmem
  have h0 : thinVec G x r w₀ 0 = 0 := by simpa using hmem
  rw [show thinVec G x r w₀ 0 = w₀ from by
    simp only [thinVec, Nat.add_zero, pow_zero, Matrix.one_mulVec]
    exact subconst_mulVec_self hw₀] at h0
  exact hw₀ne h0

/-- **Stability.**  The span of `w₀, …, w_d` is a `T(x)`-module. -/
theorem thinSpan_stable
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    (ha : HasThinA G x W r a) (hx : HasThinX G x W r xs) {D : ℕ}
    (hD : ∀ y, G.dist x y ≤ D) (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) :
    IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra (thinSpan G x r d w₀) := by
  have hgen : ∀ i, i < d + 1 → thinVec G x r w₀ i ∈ thinSpan G x r d w₀ :=
    fun i hi => thinVec_mem_thinSpan G x r d w₀ i hi
  have hAU : ∀ v ∈ thinSpan G x r d w₀, adj (𝕜 := ℂ) G *ᵥ v ∈ thinSpan G x r d w₀ := by
    intro v hv
    rw [thinSpan] at hv
    induction hv using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        change adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ (i : ℕ) ∈ thinSpan G x r d w₀
        have hi : (i : ℕ) ≤ d := Nat.lt_succ_iff.1 i.isLt
        by_cases hi0 : (i : ℕ) = 0
        · rw [hi0, adj_mulVec_thinVec_zero hD hstable hend ha hw₀]
          refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ (hgen 0 (Nat.succ_pos d)))
          by_cases hd0 : d = 0
          · rw [thinVec_eq_zero_of_lt hstable hdiam hw₀ (by omega)]
            exact Submodule.zero_mem _
          · exact hgen 1 (by omega)
        · rw [adj_mulVec_thinVec_succ hD hstable hend ha hx hdiam hw₀ (by omega) hi]
          refine Submodule.add_mem _ (Submodule.add_mem _ ?_
            (Submodule.smul_mem _ _ (hgen (i : ℕ) (by omega))))
            (Submodule.smul_mem _ _ (hgen ((i : ℕ) - 1) (by omega)))
          by_cases hid : (i : ℕ) = d
          · rw [hid, thinVec_eq_zero_of_lt hstable hdiam hw₀ (by omega)]
            exact Submodule.zero_mem _
          · exact hgen ((i : ℕ) + 1) (by omega)
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  have hEU : ∀ (k : ℕ) (v : X → ℂ), v ∈ thinSpan G x r d w₀ →
      subconst (𝕜 := ℂ) G x k *ᵥ v ∈ thinSpan G x r d w₀ := by
    intro k v hv
    rw [thinSpan] at hv
    induction hv using Submodule.span_induction with
    | mem u hu =>
        obtain ⟨i, rfl⟩ := hu
        change subconst (𝕜 := ℂ) G x k *ᵥ thinVec G x r w₀ (i : ℕ) ∈ thinSpan G x r d w₀
        rw [subconst_mulVec_thinVec]
        by_cases hki : k = r + (i : ℕ)
        · rw [if_pos hki]
          exact hgen (i : ℕ) i.isLt
        · rw [if_neg hki]
          exact Submodule.zero_mem _
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c ha
  exact isStable_of_generators hAU hEU

/-- The span of `w₀, …, w_d` is all of `W`. -/
theorem thinSpan_eq_top
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hend : IsEndpoint (𝕜 := ℂ) G x W r) (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    (ha : HasThinA G x W r a) (hx : HasThinX G x W r xs) {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    thinSpan G x r d w₀ = W :=
  hirr.2 _ (thinSpan_le (d := d) hstable hw₀)
    (thinSpan_stable hstable hend hdiam ha hx hD hw₀)
    (thinSpan_ne_bot (d := d) hstable hw₀ hw₀ne)

/-! ## Lemma 9.2 (iii): the thin module structure -/

/-- `wᵢ = E*_{r+i}(x) A w_{i-1}`. -/
theorem thinVec_succ_eq {D : ℕ} (hD : ∀ y, G.dist x y ≤ D)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d)
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i : ℕ} (hi : 1 ≤ i) (hid : i ≤ d) :
    thinVec G x r w₀ i
      = subconst (𝕜 := ℂ) G x (r + i) *ᵥ (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ (i - 1)) := by
  have hpow : adj (𝕜 := ℂ) G ^ i = adj (𝕜 := ℂ) G * adj (𝕜 := ℂ) G ^ (i - 1) := by
    have h := pow_succ' (adj (𝕜 := ℂ) G) (i - 1)
    rwa [Nat.sub_add_cancel hi] at h
  rw [thinVec, hpow, ← Matrix.mulVec_mulVec]
  exact subconst_mulVec_adj_eq (W := W) hD hw₀ (i := i - 1) (j := r + i) (by omega)
    (le_of_diam hD hdiam (by omega))

/-- **Lemma 9.2 (iii), (iiib).**  For `0 ≠ w₀ ∈ E*_{r}(x)W` the vectors
`wᵢ = E*_{r+i}(x) Aⁱ w₀` are nonzero for `i ≤ d`, lie in `E*_{r+i}(x)W`, vanish
for `i > d`, span `W`, and `A` acts tridiagonally. -/
theorem thin_module_structure {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    {r d : ℕ} {a xs : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) {w₀ : X → ℂ}
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    (∀ i, i ≤ d → thinVec G x r w₀ i ≠ 0) ∧
    (∀ i, thinVec G x r w₀ i ∈ subconstImage (𝕜 := ℂ) G x (r + i) W) ∧
    (∀ i, d < i → thinVec G x r w₀ i = 0) ∧
    (∀ v ∈ W, ∃ c : ℕ → ℂ,
      v = ∑ i ∈ Finset.range (d + 1), c i • thinVec G x r w₀ i) ∧
    (adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ 0
      = thinVec G x r w₀ 1 + a 0 • thinVec G x r w₀ 0) ∧
    (∀ i, 1 ≤ i → i ≤ d → adj (𝕜 := ℂ) G *ᵥ thinVec G x r w₀ i
      = thinVec G x r w₀ (i + 1) + a i • thinVec G x r w₀ i
        + xs i • thinVec G x r w₀ (i - 1)) := by
  set D : ℕ := Finset.univ.sup (fun y : X => G.dist x y) with hDdef
  have hD : ∀ y, G.dist x y ≤ D := fun y => Finset.le_sup (Finset.mem_univ y)
  refine ⟨thinVec_ne_zero hstable hirr hthin hend hdiam hD hw₀ hw₀ne,
    fun i => thinVec_mem (r := r) hstable hw₀ i,
    fun i hi => thinVec_eq_zero_of_lt hstable hdiam hw₀ hi, ?_,
    adj_mulVec_thinVec_zero hD hstable hend ha hw₀,
    fun i hi hid => adj_mulVec_thinVec_succ hD hstable hend ha hx hdiam hw₀ hi hid⟩
  intro v hv
  have hvU : v ∈ thinSpan G x r d w₀ := by
    rw [thinSpan_eq_top hstable hirr hend hdiam ha hx hD hw₀ hw₀ne]
    exact hv
  rw [thinSpan] at hvU
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hvU
  set cc : ℕ → ℂ := fun k => if h : k < d + 1 then c ⟨k, h⟩ else 0 with hcc
  refine ⟨cc, ?_⟩
  rw [← hc, ← Fin.sum_univ_eq_sum_range (fun k => cc k • thinVec G x r w₀ k) (d + 1)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hcc]
  simp only [dif_pos i.isLt]

/-- **Lemma 9.2 (iv).**  `pᵢ(A) w₀ = wᵢ`. -/
theorem thinPoly_aeval {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    {r d : ℕ} {a xs : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) {w₀ : X → ℂ}
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    ∀ i, i ≤ d + 1 →
      (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs i) *ᵥ w₀
        = thinVec G x r w₀ i := by
  set D : ℕ := Finset.univ.sup (fun y : X => G.dist x y) with hDdef
  have hD : ∀ y, G.dist x y ≤ D := fun y => Finset.le_sup (Finset.mem_univ y)
  have hw0 : thinVec G x r w₀ 0 = w₀ := by
    simp only [thinVec, Nat.add_zero, pow_zero, Matrix.one_mulVec]
    exact subconst_mulVec_self hw₀
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i with
    | 0 =>
        rw [thinPoly, Polynomial.aeval_one, Matrix.one_mulVec, hw0]
    | 1 =>
        have h1 : (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs 1)
            = adj (𝕜 := ℂ) G - a 0 • 1 := by
          simp only [thinPoly, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            Algebra.algebraMap_eq_smul_one]
        have hz := adj_mulVec_thinVec_zero hD hstable hend ha hw₀
        rw [hw0] at hz
        rw [h1, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hz]
        abel
    | (k + 2) =>
        have hk1 : k + 1 ≤ d := by omega
        have hk2 : k + 1 ≤ d + 1 := by omega
        have hk0 : k ≤ d + 1 := by omega
        have ih1 := ih (k + 1) (by omega) hk2
        have ih0 := ih k (by omega) hk0
        have hfac : thinPoly a xs (k + 2)
            = (Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)
              - Polynomial.C (xs (k + 1)) * thinPoly a xs k := by
          rw [thinPoly, sub_mul]
        have hA : (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs (k + 2))
            = (adj (𝕜 := ℂ) G - a (k + 1) • 1) *
                (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs (k + 1))
              - xs (k + 1) • (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs k) := by
          rw [hfac]
          simp only [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C,
            Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, Matrix.one_mul]
        rw [hA, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
          Matrix.smul_mulVec, Matrix.one_mulVec, ih1, Matrix.smul_mulVec, ih0,
          adj_mulVec_thinVec_succ hD hstable hend ha hx hdiam hw₀
            (show 1 ≤ k + 1 by omega) hk1]
        rw [show k + 1 - 1 = k from by omega, sub_sub, add_assoc, add_sub_cancel_right]

/-! ## Lemma 9.2 (i), (ii): the thin parameters are real -/

/-- `⟪u,u⟫` is the real number `‖u‖²`. -/
theorem star_dotProduct_self_eq_ofReal (u : X → ℂ) :
    star u ⬝ᵥ u = ((vnorm u * vnorm u : ℝ) : ℂ) := by
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 (star_dotProduct_self_real u)
  have hre := star_dotProduct_self_re u
  rw [hr] at hre ⊢
  rw [Complex.ofReal_re] at hre
  rw [hre]

/-- The Hermitian norm of a nonzero vector is positive. -/
theorem vnorm_pos {u : X → ℂ} (hu : u ≠ 0) : 0 < vnorm u := by
  have hne : vnorm u ≠ 0 := by
    intro h0
    refine hu (star_dotProduct_self_eq_zero ?_)
    rw [star_dotProduct_self_eq_ofReal, h0, mul_zero, Complex.ofReal_zero]
  exact lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hne)

/-- `(E*_j A)*(E*_j A) = A E*_j A`. -/
theorem star_mul_adj_subconst_mul (j : ℕ) :
    star (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G) *
        (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G)
      = adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G := by
  rw [star_mul, star_adj, star_subconst,
    Matrix.mul_assoc (adj (𝕜 := ℂ) G) (subconst (𝕜 := ℂ) G x j)
      (subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G),
    ← Matrix.mul_assoc (subconst (𝕜 := ℂ) G x j) (subconst (𝕜 := ℂ) G x j) (adj (𝕜 := ℂ) G),
    subconst_mul_self, Matrix.mul_assoc]

/-- `⟪E*_j A v, E*_j A v⟫ = ⟪v, (A E*_j A) v⟫`. -/
theorem star_mulVec_adj_subconst_self (v : X → ℂ) (j : ℕ) :
    star (subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ v)) ⬝ᵥ
        (subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ v))
      = star v ⬝ᵥ ((adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G) *ᵥ v) := by
  set N : Matrix X X ℂ := subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G with hN
  have hsN : star N * N = adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G := by
    rw [hN]
    exact star_mul_adj_subconst_mul j
  have h1 : subconst (𝕜 := ℂ) G x j *ᵥ (adj (𝕜 := ℂ) G *ᵥ v) = N *ᵥ v := by
    rw [hN, Matrix.mulVec_mulVec]
  rw [h1]
  calc star (N *ᵥ v) ⬝ᵥ (N *ᵥ v)
      = star (star N *ᵥ (N *ᵥ v)) ⬝ᵥ v := by rw [star_mulVec_dotProduct]
    _ = star ((star N * N) *ᵥ v) ⬝ᵥ v := by rw [Matrix.mulVec_mulVec]
    _ = star v ⬝ᵥ ((star N * N) *ᵥ v) := by
        rw [selfAdj_star_dotProduct (a := star N * N) (by rw [star_mul, star_star])]
    _ = star v ⬝ᵥ ((adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x j * adj (𝕜 := ℂ) G) *ᵥ v) := by
        rw [hsN]

/-- A vector of a subconstituent can be inserted into the first slot of the pairing. -/
theorem star_dotProduct_subconst_eq (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    {j : ℕ} {v : X → ℂ} (hv : v ∈ subconstImage (𝕜 := ℂ) G x j W) (z : X → ℂ) :
    star v ⬝ᵥ z = star v ⬝ᵥ (subconst (𝕜 := ℂ) G x j *ᵥ z) := by
  calc star v ⬝ᵥ z = star (subconst (𝕜 := ℂ) G x j *ᵥ v) ⬝ᵥ z := by
        rw [subconst_mulVec_self hv]
    _ = star v ⬝ᵥ (subconst (𝕜 := ℂ) G x j *ᵥ z) := by
        rw [selfAdj_star_dotProduct (star_subconst (𝕜 := ℂ) G x j)]

/-- The scalar `aᵢ` is real, given that `wᵢ` does not vanish. -/
theorem thinA_eq_star (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (ha : HasThinA G x W r a) (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) {i : ℕ}
    (hne : thinVec G x r w₀ i ≠ 0) : a i = star (a i) := by
  set w : X → ℂ := thinVec G x r w₀ i with hw
  have hmem : w ∈ subconstImage (𝕜 := ℂ) G x (r + i) W := thinVec_mem (r := r) hstable hw₀ i
  have hMw : (subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G *
      subconst (𝕜 := ℂ) G x (r + i)) *ᵥ w = a i • w := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, subconst_mulVec_self hmem]
    exact ha i _ hmem
  have hself : star (subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G *
        subconst (𝕜 := ℂ) G x (r + i))
      = subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x (r + i) := by
    simp only [star_mul, star_adj, star_subconst]
    rw [Matrix.mul_assoc]
  have hreal : a i * (star w ⬝ᵥ w) = star (a i) * (star w ⬝ᵥ w) := by
    calc a i * (star w ⬝ᵥ w) = star w ⬝ᵥ (a i • w) := by
          rw [dotProduct_smul, smul_eq_mul]
      _ = star w ⬝ᵥ ((subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G *
            subconst (𝕜 := ℂ) G x (r + i)) *ᵥ w) := by rw [hMw]
      _ = star ((subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G *
            subconst (𝕜 := ℂ) G x (r + i)) *ᵥ w) ⬝ᵥ w := by
          rw [selfAdj_star_dotProduct hself]
      _ = star (a i • w) ⬝ᵥ w := by rw [hMw]
      _ = star (a i) * (star w ⬝ᵥ w) := by rw [star_smul, smul_dotProduct, smul_eq_mul]
  have hz : star w ⬝ᵥ w ≠ 0 := fun h0 => hne (star_dotProduct_self_eq_zero h0)
  have h1 : (a i - star (a i)) * (star w ⬝ᵥ w) = 0 := by
    rw [sub_mul, hreal, sub_self]
  rcases mul_eq_zero.1 h1 with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hz

/-- `⟪wᵢ,wᵢ⟫ = xᵢ ⟪w_{i-1},w_{i-1}⟫`. -/
theorem thinX_eq (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hx : HasThinX G x W r xs) (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) {D : ℕ}
    (hD : ∀ y, G.dist x y ≤ D) (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W)
    {i : ℕ} (hi : 1 ≤ i) (hid : i ≤ d) :
    star (thinVec G x r w₀ i) ⬝ᵥ thinVec G x r w₀ i
      = xs i * (star (thinVec G x r w₀ (i - 1)) ⬝ᵥ thinVec G x r w₀ (i - 1)) := by
  have hidx : r + (i - 1) = r + i - 1 := by omega
  have hmem_p : thinVec G x r w₀ (i - 1) ∈ subconstImage (𝕜 := ℂ) G x (r + i - 1) W := by
    rw [← hidx]
    exact thinVec_mem (r := r) hstable hw₀ (i - 1)
  set v : X → ℂ := thinVec G x r w₀ (i - 1) with hv
  have hwi : thinVec G x r w₀ i = subconst (𝕜 := ℂ) G x (r + i) *ᵥ (adj (𝕜 := ℂ) G *ᵥ v) := by
    rw [hv]
    exact thinVec_succ_eq hD hdiam hw₀ hi hid
  have hX := hx i v hi hmem_p
  have h2 : subconst (𝕜 := ℂ) G x (r + i - 1) *ᵥ
      ((adj (𝕜 := ℂ) G * subconst (𝕜 := ℂ) G x (r + i) * adj (𝕜 := ℂ) G) *ᵥ v)
      = xs i • v := by
    rw [← hX]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hwi, star_mulVec_adj_subconst_self,
    star_dotProduct_subconst_eq (W := W) hstable hmem_p, h2, dotProduct_smul, smul_eq_mul]

theorem thin_parameters_real {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    {r d : ℕ} {a xs : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) {w₀ : X → ℂ}
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    (∀ i, i ≤ d → ∃ c : ℝ, a i = (c : ℂ)) ∧
    (∀ i, 1 ≤ i → i ≤ d → ∃ c : ℝ, 0 < c ∧ xs i = (c : ℂ)) := by
  set D : ℕ := Finset.univ.sup (fun y : X => G.dist x y) with hDdef
  have hD : ∀ y, G.dist x y ≤ D := fun y => Finset.le_sup (Finset.mem_univ y)
  have hne := thinVec_ne_zero hstable hirr hthin hend hdiam hD hw₀ hw₀ne
  constructor
  · intro i hi
    have hconj : a i = star (a i) := thinA_eq_star hstable ha hw₀ (hne i hi)
    exact Complex.conj_eq_iff_real.1 hconj.symm
  · intro i hi hid
    have hkey := thinX_eq hstable hx hdiam hD hw₀ hi hid
    have hwi : thinVec G x r w₀ i ≠ 0 := hne i hid
    have hwp : thinVec G x r w₀ (i - 1) ≠ 0 := hne (i - 1) (by omega)
    have hni : 0 < vnorm (thinVec G x r w₀ i) := vnorm_pos hwi
    have hnp : 0 < vnorm (thinVec G x r w₀ (i - 1)) := vnorm_pos hwp
    have hni' : (vnorm (thinVec G x r w₀ i) * vnorm (thinVec G x r w₀ i) : ℝ) ≠ 0 := by
      have := mul_pos hni hni
      positivity
    have hnp' : (vnorm (thinVec G x r w₀ (i - 1)) *
        vnorm (thinVec G x r w₀ (i - 1)) : ℝ) ≠ 0 := by
      have := mul_pos hnp hnp
      positivity
    have hkey' : ((vnorm (thinVec G x r w₀ i) * vnorm (thinVec G x r w₀ i) : ℝ) : ℂ)
        = xs i * ((vnorm (thinVec G x r w₀ (i - 1)) *
            vnorm (thinVec G x r w₀ (i - 1)) : ℝ) : ℂ) := by
      rw [star_dotProduct_self_eq_ofReal, star_dotProduct_self_eq_ofReal] at hkey
      exact hkey
    have hrepr : xs i = ((vnorm (thinVec G x r w₀ i) * vnorm (thinVec G x r w₀ i) : ℝ) : ℂ)
        / ((vnorm (thinVec G x r w₀ (i - 1)) *
            vnorm (thinVec G x r w₀ (i - 1)) : ℝ) : ℂ) := by
      rw [eq_div_iff]
      · exact hkey'.symm
      · simp only [Complex.ofReal_ne_zero]
        exact hnp'
    refine ⟨vnorm (thinVec G x r w₀ i) * vnorm (thinVec G x r w₀ i) /
      (vnorm (thinVec G x r w₀ (i - 1)) * vnorm (thinVec G x r w₀ (i - 1))), ?_, ?_⟩
    · positivity
    · rw [hrepr, Complex.ofReal_div]

/-! ## Lemma `measure-wi`: `‖wᵢ‖² = x₁⋯xᵢ ‖w₀‖²` -/

/-- **Lemma `measure-wi`** (lecture 9).  The squared norms of the basis vectors `wᵢ`
of a thin module grow by the factors `xᵢ`. -/
theorem thin_measure_wi {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    {r d : ℕ} {a xs : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) {w₀ : X → ℂ}
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    ∀ i, i ≤ d → star (thinVec G x r w₀ i) ⬝ᵥ (thinVec G x r w₀ i)
      = (∏ l ∈ Finset.Icc 1 i, xs l) * (star w₀ ⬝ᵥ w₀) := by
  set D : ℕ := Finset.univ.sup (fun y : X => G.dist x y) with hDdef
  have hD : ∀ y, G.dist x y ≤ D := fun y => Finset.le_sup (Finset.mem_univ y)
  intro i
  induction i with
  | zero =>
      intro _
      have h0 : thinVec G x r w₀ 0 = w₀ := by
        simp only [thinVec, Nat.add_zero, pow_zero, Matrix.one_mulVec]
        exact subconst_mulVec_self hw₀
      rw [h0]
      simp
  | succ i ih =>
      intro hi
      have hi' : i ≤ d := by omega
      have hstep := thinX_eq (W := W) hstable hx hdiam hD hw₀ (i := i + 1) (by omega) (by omega)
      rw [Nat.add_sub_cancel] at hstep
      rw [hstep, ih hi', Finset.prod_Icc_succ_top (by omega)]
      ring

/-! ## The polynomials `pᵢ` have real coefficients -/

/-- `pᵢ` is invariant under the coefficientwise conjugation, for `i ≤ d`. -/
theorem thinPoly_map_star {a xs : ℕ → ℂ} {d : ℕ}
    (ha : ∀ i, i ≤ d → (starRingEnd ℂ) (a i) = a i)
    (hxs : ∀ i, 1 ≤ i → i ≤ d → (starRingEnd ℂ) (xs i) = xs i) :
    ∀ i, i ≤ d → (thinPoly a xs i).map (starRingEnd ℂ) = thinPoly a xs i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    match i with
    | 0 => simp [thinPoly]
    | 1 =>
        simp only [thinPoly, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, ha 0 (by omega)]
    | (k + 2) =>
        have hfac : thinPoly a xs (k + 2)
            = (Polynomial.X - Polynomial.C (a (k + 1))) * thinPoly a xs (k + 1)
              - Polynomial.C (xs (k + 1)) * thinPoly a xs k := by
          rw [thinPoly, sub_mul]
        rw [hfac, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
          Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.map_C,
          ih (k + 1) (by omega) (by omega), ih k (by omega) (by omega),
          ha (k + 1) (by omega), hxs (k + 1) (by omega) (by omega)]

/-! ## Pairing and spectral-projection bookkeeping -/

/-- `⟨M x, y⟩ = ⟨x, M* y⟩` for the Hermitian form. -/
theorem star_mulVec_dotProduct_swap (M : Matrix X X ℂ) (x y : X → ℂ) :
    star (M *ᵥ x) ⬝ᵥ y = star x ⬝ᵥ (star M *ᵥ y) := by
  rw [← star_dotProduct_symm y (M *ᵥ x), star_mulVec_dotProduct]
  exact star_dotProduct_symm _ _

/-- Splitting a vector along the spectral projections. -/
theorem eq_sum_spectralProj_mulVec {A : Matrix X X ℂ} (hA : star A = A) (v : X → ℂ) :
    v = ∑ θ ∈ eigFinset A, spectralProj A θ *ᵥ v := by
  conv_lhs => rw [← Matrix.one_mulVec v, ← sum_spectralProj hA]
  rw [Matrix.sum_mulVec]

/-- The spectral projections act on the standard module as scalar multiples of the
polynomials evaluated at the eigenvalue. -/
theorem aeval_mulVec_spectralProj_mulVec {A : Matrix X X ℂ} (hA : star A = A)
    (q : Polynomial ℂ) {θ : ℂ} (hθ : θ ∈ eigFinset A) (v : X → ℂ) :
    (Polynomial.aeval A) q *ᵥ (spectralProj A θ *ᵥ v)
      = (q.eval θ) • (spectralProj A θ *ᵥ v) := by
  rw [Matrix.mulVec_mulVec, aeval_mul_spectralProj hA q hθ, Matrix.smul_mulVec]

/-- **Lemma 10.1 (orthogonality), restated.**  The polynomials `pᵢ` are orthogonal with
respect to the spectral measure of `w₀`: with `m(θ) = ‖E_θ w₀‖²/‖w₀‖²`,
`∑_θ pᵢ(θ)pⱼ(θ)m(θ) = δᵢⱼ x₁⋯xᵢ`. -/
theorem thin_orthogonality {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    {r d : ℕ} {a xs : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA G x W r a)
    (hx : HasThinX G x W r xs) {w₀ : X → ℂ}
    (hw₀ : w₀ ∈ subconstImage (𝕜 := ℂ) G x r W) (hw₀ne : w₀ ≠ 0) :
    ∀ i j, i ≤ d → j ≤ d →
      (∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
          (thinPoly a xs i).eval θ * (thinPoly a xs j).eval θ
            * ((star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)
                  ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀))
                / (star w₀ ⬝ᵥ w₀)))
        = if i = j then (∏ l ∈ Finset.Icc 1 i, xs l) else 0 := by
  have hAsa : star (adj (𝕜 := ℂ) G) = adj (𝕜 := ℂ) G := star_adj G
  obtain ⟨haR, hxsR⟩ :=
    thin_parameters_real (G := G) (x := x) (W := W) (r := r) (d := d) (a := a) (xs := xs)
      hstable hirr hthin hend hdiam ha hx hw₀ hw₀ne
  have ha' : ∀ i, i ≤ d → (starRingEnd ℂ) (a i) = a i := by
    intro i hi
    obtain ⟨c, hc⟩ := haR i hi
    rw [hc]; simp
  have hxs' : ∀ i, 1 ≤ i → i ≤ d → (starRingEnd ℂ) (xs i) = xs i := by
    intro i h1 hi
    obtain ⟨c, _, hc⟩ := hxsR i h1 hi
    rw [hc]; simp
  have hd0 : star w₀ ⬝ᵥ w₀ ≠ 0 := fun h => hw₀ne (star_dotProduct_self_eq_zero h)
  intro i j hi hj
  have hPi : thinVec G x r w₀ i
      = (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs i) *ᵥ w₀ :=
    (thinPoly_aeval hstable hirr hthin hend hdiam ha hx hw₀ hw₀ne i (by omega)).symm
  have hPj : thinVec G x r w₀ j
      = (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs j) *ᵥ w₀ :=
    (thinPoly_aeval hstable hirr hthin hend hdiam ha hx hw₀ hw₀ne j (by omega)).symm
  have hstarP : star ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs j))
      = (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs j) := by
    rw [star_aeval hAsa, thinPoly_map_star ha' hxs' j hj]
  -- the pairing equals the weighted sum of the squared projections
  have hexp : (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs j) *ᵥ
      ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs i) *ᵥ w₀)
      = ∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
          ((thinPoly a xs i).eval θ * (thinPoly a xs j).eval θ) •
            (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀) := by
    have h1 : (Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a xs i) *ᵥ w₀
        = ∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
            ((thinPoly a xs i).eval θ) • (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀) := by
      conv_lhs => rw [eq_sum_spectralProj_mulVec hAsa w₀]
      rw [Matrix.mulVec_sum]
      exact Finset.sum_congr rfl
        (fun θ hθ => aeval_mulVec_spectralProj_mulVec hAsa _ hθ w₀)
    rw [h1, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl (fun θ hθ => ?_)
    rw [Matrix.mulVec_smul, aeval_mulVec_spectralProj_mulVec hAsa _ hθ w₀, smul_smul]
  have hmain : star (thinVec G x r w₀ j) ⬝ᵥ (thinVec G x r w₀ i)
      = ∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
          (thinPoly a xs i).eval θ * (thinPoly a xs j).eval θ
            * (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)
                ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)) := by
    rw [hPj, hPi, star_mulVec_dotProduct_swap, hstarP, hexp, dotProduct_sum]
    refine Finset.sum_congr rfl (fun θ hθ => ?_)
    rw [dotProduct_smul, smul_eq_mul]
    congr 1
    rw [star_mulVec_dotProduct_swap, star_spectralProj hAsa hθ, Matrix.mulVec_mulVec,
      spectralProj_mul_self hAsa hθ]
  -- the pairing of two thin vectors
  have hpair : star (thinVec G x r w₀ j) ⬝ᵥ (thinVec G x r w₀ i)
      = if i = j then (∏ l ∈ Finset.Icc 1 i, xs l) * (star w₀ ⬝ᵥ w₀) else 0 := by
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      exact thin_measure_wi hstable hirr hthin hend hdiam ha hx hw₀ hw₀ne i hi
    · rw [if_neg hij]
      exact star_dotProduct_subconstImage_zero (W := W) (W' := W) (by omega)
        (thinVec_mem (r := r) hstable hw₀ j) (thinVec_mem (r := r) hstable hw₀ i)
  have hsum_div : (∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
        (thinPoly a xs i).eval θ * (thinPoly a xs j).eval θ
          * ((star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)
                ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)) / (star w₀ ⬝ᵥ w₀)))
      = (∑ θ ∈ eigFinset (adj (𝕜 := ℂ) G),
          (thinPoly a xs i).eval θ * (thinPoly a xs j).eval θ
            * (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀)
                ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w₀))) / (star w₀ ⬝ᵥ w₀) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl (fun θ _ => by ring)
  rw [hsum_div, ← hmain, hpair]
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, mul_div_cancel_right₀ _ hd0]
  · rw [if_neg hij, if_neg hij, zero_div]

end Terwilliger
