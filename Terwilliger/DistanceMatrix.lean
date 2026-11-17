/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.DistanceRegular

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
# The distance matrices `Aᵢ` (Chapter 16)

For a graph `Γ = (X, E)`, the `i`-th *distance matrix* `Aᵢ` has `(x,y)`-entry `1`
when `∂(x,y) = i` and `0` otherwise.  The notes observe

* `A₀ = I`, `A₁ = A`, `A₀ + ⋯ + A_D = J`,
* and, when `Γ` is distance-regular,
  `A Aᵢ = c_{i+1}A_{i+1} + aᵢAᵢ + b_{i-1}A_{i-1}` (Lemma 16.2 (i)),
  whence `Aᵢ = pᵢ(A)/(c₁⋯cᵢ)` and the `Aᵢ` form a basis of the Bose–Mesner
  algebra (Lemma 16.2 (ii), (iii)).
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **Definition 16.1.** The `i`-th distance matrix. -/
def distMatrix (G : SimpleGraph X) (i : ℕ) : Matrix X X 𝕜 :=
  fun x y => if G.dist x y = i then 1 else 0

@[simp]
theorem distMatrix_apply (G : SimpleGraph X) (i : ℕ) (x y : X) :
    distMatrix (𝕜 := 𝕜) G i x y = if G.dist x y = i then 1 else 0 := rfl

/-- The distance matrices are symmetric. -/
theorem distMatrix_transpose (G : SimpleGraph X) (i : ℕ) :
    (distMatrix (𝕜 := 𝕜) G i)ᵀ = distMatrix G i := by
  ext x y
  simp only [Matrix.transpose_apply, distMatrix_apply, SimpleGraph.dist_comm]

/-- The distance matrices are self-adjoint. -/
theorem star_distMatrix (G : SimpleGraph X) (i : ℕ) :
    star (distMatrix (𝕜 := 𝕜) G i) = distMatrix G i := by
  ext x y
  simp only [Matrix.star_apply, distMatrix_apply]
  by_cases h : G.dist x y = i <;> simp [h, SimpleGraph.dist_comm]

/-- `A₀ = I`. -/
theorem distMatrix_zero (G : SimpleGraph X) (hG : G.Connected) :
    distMatrix (𝕜 := 𝕜) G 0 = 1 := by
  ext x y
  rw [distMatrix_apply, Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · rw [if_neg h, if_neg]
    exact fun hd => h ((G.dist_eq_zero_iff_eq_or_not_reachable).mp hd |>.resolve_right (fun hr => hr (hG x y)))

/-- `A₁ = A`. -/
theorem distMatrix_one (G : SimpleGraph X) :
    distMatrix (𝕜 := 𝕜) G 1 = adj G := by
  ext x y
  rw [distMatrix_apply, adj_apply]
  by_cases h : G.Adj x y
  · rw [if_pos (SimpleGraph.dist_eq_one_iff_adj.mpr h), if_pos h]
  · rw [if_neg (fun hd => h (SimpleGraph.dist_eq_one_iff_adj.mp hd)), if_neg h]

/-- The all-ones matrix. -/
def allOnes : Matrix X X 𝕜 := fun _ _ => 1

@[simp]
theorem allOnes_apply (x y : X) : allOnes (𝕜 := 𝕜) x y = 1 := rfl

/-- `A₀ + ⋯ + A_D = J`. -/
theorem sum_distMatrix (G : SimpleGraph X) (D : ℕ) (hD : ∀ x y, G.dist x y ≤ D) :
    ∑ i ∈ Finset.range (D + 1), distMatrix (𝕜 := 𝕜) G i = allOnes := by
  ext x y
  rw [Matrix.sum_apply, allOnes_apply]
  rw [Finset.sum_eq_single (G.dist x y)]
  · simp
  · intro b _ hb
    rw [distMatrix_apply]
    simp [Ne.symm hb]
  · intro h
    simp only [Finset.mem_range, not_lt] at h
    exact absurd (hD x y) (not_le.mpr h)

/-- The common value of `cᵢ` on the `i`-th sphere around `x`, as in
`Terwilliger.sphereConst`: the coefficient `cᵢ` of a distance-regular graph. -/
def cval (G : SimpleGraph X) (x : X) (i : ℕ) : ℕ := sphereConst G x i (fun y => cnum G x y i)

/-- The coefficient `aᵢ`. -/
def aval (G : SimpleGraph X) (x : X) (i : ℕ) : ℕ := sphereConst G x i (fun y => anum G x y i)

/-- The coefficient `bᵢ`. -/
def bval (G : SimpleGraph X) (x : X) (i : ℕ) : ℕ := sphereConst G x i (fun y => bnum G x y i)

/-! ## Lemma 16.2: the distance matrices and the base vertex

`A * Aᵢ` counts, in its `(a,b)`-entry, the neighbours of `a` in the `i`-th sphere
around `b`; the three intersection numbers therefore enter with the *second*
index of the entry as base vertex.  The statements of Lemma 16.2 in this file use
a single base vertex `x`, so they hold exactly when the intersection numbers do
not depend on the base vertex --- which is Theorem 13.x of the notes for a
distance-regular graph.  Below: the pointwise form, valid for every
distance-regular graph, and the global forms under that hypothesis. -/

/-- `bᵢ(x,y) = aᵢ₊₁(x,y)`: the two counts differ only by a shift of the index. -/
theorem bnum_eq_anum {G : SimpleGraph X} (x y : X) {i : ℕ} (hi : 1 ≤ i) :
    bnum G x y (i - 1) = anum G x y i := by
  rw [bnum, anum, Nat.sub_add_cancel hi]

/-- `cᵢ₊₁(x,y) = aᵢ(x,y)`. -/
theorem cnum_eq_anum {G : SimpleGraph X} (x y : X) (i : ℕ) :
    cnum G x y (i + 1) = anum G x y i := by
  rw [cnum, anum]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

/-- `bᵢ` evaluated at a vertex of the `i`-th sphere around `x`. -/
theorem bval_eq_bnum {G : SimpleGraph X} {x z : X} {j : ℕ} (hdr : IsDistanceRegularAt G x)
    (hz : G.dist x z = j) : bval G x j = bnum G x z j :=
  sphereConst_bnum hdr hz

/-- `aᵢ` evaluated at a vertex of the `i`-th sphere around `x`. -/
theorem aval_eq_anum {G : SimpleGraph X} {x z : X} {j : ℕ} (hdr : IsDistanceRegularAt G x)
    (hz : G.dist x z = j) : aval G x j = anum G x z j :=
  sphereConst_anum hdr hz

/-- `cᵢ` evaluated at a vertex of the `i`-th sphere around `x`. -/
theorem cval_eq_cnum {G : SimpleGraph X} {x z : X} {j : ℕ} (hdr : IsDistanceRegularAt G x)
    (hz : G.dist x z = j) : cval G x j = cnum G x z j :=
  sphereConst_cnum hdr hz

/-- **Lemma 16.2 (i), pointwise form.**  The `(a,b)`-entry of `A Aᵢ` is the number
of neighbours of `a` in the `i`-th sphere around `b`, expressed through the
intersection numbers based at `b`.  No hypothesis beyond distance-regularity. -/
theorem adj_mul_distMatrix_apply {G : SimpleGraph X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) {i : ℕ} (hi : 1 ≤ i) (a b : X) :
    (adj (𝕜 := 𝕜) G * distMatrix (𝕜 := 𝕜) G i) a b
      = (if G.dist a b = i - 1 then (bval G b (i - 1) : 𝕜) else 0)
        + (if G.dist a b = i then (aval G b i : 𝕜) else 0)
        + (if G.dist a b = i + 1 then (cval G b (i + 1) : 𝕜) else 0) := by
  have hterm : ∀ z : X, adj (𝕜 := 𝕜) G a z * distMatrix (𝕜 := 𝕜) G i z b
      = if G.Adj a z ∧ G.dist b z = i then (1 : 𝕜) else 0 := by
    intro z
    rw [adj_apply, distMatrix_apply, SimpleGraph.dist_comm (v := b)]
    by_cases h1 : G.Adj a z <;> by_cases h2 : G.dist b z = i <;> simp [h1, h2]
  have hcard : (adj (𝕜 := 𝕜) G * distMatrix (𝕜 := 𝕜) G i) a b
      = ((Finset.univ.filter fun z => G.Adj a z ∧ G.dist b z = i).card : 𝕜) := by
    rw [Matrix.mul_apply]
    simp only [hterm, Finset.sum_boole]
  rw [hcard]
  by_cases h1 : G.dist a b = i - 1
  · have h2 : G.dist a b ≠ i := by omega
    have h3 : G.dist a b ≠ i + 1 := by omega
    have h1' : G.dist b a = i - 1 := by rw [SimpleGraph.dist_comm]; exact h1
    rw [if_pos h1, if_neg h2, if_neg h3, filter_card_eq_bnum (x := b) (z := a) hi,
      bval_eq_bnum (hdr b) h1']
    simp
  · by_cases h2 : G.dist a b = i
    · have h3 : G.dist a b ≠ i + 1 := by omega
      have h2' : G.dist b a = i := by rw [SimpleGraph.dist_comm]; exact h2
      rw [if_neg h1, if_pos h2, if_neg h3, filter_card_eq_bnum (x := b) (z := a) hi,
        bnum_eq_anum b a hi, aval_eq_anum (hdr b) h2']
      simp
    · by_cases h3 : G.dist a b = i + 1
      · have h3' : G.dist b a = i + 1 := by rw [SimpleGraph.dist_comm]; exact h3
        rw [if_neg h1, if_neg h2, if_pos h3, filter_card_eq_bnum (x := b) (z := a) hi,
          bnum_eq_anum b a hi, cval_eq_cnum (hdr b) h3', cnum_eq_anum b a i]
        simp
      · have h1' : G.dist b a ≠ i - 1 := by rw [SimpleGraph.dist_comm]; omega
        have h2' : G.dist b a ≠ i := by rw [SimpleGraph.dist_comm]; omega
        have h3' : G.dist b a ≠ i + 1 := by rw [SimpleGraph.dist_comm]; omega
        rw [if_neg h1, if_neg h2, if_neg h3,
          filter_card_eq_zero (x := b) (z := a) h1' h2' h3']
        simp

/-- The intersection numbers do not depend on the base vertex (Theorem 13.x of the
notes for a distance-regular graph). -/
def IntersectionNumbersIndependent (G : SimpleGraph X) : Prop :=
  ∀ (x x' : X) (j : ℕ),
    bval G x j = bval G x' j ∧ aval G x j = aval G x' j ∧ cval G x j = cval G x' j

/-- **Lemma 16.2 (i).**  For a distance-regular graph whose intersection numbers do
not depend on the base vertex, `A Aᵢ = cᵢ₊₁Aᵢ₊₁ + aᵢAᵢ + bᵢ₋₁Aᵢ₋₁`. -/
theorem adj_mul_distMatrix {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) {i : ℕ}
    (hi : 1 ≤ i) :
    adj (𝕜 := 𝕜) G * distMatrix (𝕜 := 𝕜) G i
      = (bval G x (i - 1) : 𝕜) • distMatrix (𝕜 := 𝕜) G (i - 1)
      + (aval G x i : 𝕜) • distMatrix (𝕜 := 𝕜) G i
      + (cval G x (i + 1) : 𝕜) • distMatrix (𝕜 := 𝕜) G (i + 1) := by
  ext a b
  rw [adj_mul_distMatrix_apply hG hdr hi a b]
  have hR : ((bval G x (i - 1) : 𝕜) • distMatrix (𝕜 := 𝕜) G (i - 1)
      + (aval G x i : 𝕜) • distMatrix (𝕜 := 𝕜) G i
      + (cval G x (i + 1) : 𝕜) • distMatrix (𝕜 := 𝕜) G (i + 1)) a b
      = (if G.dist a b = i - 1 then (bval G b (i - 1) : 𝕜) else 0)
        + (if G.dist a b = i then (aval G b i : 𝕜) else 0)
        + (if G.dist a b = i + 1 then (cval G b (i + 1) : 𝕜) else 0) := by
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, distMatrix_apply]
    by_cases h1 : G.dist a b = i - 1
    · have h2 : ¬ G.dist a b = i := by omega
      have h3 : ¬ G.dist a b = i + 1 := by omega
      simp only [if_pos h1, if_neg h2, if_neg h3, mul_one, mul_zero, add_zero,
        (hbi b x (i - 1)).1]
    · by_cases h2 : G.dist a b = i
      · have h3 : ¬ G.dist a b = i + 1 := by omega
        simp only [if_neg h1, if_pos h2, if_neg h3, mul_one, mul_zero, add_zero, zero_add,
          (hbi b x i).2.1]
      · by_cases h3 : G.dist a b = i + 1
        · simp only [if_neg h1, if_neg h2, if_pos h3, mul_one, mul_zero, add_zero, zero_add,
            (hbi b x (i + 1)).2.2]
        · simp only [if_neg h1, if_neg h2, if_neg h3, mul_zero, add_zero]
  rw [hR]

/-- A vertex at distance `j ≥ 1` has a neighbour at distance `j - 1`; in other
words `cⱼ ≠ 0` at such a vertex. -/
theorem cnum_ne_zero_of_dist {G : SimpleGraph X} (hG : G.Connected) {x y : X} {j : ℕ}
    (hj : 1 ≤ j) (h : G.dist x y = j) : cnum G x y j ≠ 0 := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  have hlen : p.length = j := by rw [hp, h]
  have hadj : G.Adj (p.getVert (j - 1)) y := by
    have h1 : j - 1 < p.length := by omega
    have h2 : G.Adj (p.getVert (j - 1)) (p.getVert (j - 1 + 1)) := p.adj_getVert_succ h1
    have h3 : j - 1 + 1 = p.length := by omega
    rw [h3, SimpleGraph.Walk.getVert_length] at h2
    exact h2
  have hdist : G.dist x (p.getVert (j - 1)) = j - 1 := by
    apply le_antisymm
    · calc G.dist x (p.getVert (j - 1)) ≤ (p.take (j - 1)).length := SimpleGraph.dist_le _
        _ = j - 1 := by
          rw [SimpleGraph.Walk.take_length, hlen, inf_eq_left]
          omega
    · have h4 : G.dist x y ≤ G.dist x (p.getVert (j - 1)) + G.dist (p.getVert (j - 1)) y :=
        hG.dist_triangle
      have h5 : G.dist (p.getVert (j - 1)) y = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hadj
      omega
  intro hzero
  have hmem : p.getVert (j - 1) ∈
      Finset.univ.filter (fun z => G.dist x z + 1 = j ∧ G.Adj y z) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, hadj.symm⟩
  have hpos : 0 < (Finset.univ.filter
      (fun z => G.dist x z + 1 = j ∧ G.Adj y z)).card :=
    Finset.card_pos.mpr ⟨_, hmem⟩
  rw [cnum] at hzero
  omega

/-- If the `j`-th `c`-number vanishes, the `j`-th distance matrix vanishes. -/
theorem distMatrix_eq_zero_of_cval_eq_zero {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) {j : ℕ} (hj : 1 ≤ j)
    (h : cval G x j = 0) : distMatrix (𝕜 := ℂ) G j = 0 := by
  ext a b
  rw [distMatrix_apply, Matrix.zero_apply, if_neg]
  intro hd
  have h1 : cval G b j = cnum G b a j :=
    cval_eq_cnum (hdr b) (by rw [SimpleGraph.dist_comm]; exact hd)
  have h2 : cval G b j = cval G x j := (hbi b x j).2.2
  have h3 : cnum G b a j ≠ 0 :=
    cnum_ne_zero_of_dist hG hj (by rw [SimpleGraph.dist_comm]; exact hd)
  omega

/-- The polynomial sequence of Lemma 16.2 (ii): `p₀ = 1`, `p₁ = λ` and
`p_{i+2}` is `λ p_{i+1} - a_{i+1}p_{i+1} - bᵢpᵢ`, normalised by `c_{i+2}`. -/
def distPoly (G : SimpleGraph X) (x : X) : ℕ → Polynomial ℂ
  | 0 => 1
  | 1 => Polynomial.X
  | (i + 2) =>
      Polynomial.C (if cval G x (i + 2) = 0 then (1 : ℂ) else ((cval G x (i + 2) : ℂ))⁻¹) *
        (Polynomial.X * distPoly G x (i + 1)
          - (Polynomial.C ((aval G x (i + 1) : ℕ) : ℂ) * distPoly G x (i + 1)
            + Polynomial.C ((bval G x i : ℕ) : ℂ) * distPoly G x i))

/-- The polynomials `pᵢ` have degree `i`. -/
theorem distPoly_natDegree (G : SimpleGraph X) (x : X) (i : ℕ) :
    (distPoly G x i).natDegree = i := by
  induction i using Nat.twoStepInduction with
  | zero => simp [distPoly]
  | one => simp [distPoly]
  | more n ih0 ih1 =>
    have hk : (if cval G x (n + 2) = 0 then (1 : ℂ) else ((cval G x (n + 2) : ℂ))⁻¹) ≠ 0 := by
      split_ifs with h
      · exact one_ne_zero
      · exact inv_ne_zero (by exact_mod_cast h)
    have hne : distPoly G x (n + 1) ≠ 0 := by
      intro h
      rw [h] at ih1
      simp at ih1
    have h1 : (Polynomial.X * distPoly G x (n + 1)).natDegree = n + 1 + 1 := by
      rw [Polynomial.natDegree_X_mul hne, ih1]
    have h2 : (Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ) * distPoly G x (n + 1)
        + Polynomial.C ((bval G x n : ℕ) : ℂ) * distPoly G x n).natDegree < n + 1 + 1 := by
      have ha : (Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ)
          * distPoly G x (n + 1)).natDegree ≤ n + 1 := by
        have h := Polynomial.natDegree_mul_le (p := Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ))
          (q := distPoly G x (n + 1))
        rw [Polynomial.natDegree_C, ih1] at h
        omega
      have hb : (Polynomial.C ((bval G x n : ℕ) : ℂ) * distPoly G x n).natDegree ≤ n := by
        have h := Polynomial.natDegree_mul_le (p := Polynomial.C ((bval G x n : ℕ) : ℂ))
          (q := distPoly G x n)
        rw [Polynomial.natDegree_C, ih0] at h
        omega
      have h3 := Polynomial.natDegree_add_le
        (p := Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ) * distPoly G x (n + 1))
        (q := Polynomial.C ((bval G x n : ℕ) : ℂ) * distPoly G x n)
      omega
    have h2' : (Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ) * distPoly G x (n + 1)
        + Polynomial.C ((bval G x n : ℕ) : ℂ) * distPoly G x n).natDegree
        < (Polynomial.X * distPoly G x (n + 1)).natDegree := by
      rw [h1]; exact h2
    rw [distPoly, Polynomial.natDegree_C_mul hk,
      Polynomial.natDegree_sub_eq_left_of_natDegree_lt h2', h1]

/-- The polynomials `pᵢ` realise the distance matrices: `pᵢ(A) = Aᵢ`. -/
theorem distPoly_aeval {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) (i : ℕ) :
    Polynomial.aeval (adj (𝕜 := ℂ) G) (distPoly G x i) = distMatrix (𝕜 := ℂ) G i := by
  induction i using Nat.twoStepInduction with
  | zero => rw [distPoly, map_one, distMatrix_zero (𝕜 := ℂ) G hG]
  | one => rw [distPoly, Polynomial.aeval_X, distMatrix_one]
  | more n ih0 ih1 =>
    have hinner : Polynomial.aeval (adj (𝕜 := ℂ) G)
        (Polynomial.X * distPoly G x (n + 1)
          - (Polynomial.C ((aval G x (n + 1) : ℕ) : ℂ) * distPoly G x (n + 1)
            + Polynomial.C ((bval G x n : ℕ) : ℂ) * distPoly G x n))
        = ((cval G x (n + 2) : ℕ) : ℂ) • distMatrix (𝕜 := ℂ) G (n + 2) := by
      simp only [map_sub, map_add, map_mul, Polynomial.aeval_X, ih1, ih0, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
      rw [adj_mul_distMatrix hG hdr hbi (x := x) (i := n + 1) (by omega)]
      simp only [Nat.add_sub_cancel]
      abel
    rw [distPoly, map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul,
      one_mul, hinner, smul_smul]
    by_cases hc : cval G x (n + 2) = 0
    · have hz : distMatrix (𝕜 := ℂ) G (n + 2) = 0 :=
        distMatrix_eq_zero_of_cval_eq_zero hG hdr hbi (x := x) (j := n + 2) (by omega) hc
      rw [if_pos hc, one_mul, hc, Nat.cast_zero, zero_smul, hz]
    · rw [if_neg hc, inv_mul_cancel₀ (by exact_mod_cast hc), one_smul]

/-- **Lemma 16.2 (ii).**  For a distance-regular graph whose intersection numbers do
not depend on the base vertex, `Aᵢ` is a monic polynomial of degree `i` in `A`. -/
theorem distMatrix_eq_polynomial {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) (i : ℕ) :
    ∃ p : Polynomial ℂ, p.natDegree = i ∧
      distMatrix (𝕜 := ℂ) G i = Polynomial.aeval (adj (𝕜 := ℂ) G) p :=
  ⟨distPoly G x i, distPoly_natDegree G x i, (distPoly_aeval hG hdr hbi i).symm⟩

/-- `Aⱼ = 0` when `j` exceeds the diameter. -/
theorem distMatrix_eq_zero_of_lt {G : SimpleGraph X} {D : ℕ} (hD : ∀ a b : X, G.dist a b ≤ D)
    {j : ℕ}
    (hj : D < j) :
    distMatrix (𝕜 := 𝕜) G j = 0 := by
  ext a b
  rw [distMatrix_apply, Matrix.zero_apply, if_neg]
  intro h
  have := hD a b
  omega

/-- Each distance matrix is a polynomial in `A`. -/
theorem distMatrix_mem_boseMesner {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) (i : ℕ) :
    distMatrix (𝕜 := ℂ) G i ∈ boseMesner (𝕜 := ℂ) G := by
  obtain ⟨p, -, hp⟩ := distMatrix_eq_polynomial hG hdr hbi (x := x) i
  rw [boseMesner, Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨p, hp.symm⟩

/-- **Lemma 16.2 (iii).**  For a distance-regular graph whose intersection numbers do
not depend on the base vertex, the distance matrices span the Bose–Mesner algebra. -/
theorem boseMesner_eq_span_distMatrix {G : SimpleGraph X} {x : X} (hG : G.Connected)
    (hdr : IsDistanceRegular G) (hbi : IntersectionNumbersIndependent G) (D : ℕ)
    (hD1 : 1 ≤ D) (hD : ∀ a b : X, G.dist a b ≤ D) :
    (boseMesner (𝕜 := ℂ) G).toSubmodule
      = Submodule.span ℂ (Set.range fun i : Fin (D + 1) => distMatrix (𝕜 := ℂ) G i) := by
  classical
  set S : Submodule ℂ (Matrix X X ℂ) :=
    Submodule.span ℂ (Set.range fun i : Fin (D + 1) => distMatrix (𝕜 := ℂ) G i) with hS
  have hmem : ∀ j : ℕ, distMatrix (𝕜 := ℂ) G j ∈ S := by
    intro j
    by_cases hj : j ≤ D
    · exact Submodule.subset_span ⟨⟨j, by omega⟩, rfl⟩
    · rw [distMatrix_eq_zero_of_lt hD (by omega)]
      exact Submodule.zero_mem _
  have hA0 : (1 : Matrix X X ℂ) ∈ S := by
    rw [← distMatrix_zero (𝕜 := ℂ) G hG]
    exact Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
  have hstep : ∀ j : ℕ, adj (𝕜 := ℂ) G * distMatrix (𝕜 := ℂ) G j ∈ S := by
    intro j
    rcases j with _ | k
    · rw [distMatrix_zero (𝕜 := ℂ) G hG, mul_one]
      have h1 : distMatrix (𝕜 := ℂ) G 1 ∈ S := hmem 1
      rwa [distMatrix_one] at h1
    · rw [adj_mul_distMatrix hG hdr hbi (x := x) (i := k + 1) (by omega)]
      exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ (hmem _))
        (Submodule.smul_mem _ _ (hmem _))) (Submodule.smul_mem _ _ (hmem _))
  have hSclosed : ∀ m ∈ S, adj (𝕜 := ℂ) G * m ∈ S := by
    intro m hm
    rw [hS] at hm
    induction hm using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        exact hstep (i : ℕ)
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hu
  have hpow : ∀ j : ℕ, adj (𝕜 := ℂ) G ^ j ∈ S := by
    intro j
    induction j with
    | zero => simpa using hA0
    | succ n ih => rw [pow_succ']; exact hSclosed _ ih
  have haeval : ∀ p : Polynomial ℂ, Polynomial.aeval (adj (𝕜 := ℂ) G) p ∈ S := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq
    | monomial n a =>
        rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul]
        exact Submodule.smul_mem _ _ (hpow n)
  refine le_antisymm ?_ ?_
  · intro m hm
    rw [boseMesner, Algebra.adjoin_singleton_eq_range_aeval] at hm
    obtain ⟨p, hp⟩ := hm
    rw [← hp]
    exact haeval p
  · rw [hS]
    exact Submodule.span_le.mpr (Set.range_subset_iff.mpr fun i =>
      distMatrix_mem_boseMesner hG hdr hbi (x := x) (i := (i : ℕ)))

end Terwilliger
