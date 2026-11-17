/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.PerronFrobenius

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
# Collatz–Wielandt theory for nonnegative matrices

This file develops the variational half of the Perron–Frobenius theorem by the
Collatz–Wielandt method, for a symmetric nonnegative irreducible real matrix
`C : Matrix X X ℝ`.

The plan of the argument (see `ROADMAP.md`) is:

1. `K = {v | v ≥ 0, v ⬝ᵥ v = 1}` is compact (`isCompact_K`), and `quad C v = v ⬝ᵥ (C *ᵥ v)`
   is continuous (`quad_continuous`), so `quad` attains a maximum on `K`
   (`exists_maximizer`).
2. At a maximiser `v`, every feasible direction `d` satisfies the first-order
   inequality `(C *ᵥ v) ⬝ᵥ d ≤ quad C v * (v ⬝ᵥ d)` (`first_order_general`).
   This is proved by normalising `v + s • d` and letting `s → 0⁺`; no calculus and
   no Lagrange multipliers are needed, only the algebraic expansion
   `quad_add_smul` and the closedness of `{s | … ≤ 0}`.
3. A maximiser is strictly positive (`maximizer_pos`): if `v j = 0` then the
   one-sided condition with `d = eⱼ` forces `(C v) j = 0`, i.e. row `j` vanishes on
   the support of `v`; the support and its complement would then give a
   reducibility witness, contradicting irreducibility.
4. Consequently `C v = quad C v • v` (`maximizer_eigen`), `quad C v > 0`
   (`quad_pos_of_ne_zero`), and `quad C v` dominates every eigenvalue
   (`eigenvalue_le_quad`).
5. `eq_zero_of_mulVec_le` is the maximum principle used for the last step: a
   nonnegative `w` with `C w ≤ θ w` and a zero entry must vanish.
6. Finally `eigenvector_unique` gives the uniqueness of the Perron eigenvector
   up to scale (via the maximum principle applied to `M v - |u|` and to
   `|u| - u`), and `perron_frobenius` assembles Theorem 2.4 (i), (ii).
-/

set_option linter.unusedSectionVars false
open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]


def quad (C : Matrix X X ℝ) (v : X → ℝ) : ℝ := v ⬝ᵥ (C *ᵥ v)

theorem continuous_mulVec_const (C : Matrix X X ℝ) :
    Continuous fun v : X → ℝ => C *ᵥ v := by
  rw [continuous_pi_iff]
  intro i
  simp only [mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

theorem quad_continuous (C : Matrix X X ℝ) : Continuous (quad C) :=
  Continuous.dotProduct continuous_id (continuous_mulVec_const C)

theorem quad_add_smul (C : Matrix X X ℝ) (hsym : Cᵀ = C) (v d : X → ℝ) (s : ℝ) :
    quad C (v + s • d) = quad C v + 2 * s * ((C *ᵥ v) ⬝ᵥ d) + s ^ 2 * (d ⬝ᵥ (C *ᵥ d)) := by
  have hsym' : v ⬝ᵥ (C *ᵥ d) = (C *ᵥ v) ⬝ᵥ d := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym]
  have hcomm : d ⬝ᵥ (C *ᵥ v) = (C *ᵥ v) ⬝ᵥ d := dotProduct_comm _ _
  calc quad C (v + s • d)
      = (v + s • d) ⬝ᵥ (C *ᵥ v + s • (C *ᵥ d)) := by
          rw [quad, mulVec_add, mulVec_smul]
    _ = (v + s • d) ⬝ᵥ (C *ᵥ v) + (v + s • d) ⬝ᵥ (s • (C *ᵥ d)) := by
          rw [dotProduct_add]
    _ = ((v ⬝ᵥ (C *ᵥ v) + (s • d) ⬝ᵥ (C *ᵥ v)) + s • ((v + s • d) ⬝ᵥ (C *ᵥ d))) := by
          rw [add_dotProduct, dotProduct_smul]
    _ = quad C v + 2 * s * ((C *ᵥ v) ⬝ᵥ d) + s ^ 2 * (d ⬝ᵥ (C *ᵥ d)) := by
          rw [quad, add_dotProduct, smul_dotProduct, smul_add, smul_dotProduct, smul_smul,
            hsym', hcomm]
          simp only [smul_eq_mul]
          ring

def K (X : Type*) [Fintype X] [DecidableEq X] : Set (X → ℝ) :=
  {v | (∀ i, 0 ≤ v i) ∧ v ⬝ᵥ v = 1}

theorem isClosed_K : IsClosed (K X) := by
  have h1 : IsClosed {v : X → ℝ | ∀ i, 0 ≤ v i} := by
    rw [show {v : X → ℝ | ∀ i, 0 ≤ v i} = ⋂ i, {v : X → ℝ | 0 ≤ v i} from by
      ext v; simp]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {v : X → ℝ | v ⬝ᵥ v = 1} := by
    rw [show {v : X → ℝ | v ⬝ᵥ v = 1}
        = (fun v : X → ℝ => v ⬝ᵥ v) ⁻¹' {1} from rfl]
    exact IsClosed.preimage (Continuous.dotProduct continuous_id continuous_id)
      isClosed_singleton
  exact h1.inter h2

theorem isCompact_K : IsCompact (K X) := by
  have hbox : IsCompact (Set.univ.pi fun _ : X => Set.Icc (-1 : ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine hbox.of_isClosed_subset isClosed_K ?_
  intro v hv
  obtain ⟨h0, h1⟩ := hv
  simp only [Set.mem_univ_pi, Set.mem_Icc]
  intro i
  have hii : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  have h1' : ∑ j, v j * v j = 1 := by simpa [dotProduct] using h1
  rw [h1'] at hii
  constructor <;> nlinarith [h0 i]

theorem K_nonempty (hcard : 0 < Fintype.card X) : (K X).Nonempty := by
  have hn' : (0:ℝ) < Fintype.card X := by exact_mod_cast hcard
  refine ⟨fun _ => (Real.sqrt (Fintype.card X))⁻¹, fun i => ?_, ?_⟩
  · positivity
  · rw [dotProduct, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h : Real.sqrt (Fintype.card X) * Real.sqrt (Fintype.card X)
        = (Fintype.card X : ℝ) := by rw [← sq, Real.sq_sqrt hn'.le]
    have hs : Real.sqrt (Fintype.card X) ≠ 0 := by positivity
    field_simp
    linarith

theorem mem_K_norm_le_one {v : X → ℝ} (hv : v ∈ K X) (i : X) : |v i| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hv
  have hii : v i * v i ≤ ∑ j, v j * v j :=
    Finset.single_le_sum (f := fun j => v j * v j)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
  have h1' : ∑ j, v j * v j = 1 := by simpa [dotProduct] using h1
  rw [h1'] at hii
  rw [abs_le]
  constructor <;> nlinarith [h0 i]

theorem exists_maximizer (hcard : 0 < Fintype.card X) (C : Matrix X X ℝ) :
    ∃ v ∈ K X, ∀ u ∈ K X, quad C u ≤ quad C v :=
  (isCompact_K (X := X)).exists_isMaxOn (K_nonempty hcard) (quad_continuous C).continuousOn

theorem dotProduct_smul_smul (c : ℝ) (w : X → ℝ) :
    (c • w) ⬝ᵥ (c • w) = c ^ 2 * (w ⬝ᵥ w) := by
  rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, sq]

theorem quad_smul (C : Matrix X X ℝ) (c : ℝ) (w : X → ℝ) :
    quad C (c • w) = c ^ 2 * quad C w := by
  rw [quad, quad, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, sq]

/-- The first-order condition at a maximiser of `quad` on `K`: for every direction
`d` that stays feasible on `[0, δ)`, one has `(Cv)·d ≤ θ (v·d)` with `θ = quad C v`. -/
theorem first_order_general (C : Matrix X X ℝ) (hsym : Cᵀ = C) {v : X → ℝ}
    (hvK : v ∈ K X) (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v)
    {d : X → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hfeas : ∀ s : ℝ, 0 ≤ s → s < δ → ∀ i, 0 ≤ v i + s * d i) :
    (C *ᵥ v) ⬝ᵥ d ≤ quad C v * (v ⬝ᵥ d) := by
  obtain ⟨hv0, hvv⟩ := hvK
  by_contra hcon
  push Not at hcon
  set α := (C *ᵥ v) ⬝ᵥ d with hα
  set β := d ⬝ᵥ (C *ᵥ d) with hβ
  set Kd := d ⬝ᵥ d with hKd
  set γ := v ⬝ᵥ d with hγ
  set θ := quad C v with hθ
  have hKd0 : 0 ≤ Kd := by
    rw [hKd, dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  -- a small upper bound for `s` making `w·w > 0`
  have hden : (0:ℝ) < 4 * (|γ| + |Kd| + 1) := by positivity
  set δ' : ℝ := min δ (1 / (4 * (|γ| + |Kd| + 1))) with hδ'
  have hδ'pos : 0 < δ' := lt_min hδ (by positivity)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  have hδ'le' : δ' ≤ 1 / (4 * (|γ| + |Kd| + 1)) := min_le_right _ _
  have hδ'one : δ' ≤ 1 := by
    have h2 : 1 / (4 * (|γ| + |Kd| + 1)) ≤ 1 := by
      rw [div_le_one hden]; linarith [abs_nonneg γ, abs_nonneg Kd]
    linarith
  have key : ∀ s : ℝ, 0 < s → s < δ' → 2 * (α - θ * γ) + s * (β - θ * Kd) ≤ 0 := by
    intro s hs0 hs1
    have hsd : s < δ := lt_of_lt_of_le hs1 hδ'le
    set w : X → ℝ := v + s • d with hw
    have hw0 : ∀ i, 0 ≤ w i := by
      intro i
      have := hfeas s hs0.le hsd i
      simpa [hw, smul_eq_mul] using this
    have hww : w ⬝ᵥ w = 1 + 2 * s * γ + s ^ 2 * Kd := by
      have h := quad_add_smul (1 : Matrix X X ℝ) (by simp) v d s
      simp only [quad, one_mulVec, hKd, hγ] at h
      rw [h, hvv]
    have hww_pos : 0 < w ⬝ᵥ w := by
      rw [hww]
      have hs1' : s ≤ 1 := le_of_lt (lt_of_lt_of_le hs1 hδ'one)
      have hsq : s ^ 2 ≤ s := by nlinarith [hs0, hs1']
      have h2 : 2 * s * |γ| ≤ 2 * (1 / (4 * (|γ| + |Kd| + 1))) * |γ| := by
        have : s * |γ| ≤ (1 / (4 * (|γ| + |Kd| + 1))) * |γ| :=
          mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le hs1 hδ'le')) (abs_nonneg γ)
        linarith
      have h3 : s ^ 2 * |Kd| ≤ (1 / (4 * (|γ| + |Kd| + 1))) * |Kd| := by
        have h4 : s ^ 2 * |Kd| ≤ s * |Kd| := mul_le_mul_of_nonneg_right hsq (abs_nonneg Kd)
        have h5 : s * |Kd| ≤ (1 / (4 * (|γ| + |Kd| + 1))) * |Kd| :=
          mul_le_mul_of_nonneg_right (le_of_lt (lt_of_lt_of_le hs1 hδ'le')) (abs_nonneg Kd)
        linarith
      have h6 : 2 * (1 / (4 * (|γ| + |Kd| + 1))) * |γ| + (1 / (4 * (|γ| + |Kd| + 1))) * |Kd|
          ≤ 1 / 2 := by
        rw [← sub_nonneg]
        have heq : 1 / 2 - (2 * (1 / (4 * (|γ| + |Kd| + 1))) * |γ|
            + (1 / (4 * (|γ| + |Kd| + 1))) * |Kd|)
            = (2 * (|γ| + |Kd| + 1) - (2 * |γ| + |Kd|)) / (4 * (|γ| + |Kd| + 1)) := by
          field_simp
          ring
        rw [heq]
        apply div_nonneg <;> nlinarith [abs_nonneg γ, abs_nonneg Kd]
      nlinarith [neg_abs_le γ, neg_abs_le Kd, h2, h3, h6]
    set c : ℝ := (Real.sqrt (w ⬝ᵥ w))⁻¹ with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hcsq : c ^ 2 = (w ⬝ᵥ w)⁻¹ := by
      rw [hc, inv_pow, Real.sq_sqrt hww_pos.le]
    have hw'K : c • w ∈ K X := by
      refine ⟨fun i => ?_, ?_⟩
      · exact mul_nonneg hcpos.le (hw0 i)
      · rw [dotProduct_smul_smul, hcsq, inv_mul_cancel₀ hww_pos.ne']
    have hmax := hvmax (c • w) hw'K
    rw [quad_smul, hcsq] at hmax
    have hqw : quad C w = θ + 2 * s * α + s ^ 2 * β := by
      rw [hθ, hα, hβ, hw, quad_add_smul C hsym]
    rw [hqw, hww] at hmax
    have hD : 0 < 1 + 2 * s * γ + s ^ 2 * Kd := by rw [← hww]; exact hww_pos
    have h2 : θ + 2 * s * α + s ^ 2 * β ≤ (1 + 2 * s * γ + s ^ 2 * Kd) * θ := by
      have h3 := mul_le_mul_of_nonneg_left hmax hD.le
      rwa [← mul_assoc, mul_inv_cancel₀ hD.ne', one_mul] at h3
    have h4 : s * (2 * (α - θ * γ) + s * (β - θ * Kd)) ≤ 0 := by nlinarith [h2]
    by_contra hc2
    push Not at hc2
    nlinarith [h4, hs0, hc2]
  -- s → 0⁺
  have hclosed : IsClosed {s : ℝ | 2 * (α - θ * γ) + s * (β - θ * Kd) ≤ 0} :=
    isClosed_le (by continuity) continuous_const
  have h0 : (0:ℝ) ∈ closure (Set.Ioo (0:ℝ) δ') := by
    rw [closure_Ioo (a := (0:ℝ)) (b := δ') (ne_of_lt hδ'pos)]
    exact ⟨le_rfl, hδ'pos.le⟩
  have hsub : Set.Ioo (0:ℝ) δ' ⊆ {s : ℝ | 2 * (α - θ * γ) + s * (β - θ * Kd) ≤ 0} :=
    fun (s : ℝ) hs => key s hs.1 hs.2
  have hmem : (0:ℝ) ∈ {s : ℝ | 2 * (α - θ * γ) + s * (β - θ * Kd) ≤ 0} :=
    hclosed.closure_subset (closure_mono hsub h0)
  simp only [Set.mem_ofPred_eq, mul_zero, add_zero] at hmem
  linarith

theorem dotProduct_delta {u : X → ℝ} {i : X} {c : ℝ} :
    u ⬝ᵥ (fun k => if i = k then c else 0) = c * u i := by
  rw [dotProduct, Finset.sum_eq_single i]
  · simp [mul_comm]
  · intro b _ hb; simp [if_neg (Ne.symm hb)]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem dotProduct_single (v : X → ℝ) (j : X) :
    v ⬝ᵥ (Pi.single j (1:ℝ)) = v j := by
  rw [dotProduct, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; simp [Pi.single_eq_of_ne hb]
  · intro h; simp at h

theorem single_dotProduct (v : X → ℝ) (j : X) :
    (Pi.single j (1:ℝ)) ⬝ᵥ v = v j := by
  rw [dotProduct_comm]; exact dotProduct_single v j

theorem mulVec_single (C : Matrix X X ℝ) (j : X) :
    (C *ᵥ v) ⬝ᵥ (Pi.single j (1:ℝ)) = (C *ᵥ v) j := dotProduct_single _ _

/-- **Positivity.**  A maximiser of `quad` on `K` is strictly positive when `C` is
irreducible with nonnegative entries. -/
theorem maximizer_pos {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hnn : ∀ i j, 0 ≤ C i j) {v : X → ℝ} (hvK : v ∈ K X)
    (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v) (hirr : IsIrreducibleMatrix C) :
    ∀ i, 0 < v i := by
  obtain ⟨hv0, hvv⟩ := hvK
  by_contra hcon
  push Not at hcon
  obtain ⟨j0, hj0⟩ := hcon
  have hvj0 : v j0 = 0 := le_antisymm hj0 (hv0 j0)
  -- every `j` with `v j = 0` has row vanishing on the support of `v`
  have hrow : ∀ j, v j = 0 → ∀ k, 0 < v k → C j k = 0 := by
    intro j hvj k hvk
    set e : X → ℝ := Pi.single j (1:ℝ) with he
    have hd : v ⬝ᵥ e = 0 := by
      rw [he]; rw [dotProduct_single, hvj]
    have hfeas : ∀ s : ℝ, 0 ≤ s → s < 1 → ∀ i, 0 ≤ v i + s * e i := by
      intro s hs _ i
      have h2 : (0:ℝ) ≤ e i := by
        rw [he]
        by_cases h : j = i
        · subst h; simp
        · rw [Pi.single_apply, if_neg (Ne.symm h)]
      nlinarith [hv0 i, mul_nonneg hs h2]
    have hle := first_order_general C hsym ⟨hv0, hvv⟩ hvmax (δ := 1) one_pos hfeas
    rw [hd, mul_zero] at hle
    have hval : (C *ᵥ v) ⬝ᵥ e = (C *ᵥ v) j := by rw [he]; exact dotProduct_single _ _
    rw [hval] at hle
    have hnn' : 0 ≤ (C *ᵥ v) j := by
      rw [mulVec, dotProduct]
      exact Finset.sum_nonneg fun i _ => mul_nonneg (hnn j i) (hv0 i)
    have hzero : (C *ᵥ v) j = 0 := le_antisymm hle hnn'
    rw [mulVec, dotProduct] at hzero
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun i => C j i * v i) (fun i _ => mul_nonneg (hnn j i) (hv0 i))).mp hzero
    have hk := hterm k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hvk)
  -- the partition given by the support of `v`
  set P : Finset X := Finset.univ.filter (fun i => v i ≠ 0) with hP
  set Z : Finset X := Finset.univ.filter (fun j => v j = 0) with hZ
  have hPne : P.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      have hv0' : v = 0 := funext h
      rw [hv0'] at hvv
      simp at hvv
    exact ⟨i, by rw [hP]; simp [hi]⟩
  have hZne : Z.Nonempty := ⟨j0, by rw [hZ]; simp [hvj0]⟩
  have hdisj : Disjoint P Z := by
    rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hP, Finset.mem_filter] at hi
    simp only [hZ, Finset.mem_filter] at hi'
    exact hi.2 hi'.2
  have hunion : P ∪ Z = Finset.univ := by
    ext i
    simp only [hP, hZ, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases h : v i = 0
    · exact Or.inr h
    · exact Or.inl h
  have hzero1 : ∀ i ∈ P, ∀ j ∈ Z, C i j = 0 := by
    intro i hi j hj
    simp only [hP, Finset.mem_filter] at hi
    simp only [hZ, Finset.mem_filter] at hj
    rw [← hsym]
    exact hrow j hj.2 i (lt_of_le_of_ne (hv0 i) (Ne.symm hi.2))
  have hzero2 : ∀ i ∈ Z, ∀ j ∈ P, C i j = 0 := by
    intro i hi j hj
    simp only [hP, Finset.mem_filter] at hj
    simp only [hZ, Finset.mem_filter] at hi
    exact hrow i hi.2 j (lt_of_le_of_ne (hv0 j) (Ne.symm hj.2))
  exact hirr ⟨P, Z, hPne, hZne, hdisj, hunion, hzero1, hzero2⟩

theorem abs_dotProduct_le (h : X → ℝ) (w : X → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |h ⬝ᵥ w| ≤ (fun i => |h i|) ⬝ᵥ w := by
  rw [dotProduct, dotProduct]
  calc |∑ i, h i * w i| ≤ ∑ i, |h i * w i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, |h i| * w i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul, abs_of_nonneg (hw i)]

theorem mulVec_abs_le {C : Matrix X X ℝ} (hnn : ∀ i j, 0 ≤ C i j)
    (u : X → ℝ) (i : X) :
    |(C *ᵥ u) i| ≤ (C *ᵥ (fun j => |u j|)) i := by
  rw [mulVec, dotProduct, mulVec, dotProduct]
  calc |∑ j, C i j * u j| ≤ ∑ j, |C i j * u j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j, C i j * |u j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_of_nonneg (hnn i j)]

/-- **The eigenvector equation** at a strictly positive maximiser. -/
theorem maximizer_eigen {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    {v : X → ℝ} (hvK : v ∈ K X) (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v)
    (hvpos : ∀ i, 0 < v i) :
    C *ᵥ v = quad C v • v := by
  obtain ⟨hv0, hvv⟩ := hvK
  funext i
  have hle : (C *ᵥ v) i ≤ quad C v * v i := by
    have hfeas : ∀ s : ℝ, 0 ≤ s → s < 1 → ∀ k,
        0 ≤ v k + s * (fun k => if i = k then (1:ℝ) else 0) k := by
      intro s hs _ k
      dsimp only
      by_cases hk : i = k
      · rw [if_pos hk]; nlinarith [hv0 k]
      · rw [if_neg hk]; simp only [mul_zero, add_zero]; exact hv0 k
    have h := first_order_general (C := C) hsym ⟨hv0, hvv⟩ hvmax (δ := 1) one_pos
      (d := fun k => if i = k then (1:ℝ) else 0) hfeas
    rw [dotProduct_delta, dotProduct_delta] at h
    simpa using h
  have hge : quad C v * v i ≤ (C *ᵥ v) i := by
    have hfeas : ∀ s : ℝ, 0 ≤ s → s < v i → ∀ k,
        0 ≤ v k + s * (fun k => if i = k then (-1:ℝ) else 0) k := by
      intro s hs hsv k
      dsimp only
      by_cases hk : i = k
      · rw [if_pos hk]; simp only [mul_neg, mul_one]; rw [hk] at hsv; linarith
      · rw [if_neg hk]; simp only [mul_zero, add_zero]; exact hv0 k
    have h := first_order_general (C := C) hsym ⟨hv0, hvv⟩ hvmax (δ := v i) (hvpos i)
      (d := fun k => if i = k then (-1:ℝ) else 0) hfeas
    rw [dotProduct_delta, dotProduct_delta] at h
    simp only [neg_one_mul] at h
    linarith
  rw [Pi.smul_apply, smul_eq_mul]
  linarith

theorem quad_pos_of_ne_zero {C : Matrix X X ℝ} (hnn : ∀ i j, 0 ≤ C i j)
    (hC0 : C ≠ 0) {v : X → ℝ} (hvpos : ∀ i, 0 < v i) : 0 < quad C v := by
  obtain ⟨a, b, hab⟩ : ∃ a b, C a b ≠ 0 := by
    by_contra h; push Not at h
    exact hC0 (funext fun a => funext fun b => h a b)
  have hab' : 0 < C a b := lt_of_le_of_ne (hnn a b) (Ne.symm hab)
  have heq : quad C v = ∑ i, ∑ j, v i * (C i j * v j) := by
    simp only [quad, mulVec, dotProduct, Finset.mul_sum]
  rw [heq]
  have hrow : v a * (C a b * v b) ≤ ∑ j, v a * (C a j * v j) :=
    Finset.single_le_sum (f := fun j => v a * (C a j * v j))
      (fun j _ => mul_nonneg (le_of_lt (hvpos a))
        (mul_nonneg (hnn a j) (le_of_lt (hvpos j)))) (Finset.mem_univ b)
  have hall : (∑ j, v a * (C a j * v j)) ≤ ∑ i, ∑ j, v i * (C i j * v j) :=
    Finset.single_le_sum (f := fun i => ∑ j, v i * (C i j * v j))
      (fun i _ => Finset.sum_nonneg fun j _ =>
        mul_nonneg (le_of_lt (hvpos i)) (mul_nonneg (hnn i j) (le_of_lt (hvpos j))))
      (Finset.mem_univ a)
  have hpos : 0 < v a * (C a b * v b) := mul_pos (hvpos a) (mul_pos hab' (hvpos b))
  linarith

/-- **Maximality.**  Every eigenvalue is at most `quad C v` at a maximiser. -/
theorem eigenvalue_le_quad {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hnn : ∀ i j, 0 ≤ C i j) {v : X → ℝ} (hvK : v ∈ K X)
    (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v) (hvpos : ∀ i, 0 < v i)
    {u : X → ℝ} (hu : u ≠ 0) {μ : ℝ} (heig : C *ᵥ u = μ • u) :
    μ ≤ quad C v := by
  have hu_pos : 0 < u ⬝ᵥ u := by
    have h1 : 0 ≤ u ⬝ᵥ u := by
      rw [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have h2 : u ⬝ᵥ u ≠ 0 := by
      intro h; exact hu ((dotProduct_self_eq_zero).mp h)
    exact lt_of_le_of_ne h1 (Ne.symm h2)
  have h1 : u ⬝ᵥ (C *ᵥ u) ≤ (fun i => |u i|) ⬝ᵥ (C *ᵥ (fun j => |u j|)) := by
    rw [dotProduct, dotProduct]
    apply Finset.sum_le_sum
    intro i _
    have h2 : u i * (C *ᵥ u) i ≤ |u i| * |(C *ᵥ u) i| := by
      calc u i * (C *ᵥ u) i ≤ |u i * (C *ᵥ u) i| := le_abs_self _
        _ = |u i| * |(C *ᵥ u) i| := abs_mul _ _
    have h3 : |u i| * |(C *ᵥ u) i| ≤ |u i| * (C *ᵥ (fun j => |u j|)) i :=
      mul_le_mul_of_nonneg_left (mulVec_abs_le hnn u i) (abs_nonneg _)
    linarith
  have h2 : (fun i => |u i|) ⬝ᵥ (C *ᵥ (fun j => |u j|)) ≤ quad C v * (u ⬝ᵥ u) := by
    set w : X → ℝ := fun i => |u i| with hw
    have hw0 : ∀ i, 0 ≤ w i := fun i => abs_nonneg _
    have hww : w ⬝ᵥ w = u ⬝ᵥ u := by
      rw [dotProduct, dotProduct]
      apply Finset.sum_congr rfl
      intro i _
      simp only [hw]
      rw [← sq, sq_abs, sq]
    have hwwpos : 0 < w ⬝ᵥ w := by rw [hww]; exact hu_pos
    set c : ℝ := (Real.sqrt (w ⬝ᵥ w))⁻¹ with hc
    have hcpos : 0 < c := by rw [hc]; positivity
    have hcsq : c ^ 2 = (w ⬝ᵥ w)⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hwwpos.le]
    have hwK : c • w ∈ K X := by
      refine ⟨fun i => mul_nonneg hcpos.le (hw0 i), ?_⟩
      rw [dotProduct_smul_smul, hcsq, inv_mul_cancel₀ hwwpos.ne']
    have hmax := hvmax (c • w) hwK
    rw [quad_smul, hcsq] at hmax
    calc (fun i => |u i|) ⬝ᵥ (C *ᵥ (fun j => |u j|))
        = quad C w := by rw [hw, quad]
      _ = (w ⬝ᵥ w) * ((w ⬝ᵥ w)⁻¹ * quad C w) := by
          rw [← mul_assoc, mul_inv_cancel₀ hwwpos.ne', one_mul]
      _ ≤ (w ⬝ᵥ w) * quad C v := mul_le_mul_of_nonneg_left hmax hwwpos.le
      _ = quad C v * (u ⬝ᵥ u) := by rw [hww]; ring
  have hμ : μ * (u ⬝ᵥ u) = u ⬝ᵥ (C *ᵥ u) := by
    rw [heig, dotProduct_smul, smul_eq_mul]
  nlinarith [h1, h2]

/-- **The maximum principle.**  If `0 ≤ w`, `(C w)_i ≤ θ w_i` and `w` has a zero
entry, then `w = 0` (for `C` irreducible with nonnegative entries and `θ > 0`). -/
theorem eq_zero_of_mulVec_le {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hnn : ∀ i j, 0 ≤ C i j) (hirr : IsIrreducibleMatrix C) {θ : ℝ} (hθ : 0 < θ)
    {w : X → ℝ} (hw0 : ∀ i, 0 ≤ w i) (hcle : ∀ i, (C *ᵥ w) i ≤ θ * w i)
    {i₀ : X} (hi₀ : w i₀ = 0) : w = 0 := by
  by_contra hw
  have hZ : ∀ i, w i = 0 → ∀ k, 0 < w k → C i k = 0 := by
    intro i hi k hk
    have h1 : (C *ᵥ w) i ≤ 0 := by simpa [hi] using hcle i
    have h2 : 0 ≤ (C *ᵥ w) i := by
      rw [mulVec, dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_nonneg (hnn i j) (hw0 j)
    have h3 : (C *ᵥ w) i = 0 := le_antisymm h1 h2
    rw [mulVec, dotProduct] at h3
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (f := fun j => C i j * w j) (fun j _ => mul_nonneg (hnn i j) (hw0 j))).mp h3
    have := hterm k (Finset.mem_univ k)
    rcases mul_eq_zero.mp this with h' | h'
    · exact h'
    · exact absurd h' (ne_of_gt hk)
  set P : Finset X := Finset.univ.filter (fun i => w i ≠ 0) with hP
  set Z : Finset X := Finset.univ.filter (fun i => w i = 0) with hZdef
  have hPne : P.Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push Not at h; exact hw (funext h)
    exact ⟨i, by rw [hP]; simp [hi]⟩
  have hZne : Z.Nonempty := ⟨i₀, by rw [hZdef]; simp [hi₀]⟩
  refine hirr ⟨Z, P, hZne, hPne, ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [hZdef, Finset.mem_filter] at hi
    simp only [hP, Finset.mem_filter] at hi'
    exact hi'.2 hi.2
  · ext i
    simp only [hP, hZdef, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    by_cases h : w i = 0
    · exact Or.inl h
    · exact Or.inr h
  · intro i hi j hj
    simp only [hZdef, Finset.mem_filter] at hi
    simp only [hP, Finset.mem_filter] at hj
    exact hZ i hi.2 j (lt_of_le_of_ne (hw0 j) (Ne.symm hj.2))
  · intro i hi j hj
    simp only [hP, Finset.mem_filter] at hi
    simp only [hZdef, Finset.mem_filter] at hj
    rw [← hsym]
    exact hZ j hj.2 i (lt_of_le_of_ne (hw0 i) (Ne.symm hi.2))

theorem abs_sub_mem (u : X → ℝ) : (∀ i, 0 ≤ (fun i => |u i|) i - u i) :=
  fun i => sub_nonneg.mpr (le_abs_self _)

theorem abs_add_mem (u : X → ℝ) : (∀ i, 0 ≤ (fun i => |u i|) i + u i) :=
  fun i => by have := neg_le_abs (u i); linarith


theorem mulVec_lin_apply {C : Matrix X X ℝ} {x y : X → ℝ} {a b : ℝ}
    {i : X} :
    (C *ᵥ (fun k => a * x k - b * y k)) i = a * (C *ᵥ x) i - b * (C *ᵥ y) i := by
  simp only [mulVec, dotProduct]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- **Uniqueness of the Perron eigenvector.** -/
theorem eigenvector_unique [Nonempty X] {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hnn : ∀ i j, 0 ≤ C i j) (hirr : IsIrreducibleMatrix C) (hC0 : C ≠ 0)
    {v : X → ℝ} (hvK : v ∈ K X) (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v)
    (hvpos : ∀ i, 0 < v i) {u : X → ℝ} (heig : C *ᵥ u = quad C v • u) :
    ∃ c : ℝ, u = c • v := by
  have hθ : 0 < quad C v := quad_pos_of_ne_zero hnn hC0 hvpos
  have hveig : C *ᵥ v = quad C v • v := maximizer_eigen hsym hvK hvmax hvpos
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, by simp⟩
  -- abbreviations
  have habsu : ∀ i, |(C *ᵥ u) i| = (quad C v) * |u i| := by
    intro i
    rw [heig, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hθ]
  have hpoint : ∀ i, (quad C v) * |u i| ≤ (C *ᵥ (fun j => |u j|)) i := by
    intro i
    rw [← habsu i]
    exact mulVec_abs_le hnn u i
  -- M and the maximiser j₀
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset X)
    (fun i => |u i| / v i) ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  set M : ℝ := |u j₀| / v j₀ with hM
  have hMle : ∀ i, |u i| / v i ≤ M := fun i => hj₀ i (Finset.mem_univ i)
  have hMv : ∀ i, |u i| ≤ M * v i := by
    intro i
    have h1 := hMle i
    rw [div_le_iff₀ (hvpos i)] at h1
    linarith
  have hMvj : |u j₀| = M * v j₀ := by
    rw [hM]; exact (div_mul_cancel₀ _ (ne_of_gt (hvpos j₀))).symm
  -- apply the maximum principle to `y = M v - |u|`
  have hy : (fun i => M * v i - |u i|) = 0 := by
    refine eq_zero_of_mulVec_le hsym hnn hirr hθ (fun i => sub_nonneg.mpr (hMv i))
      (fun i => ?_) (i₀ := j₀) (by beta_reduce; rw [hMvj]; ring)
    have h1 : (C *ᵥ (fun i => M * v i - 1 * |u i|)) i
        = M * (C *ᵥ v) i - 1 * (C *ᵥ (fun j => |u j|)) i := mulVec_lin_apply
    have h2 : (fun i => M * v i - 1 * |u i|) = (fun i => M * v i - |u i|) := by
      funext k; ring_nf
    rw [← h2, h1, hveig]
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [hpoint i]
  -- hence `|u| = M • v`
  have habs : (fun i => |u i|) = M • v := by
    funext i
    have h1 := congrFun hy i
    simp only [Pi.sub_apply, Pi.zero_apply] at h1
    rw [Pi.smul_apply, smul_eq_mul]
    linarith
  have hcw : C *ᵥ (fun j => |u j|) = quad C v • (fun j => |u j|) := by
    rw [habs, mulVec_smul, hveig, smul_smul, smul_smul, mul_comm]
  by_cases hsign : ∃ j, 0 ≤ u j
  · rcases hsign with ⟨j, hj⟩
    refine ⟨M, ?_⟩
    have hZu : (fun i => |u i| - u i) = 0 := by
      refine eq_zero_of_mulVec_le hsym hnn hirr hθ
        (fun i => sub_nonneg.mpr (le_abs_self _)) (fun i => ?_) (i₀ := j) ?_
      · have h2 : (C *ᵥ (fun i => 1 * (fun j => |u j|) i - 1 * u i)) i
            = 1 * (C *ᵥ (fun j => |u j|)) i - 1 * (C *ᵥ u) i := mulVec_lin_apply
        have h3 : (fun i => 1 * |u i| - 1 * u i) = (fun i => |u i| - u i) := by
          funext k; ring_nf
        rw [← h3, h2, hcw, heig]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · beta_reduce
        rw [abs_of_nonneg hj]; ring
    funext i
    have h1 := congrFun hZu i
    have h2 := congrFun habs i
    simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linarith
  · push Not at hsign
    refine ⟨-M, ?_⟩
    funext i
    have h1 : u i < 0 := hsign i
    have h2 : |u i| = -u i := abs_of_neg h1
    have h3 := congrFun habs i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [Pi.smul_apply, smul_eq_mul]
    linarith


/-- **Theorem 2.4 (Perron–Frobenius), parts (i) and (ii).**

For a symmetric irreducible nonnegative real matrix `C` with `C ≠ 0` (which
follows from irreducibility when `1 < n`) there is a real eigenvalue `θ₀`, the
Perron root, which is positive, whose eigenspace is spanned by a strictly
positive eigenvector `v`, and which dominates every eigenvalue of `C`.

Proved by Collatz–Wielandt maximisation of the quadratic form `v ⬝ᵥ (C *ᵥ v)`
on the nonnegative unit sphere.  The parts of Theorem 2.4 that need Perron root
`θ₀ := quad C v` are its existence (`exists_maximizer`, `maximizer_pos`,
`maximizer_eigen`), positivity (`quad_pos_of_ne_zero`), domination of every
eigenvalue (`eigenvalue_le_quad`) and simplicity (`eigenvector_unique`). -/
theorem perron_frobenius [Nonempty X] (C : Matrix X X ℝ)
    (hsym : Cᵀ = C) (hirr : IsIrreducibleMatrix C) (hnn : ∀ i j, 0 ≤ C i j)
    (hC0 : C ≠ 0) :
    ∃ θ : ℝ, ∃ v : X → ℝ,
      0 < θ ∧ (∀ i, 0 < v i) ∧ C *ᵥ v = θ • v ∧
      (∀ μ : ℝ, (∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u) → μ ≤ θ) ∧
      (∀ u : X → ℝ, C *ᵥ u = θ • u → ∃ c : ℝ, u = c • v) := by
  obtain ⟨v, hvK, hvmax⟩ := exists_maximizer (Fintype.card_pos_iff.mpr (inferInstance : Nonempty X)) C
  have hvpos : ∀ i, 0 < v i := maximizer_pos hsym hnn hvK hvmax hirr
  refine ⟨quad C v, v, quad_pos_of_ne_zero hnn hC0 hvpos, hvpos,
    maximizer_eigen hsym hvK hvmax hvpos, ?_, ?_⟩
  · rintro μ ⟨u, hu, heig⟩
    exact eigenvalue_le_quad hsym hnn hvK hvmax hvpos hu heig
  · intro u heig
    exact eigenvector_unique hsym hnn hirr hC0 hvK hvmax hvpos heig

/-! ## The adjacency matrix of a connected graph

`Lemma 1.2` of Chapter 1 is deduced from `perron_frobenius`: the spectral radius
of a connected graph is at most the maximal valency. -/

theorem neighborFinset_eq_filter' (G : SimpleGraph X) (x : X) :
    G.neighborFinset x = Finset.univ.filter (fun w => G.Adj x w) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.mem_neighborFinset]

theorem sum_adj_eq_valency (G : SimpleGraph X) (x : X) :
    ∑ y, adj (𝕜 := ℝ) G x y = (valency G x : ℝ) := by
  simp only [Terwilliger.adj_apply]
  rw [Finset.sum_boole (fun w => G.Adj x w) Finset.univ]
  have hcard : ((Finset.univ.filter (fun w => G.Adj x w)).card : ℝ)
      = ((G.neighborFinset x).card : ℝ) := by
    rw [← neighborFinset_eq_filter' G x]
  rw [hcard]
  rfl

/-- If a set contains `x` and is closed under adjacency, it contains everything
reachable from `x`. -/
theorem mem_of_reachable {G : SimpleGraph X} {S : Set X} {x : X} (hx : x ∈ S)
    (hS : ∀ z ∈ S, ∀ w, G.Adj z w → w ∈ S) {y : X} (h : G.Reachable x y) : y ∈ S := by
  obtain ⟨p⟩ := h
  have key : ∀ (a b : X) (t : G.Walk a b), a ∈ S → b ∈ S := by
    intro a b t
    induction t with
    | nil => exact fun hz => hz
    | cons hadj t ih => exact fun hz => ih (hS _ hz _ hadj)
  exact key x y p hx

/-- **The adjacency matrix of a connected graph with at least two vertices is
irreducible.**  A reducibility witness would partition the vertex set into two
nonempty parts with no edges across; each part is then closed under adjacency,
so connectivity is violated. -/
theorem isIrreducible_adj {G : SimpleGraph X} (hG : G.Connected) :
    IsIrreducibleMatrix (adj (𝕜 := ℝ) G) := by
  rintro ⟨Xp, Xm, hXp, hXm, hdisj, hunion, hz1, hz2⟩
  obtain ⟨x, hx⟩ := hXp
  obtain ⟨y, hy⟩ := hXm
  have hpre : G.Preconnected := (SimpleGraph.connected_iff G).mp hG |>.1
  have hclosed : ∀ z, z ∈ Xp → ∀ w, G.Adj z w → w ∈ Xp := by
    intro z hz w hadj
    by_cases hw : w ∈ Xp
    · exact hw
    · exfalso
      have hwXm : w ∈ Xm := by
        have hmem : w ∈ Xp ∪ Xm := by rw [hunion]; exact Finset.mem_univ w
        rcases Finset.mem_union.mp hmem with h | h
        · exact absurd h hw
        · exact h
      have h0 := hz1 z hz w hwXm
      rw [Terwilliger.adj_apply, if_pos hadj] at h0
      norm_num at h0
  have hy' : y ∈ Xp := by
    have hset := mem_of_reachable (G := G) (S := (Xp : Set X)) (x := x)
      (Finset.mem_coe.2 hx) (fun z hz w hadj => Finset.mem_coe.2 (hclosed z (Finset.mem_coe.1 hz) w hadj))
      (hpre x y)
    exact Finset.mem_coe.1 hset
  exact Finset.disjoint_right.mp hdisj hy hy'

theorem adj_ne_zero {G : SimpleGraph X} (hG : G.Connected) (hcard : 2 ≤ Fintype.card X) :
    adj (𝕜 := ℝ) G ≠ 0 := by
  obtain ⟨x, y, hxy⟩ : ∃ x y : X, x ≠ y := Fintype.one_lt_card_iff.mp (by omega)
  obtain ⟨p⟩ := (SimpleGraph.connected_iff G).mp hG |>.1 x y
  rcases p with _ | ⟨hadj, p⟩
  · exact absurd rfl hxy
  · have hadj' : ∃ v : X, G.Adj x v := ⟨_, hadj⟩
    obtain ⟨v, hadj⟩ := hadj'
    intro h0
    have h1 := congrFun (congrFun h0 x) v
    simp only [Terwilliger.adj_apply] at h1
    rw [if_pos hadj] at h1
    norm_num at h1

/-- **Lemma 1.2 (i).**  For a connected graph the spectral radius is at most the
maximal valency.

The proof is the Perron–Frobenius argument: with `θ` the Perron root and `v` a
strictly positive eigenvector, evaluate `A v = θ v` at a coordinate `i₀` where
`v` is maximal. -/
theorem largest_eigenvalue_le_max_valency {G : SimpleGraph X} (hG : G.Connected)
    (hcard : 2 ≤ Fintype.card X) :
    ∃ θ : ℝ, ∃ v : X → ℝ, v ≠ 0 ∧ adj (𝕜 := ℝ) G *ᵥ v = θ • v ∧
      (∀ μ : ℝ, (∃ u : X → ℝ, u ≠ 0 ∧ adj (𝕜 := ℝ) G *ᵥ u = μ • u) → μ ≤ θ) ∧
      θ ≤ ((Finset.univ.sup fun x => valency G x : ℕ) : ℝ) := by
  haveI : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  have hsym : (adj (𝕜 := ℝ) G)ᵀ = adj (𝕜 := ℝ) G := Terwilliger.adj_transpose G
  have hnn : ∀ i j, 0 ≤ adj (𝕜 := ℝ) G i j := by
    intro i j
    by_cases h : G.Adj i j <;> simp [Terwilliger.adj_apply, h]
  obtain ⟨θ, v, hθ0, hvpos, heav, hdom, -⟩ :=
    perron_frobenius (adj (𝕜 := ℝ) G) hsym (isIrreducible_adj hG) hnn (adj_ne_zero hG hcard)
  refine ⟨θ, v, ?_, heav, hdom, ?_⟩
  · intro hv
    obtain ⟨i⟩ : Nonempty X := Fintype.card_pos_iff.mp (by omega)
    have := hvpos i
    rw [hv] at this
    simp at this
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset X) v
      ⟨Classical.arbitrary X, Finset.mem_univ _⟩
    have hvi : ∀ j, v j ≤ v i₀ := fun j => hi₀ j (Finset.mem_univ j)
    -- θ * v i₀ = ∑ j, A i₀ j * v j ≤ ∑ j, A i₀ j * v i₀ = v i₀ * k(i₀)
    have hexp : (adj (𝕜 := ℝ) G *ᵥ v) i₀ = ∑ j, adj (𝕜 := ℝ) G i₀ j * v j := by
      rw [mulVec, dotProduct]
    have h1 : θ * v i₀ = ∑ j, adj (𝕜 := ℝ) G i₀ j * v j := by
      rw [← hexp, heav]; rfl
    have h2 : ∑ j, adj (𝕜 := ℝ) G i₀ j * v j
        ≤ ∑ j, adj (𝕜 := ℝ) G i₀ j * v i₀ :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvi j) (hnn i₀ j)
    have h3 : ∑ j, adj (𝕜 := ℝ) G i₀ j * v i₀ = v i₀ * (valency G i₀ : ℝ) := by
      rw [← Finset.sum_mul, sum_adj_eq_valency, mul_comm]
    have h4 : θ ≤ (valency G i₀ : ℝ) := by
      have h5 : θ * v i₀ ≤ v i₀ * (valency G i₀ : ℝ) := by
        rw [h1]
        calc ∑ j, adj (𝕜 := ℝ) G i₀ j * v j
            ≤ ∑ j, adj (𝕜 := ℝ) G i₀ j * v i₀ := h2
          _ = v i₀ * (valency G i₀ : ℝ) := h3
      have h6 : (0:ℝ) < v i₀ := hvpos i₀
      nlinarith [h5, h6]
    calc θ ≤ (valency G i₀ : ℝ) := h4
      _ ≤ ((Finset.univ.sup fun x => valency G x : ℕ) : ℝ) := by
          exact_mod_cast Finset.le_sup (Finset.mem_univ i₀)

/-! ## The Perron–Frobenius theorem, parts (iii) and (iv) -/

private theorem aux_mul_apply_nonneg {C : Matrix X X ℝ} (hnn : ∀ i j, 0 ≤ C i j) (i j : X) :
    0 ≤ (C * C) i j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hnn i k) (hnn k j)

/-! ## The sign-change involution of a bipartition -/

/-- If `C` is bipartite then `-θ` is an eigenvalue whenever `θ` is: the sign
change `S` of a bipartition satisfies `S * C * S = -C` and `S * S = 1`. -/
private theorem exists_sign_neg_eigenvector {C : Matrix X X ℝ} (hbip : IsBipartiteMatrix C)
    {θ : ℝ} {v : X → ℝ} (hv : v ≠ 0) (heig : C *ᵥ v = θ • v) :
    ∃ w : X → ℝ, w ≠ 0 ∧ C *ᵥ w = (-θ) • w := by
  obtain ⟨Xp, Xm, hXpne, hXmne, hdisj, hunion, hp, hm⟩ := hbip
  set s : X → ℝ := fun i => if i ∈ Xp then 1 else -1 with hs
  have hmem : ∀ z : X, z ∈ Xp ∨ z ∈ Xm :=
    fun z => Finset.mem_union.mp (hunion ▸ Finset.mem_univ z)
  have hsne : ∀ i, s i ≠ 0 := by
    intro i
    by_cases h : i ∈ Xp
    · rw [hs]; simp [h]
    · rw [hs]; simp [h]
  set w : X → ℝ := fun i => s i * v i with hw
  have hwne : w ≠ 0 := by
    intro h0
    apply hv
    funext i
    have h1 := congrFun h0 i
    simp only [hw, Pi.zero_apply] at h1
    exact (mul_eq_zero.mp h1).resolve_left (hsne i)
  have hcross : ∀ i j : X, C i j * s j = -s i * C i j := by
    intro i j
    rcases hmem i with hi | hi <;> rcases hmem j with hj | hj
    · rw [hp i hi j hj]
      rw [hs]; simp [hi]
    · rw [hs]
      simp only
      rw [if_pos hi, if_neg (fun h => (Finset.disjoint_right.mp hdisj hj) h)]
      ring
    · rw [hs]
      simp only
      rw [if_neg (fun h => (Finset.disjoint_right.mp hdisj hi) h), if_pos hj]
      ring
    · rw [hm i hi j hj]
      rw [hs]; simp [hi]
  refine ⟨w, hwne, ?_⟩
  funext i
  have hvi : (C *ᵥ v) i = θ * v i := by
    rw [heig]
    simp
  calc (C *ᵥ w) i = ∑ j, C i j * w j := rfl
    _ = ∑ j, C i j * (s j * v j) := by simp only [hw]
    _ = ∑ j, (C i j * s j) * v j := by
          refine Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ j, (-s i * C i j) * v j := by
          refine Finset.sum_congr rfl fun j _ => by rw [hcross i j]
    _ = -s i * ∑ j, C i j * v j := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => by ring
    _ = -s i * (θ * v i) := by
          rw [show (∑ j, C i j * v j) = (C *ᵥ v) i from rfl, hvi]
    _ = (-θ) * (s i * v i) := by ring
    _ = ((-θ) • w) i := by simp [hw]

/-! ## The real eigenvalue set -/

/-- The set of real eigenvalues of a real matrix `C`. -/
private def eigSet (C : Matrix X X ℝ) : Set ℝ := {μ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u}

private theorem mem_eigSet_iff_charpoly {C : Matrix X X ℝ} {μ : ℝ} :
    μ ∈ eigSet C ↔ (C.charpoly).eval μ = 0 := by
  constructor
  · rintro ⟨u, hu, hCu⟩
    have h0 : ((Matrix.scalar X) μ - C) *ᵥ u = 0 := by
      rw [Matrix.sub_mulVec, Matrix.scalar_apply, Matrix.diagonal_const_mulVec, hCu, sub_self]
    have hdet : ((Matrix.scalar X) μ - C).det = 0 := Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, h0⟩
    rw [Matrix.eval_charpoly]
    exact hdet
  · intro h
    have hdet : ((Matrix.scalar X) μ - C).det = 0 := by
      rw [← Matrix.eval_charpoly]
      exact h
    obtain ⟨u, hu, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨u, hu, ?_⟩
    have h1 : ((Matrix.scalar X) μ) *ᵥ u - C *ᵥ u = 0 := by
      rw [← Matrix.sub_mulVec]
      exact h0
    rw [Matrix.scalar_apply, Matrix.diagonal_const_mulVec] at h1
    exact (sub_eq_zero.mp h1).symm

private theorem mem_eigFinset {C : Matrix X X ℝ} {μ : ℝ} :
    μ ∈ C.charpoly.roots.toFinset ↔ μ ∈ eigSet C := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (Matrix.charpoly_monic C).ne_zero,
    mem_eigSet_iff_charpoly]
  exact Iff.rfl

private theorem eigSet_finite (C : Matrix X X ℝ) : (eigSet C).Finite :=
  (Polynomial.finite_setOfPred_isRoot (Matrix.charpoly_monic C).ne_zero).subset
    fun μ hμ => mem_eigSet_iff_charpoly.mp hμ

/-! ## The smallest eigenvalue is at least minus the Perron root -/

/-- Every eigenvalue of a nonnegative symmetric matrix with Perron data `(v, θ₀)`
has `|μ| ≤ θ₀`. -/
private theorem abs_eigenvalue_le_quad {C : Matrix X X ℝ} (hsym : Cᵀ = C) (hnn : ∀ i j, 0 ≤ C i j)
    {v : X → ℝ} (hvK : v ∈ K X) (hvmax : ∀ u ∈ K X, quad C u ≤ quad C v)
    (hvpos : ∀ i, 0 < v i) {u : X → ℝ} (hu : u ≠ 0) {μ : ℝ}
    (heig : C *ᵥ u = μ • u) : |μ| ≤ quad C v := by
  set x : X → ℝ := fun j => |u j| with hx
  have hx0 : ∀ i, 0 ≤ x i := fun i => abs_nonneg _
  have hxne : x ≠ 0 := by
    intro h0
    apply hu
    funext i
    have h1 := congrFun h0 i
    simp only [hx, Pi.zero_apply] at h1
    exact abs_eq_zero.mp h1
  have h1 : ∀ i, |μ| * x i ≤ (C *ᵥ x) i := by
    intro i
    have h2 := mulVec_abs_le hnn u i
    have h3 : (C *ᵥ u) i = μ * u i := by
      rw [heig]
      simp
    rw [h3, abs_mul] at h2
    exact h2
  have hxx : 0 < x ⬝ᵥ x := by
    rw [dotProduct]
    refine Finset.sum_pos' (fun i _ => mul_nonneg (hx0 i) (hx0 i)) ?_
    have hex : ∃ i, x i ≠ 0 := by
      by_contra h
      push Not at h
      exact hxne (funext h)
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩
  have h2 : |μ| * (x ⬝ᵥ x) ≤ quad C x := by
    rw [quad, dotProduct, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |μ| * (x i * x i) = x i * (|μ| * x i) := by ring
      _ ≤ x i * (C *ᵥ x) i := mul_le_mul_of_nonneg_left (h1 i) (hx0 i)
  have h3 : quad C x ≤ quad C v * (x ⬝ᵥ x) := by
    have hcpos : 0 < (Real.sqrt (x ⬝ᵥ x))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hxx)
    have hcK : (Real.sqrt (x ⬝ᵥ x))⁻¹ • x ∈ K X := by
      refine ⟨fun i => mul_nonneg hcpos.le (hx0 i), ?_⟩
      rw [dotProduct_smul_smul, inv_pow, Real.sq_sqrt hxx.le, inv_mul_cancel₀ hxx.ne']
    have hmax := hvmax _ hcK
    rw [quad_smul, inv_pow, Real.sq_sqrt hxx.le] at hmax
    calc quad C x = (x ⬝ᵥ x) * ((x ⬝ᵥ x)⁻¹ * quad C x) := by
          rw [← mul_assoc, mul_inv_cancel₀ hxx.ne', one_mul]
      _ ≤ (x ⬝ᵥ x) * quad C v := mul_le_mul_of_nonneg_left hmax hxx.le
      _ = quad C v * (x ⬝ᵥ x) := by rw [mul_comm]
  have h4 : |μ| * (x ⬝ᵥ x) ≤ quad C v * (x ⬝ᵥ x) := le_trans h2 h3
  exact le_of_mul_le_mul_right h4 hxx

/-! ## Uniqueness of the eigenvector for a positive eigenvalue -/

/-- A symmetric nonnegative irreducible matrix has a one-dimensional eigenspace
for every positive eigenvalue admitting a strictly positive eigenvector. -/
private theorem eigenvector_unique_of_pos [Nonempty X] {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hnn : ∀ i j, 0 ≤ C i j) (hirr : IsIrreducibleMatrix C) {lam : ℝ} (hlam : 0 < lam)
    {v : X → ℝ} (hvpos : ∀ i, 0 < v i) (hveig : C *ᵥ v = lam • v)
    {u : X → ℝ} (heig : C *ᵥ u = lam • u) : ∃ c : ℝ, u = c • v := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, by simp⟩
  have habsu : ∀ i, |(C *ᵥ u) i| = lam * |u i| := by
    intro i
    rw [heig, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hlam]
  have hpoint : ∀ i, lam * |u i| ≤ (C *ᵥ (fun j => |u j|)) i := by
    intro i
    rw [← habsu i]
    exact mulVec_abs_le hnn u i
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image (Finset.univ : Finset X)
    (fun i => |u i| / v i) ⟨Classical.arbitrary X, Finset.mem_univ _⟩
  set M : ℝ := |u j₀| / v j₀ with hM
  have hMle : ∀ i, |u i| / v i ≤ M := fun i => hj₀ i (Finset.mem_univ i)
  have hMv : ∀ i, |u i| ≤ M * v i := by
    intro i
    have h1 := hMle i
    rw [div_le_iff₀ (hvpos i)] at h1
    linarith
  have hMvj : |u j₀| = M * v j₀ := by
    rw [hM]; exact (div_mul_cancel₀ _ (ne_of_gt (hvpos j₀))).symm
  have hy : (fun i => M * v i - |u i|) = 0 := by
    refine eq_zero_of_mulVec_le hsym hnn hirr hlam (fun i => sub_nonneg.mpr (hMv i))
      (fun i => ?_) (i₀ := j₀) (by beta_reduce; rw [hMvj]; ring)
    have h1 : (C *ᵥ (fun i => M * v i - 1 * |u i|)) i
        = M * (C *ᵥ v) i - 1 * (C *ᵥ (fun j => |u j|)) i := mulVec_lin_apply
    have h2 : (fun i => M * v i - 1 * |u i|) = (fun i => M * v i - |u i|) := by
      funext k; ring_nf
    rw [← h2, h1, hveig]
    simp only [Pi.smul_apply, smul_eq_mul]
    linarith [hpoint i]
  have habs : (fun i => |u i|) = M • v := by
    funext i
    have h1 := congrFun hy i
    simp only [Pi.sub_apply, Pi.zero_apply] at h1
    rw [Pi.smul_apply, smul_eq_mul]
    linarith
  have hcw : C *ᵥ (fun j => |u j|) = lam • (fun j => |u j|) := by
    rw [habs, Matrix.mulVec_smul, hveig, smul_smul, smul_smul, mul_comm]
  by_cases hsign : ∃ j, 0 ≤ u j
  · rcases hsign with ⟨j, hj⟩
    refine ⟨M, ?_⟩
    have hZu : (fun i => |u i| - u i) = 0 := by
      refine eq_zero_of_mulVec_le hsym hnn hirr hlam
        (fun i => sub_nonneg.mpr (le_abs_self _)) (fun i => ?_) (i₀ := j) ?_
      · have h2 : (C *ᵥ (fun i => 1 * (fun j => |u j|) i - 1 * u i)) i
            = 1 * (C *ᵥ (fun j => |u j|)) i - 1 * (C *ᵥ u) i := mulVec_lin_apply
        have h3 : (fun i => 1 * |u i| - 1 * u i) = (fun i => |u i| - u i) := by
          funext k; ring_nf
        rw [← h3, h2, hcw, heig]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        linarith
      · beta_reduce
        rw [abs_of_nonneg hj]; ring
    funext i
    have h1 := congrFun hZu i
    have h2 := congrFun habs i
    simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
    linarith
  · push Not at hsign
    refine ⟨-M, ?_⟩
    funext i
    have h1 : u i < 0 := hsign i
    have h2 : |u i| = -u i := abs_of_neg h1
    have h3 := congrFun habs i
    simp only [Pi.smul_apply, smul_eq_mul] at h3
    rw [Pi.smul_apply, smul_eq_mul]
    linarith


/-! ## Theorem 2.4 (iii) and (iv) -/

/-- **Theorem 2.4 (iii) and (iv).**

The minimal eigenvalue `θr` satisfies `θr ≥ -θ₀`, with equality exactly when `C`
is bipartite.  (Restated from the previous draft with `hC0 : C ≠ 0`: the 1×1 zero
matrix makes the old statement false — `θr = -θ₀` holds there but a singleton
cannot be bipartite.) -/
theorem perron_frobenius_min [Nonempty X] (C : Matrix X X ℝ)
    (hsym : Cᵀ = C) (hirr : IsIrreducibleMatrix C) (hnn : ∀ i j, 0 ≤ C i j)
    (hC0 : C ≠ 0) :
    ∃ θ₀ θr : ℝ, θ₀ = sSup {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} ∧
      θr = sInf {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} ∧
      -θ₀ ≤ θr ∧ (θr = -θ₀ ↔ IsBipartiteMatrix C) := by
  obtain ⟨v, hvK, hvmax⟩ := exists_maximizer (Fintype.card_pos_iff.mpr inferInstance) C
  have hvpos : ∀ i, 0 < v i := maximizer_pos hsym hnn hvK hvmax hirr
  have hθpos : 0 < quad C v := quad_pos_of_ne_zero hnn hC0 hvpos
  have hveig : C *ᵥ v = quad C v • v := maximizer_eigen hsym hvK hvmax hvpos
  have hvne : v ≠ 0 := by
    intro h0
    have h1 := hvpos (Classical.arbitrary X)
    rw [h0] at h1
    simp at h1
  have hvmem : v ∈ K X := hvK
  -- the Perron root is the greatest eigenvalue
  have hgreat : IsGreatest (eigSet C) (quad C v) :=
    ⟨⟨v, hvne, hveig⟩, fun μ hμ => by
      obtain ⟨u, hu, hCu⟩ := hμ
      exact eigenvalue_le_quad hsym hnn hvK hvmax hvpos hu hCu⟩
  have hsup : quad C v = sSup (eigSet C) := hgreat.csSup_eq.symm
  -- the least eigenvalue exists
  have hne : (C.charpoly.roots.toFinset).Nonempty :=
    ⟨quad C v, mem_eigFinset.mpr ⟨v, hvne, hveig⟩⟩
  set θr : ℝ := (C.charpoly.roots.toFinset).min' hne with hθr
  have hmemθr : θr ∈ eigSet C := by
    rw [hθr]
    exact mem_eigFinset.mp (Finset.min'_mem _ _)
  have hleast : IsLeast (eigSet C) θr :=
    ⟨hmemθr, fun μ hμ => by
      rw [hθr]
      exact Finset.min'_le _ _ (mem_eigFinset.mpr hμ)⟩
  have hinf : θr = sInf (eigSet C) := hleast.csInf_eq.symm
  -- and it is at least `-θ₀`
  have hge : -quad C v ≤ θr := by
    obtain ⟨u, hu, hCu⟩ := hmemθr
    have h := abs_eigenvalue_le_quad hsym hnn hvK hvmax hvpos hu hCu
    have h2 := abs_le.mp h
    linarith [h2.1]
  refine ⟨quad C v, θr, hsup, hinf, hge, ?_⟩
  constructor
  · -- `θr = -θ₀` forces `C` bipartite: the eigenvectors of `θ₀` and `-θ₀` are
    -- both `θ₀²`-eigenvectors of `C * C`, which therefore has a repeated eigenvalue
    intro heq
    obtain ⟨u, hu, hCu⟩ := heq ▸ hmemθr
    have hBsym : (C * C)ᵀ = C * C := by rw [Matrix.transpose_mul, hsym]
    have hBnn : ∀ i j, 0 ≤ (C * C) i j := aux_mul_apply_nonneg hnn
    have hBv : (C * C) *ᵥ v = (quad C v * quad C v) • v := by
      rw [← Matrix.mulVec_mulVec, hveig, Matrix.mulVec_smul, hveig, smul_smul]
    have hBu : (C * C) *ᵥ u = (quad C v * quad C v) • u := by
      rw [← Matrix.mulVec_mulVec, hCu, Matrix.mulVec_smul, hCu, smul_smul]
      ring_nf
    by_cases hBirr : IsIrreducibleMatrix (C * C)
    · exfalso
      obtain ⟨c', hc'⟩ :=
        eigenvector_unique_of_pos hBsym hBnn hBirr (mul_pos hθpos hθpos) hvpos hBv hBu
      have hc'ne : c' ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc'
        exact hu hc'
      -- but `C u = -θ₀ u` and `C u = c' θ₀ v` are incompatible
      have h2 : C *ᵥ u = ((-quad C v) * c') • v := by
        rw [hCu, hc', smul_smul]
      have h3 : C *ᵥ u = (c' * quad C v) • v := by
        rw [hc', Matrix.mulVec_smul, hveig, smul_smul]
      have h4 : (c' * quad C v) • v = ((-quad C v) * c') • v := by rw [← h3, h2]
      have h5 := congrFun h4 (Classical.arbitrary X)
      simp only [Pi.smul_apply, smul_eq_mul] at h5
      have h6 := hvpos (Classical.arbitrary X)
      have h7 : (c' * quad C v - (-quad C v) * c') * v (Classical.arbitrary X) = 0 := by
        nlinarith [h5]
      have h8 : c' * quad C v - (-quad C v) * c' = 0 := by
        rcases mul_eq_zero.mp h7 with h | h
        · exact h
        · exact absurd h (ne_of_gt h6)
      have h9 : c' * quad C v = 0 := by linarith [h8]
      rcases mul_eq_zero.mp h9 with h | h
      · exact hc'ne h
      · exact absurd h (ne_of_gt hθpos)
    · exact isBipartiteMatrix_of_sq_reducible hsym hirr hnn (not_not.mp hBirr)
  · -- a bipartition flips the sign of the Perron eigenvector
    intro hbip
    obtain ⟨w, hwne, hweig⟩ := exists_sign_neg_eigenvector hbip hvne hveig
    have hle : θr ≤ -quad C v := by
      rw [hθr]
      exact Finset.min'_le _ _ (mem_eigFinset.mpr ⟨w, hwne, hweig⟩)
    linarith

end Terwilliger
