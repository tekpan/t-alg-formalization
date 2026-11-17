/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.Basic
import Terwilliger.Hermitian
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
# The Perron–Frobenius theorem (Chapter 2)

Chapter 2 of Terwilliger's notes.  Nothing here uses the graph structure: this is
linear algebra over `ℝ`.

**Theorem 2.4 (i), (ii)** is proved in `Terwilliger/CollatzWielandt.lean` as
`Terwilliger.perron_frobenius`, by the Collatz–Wielandt method.

**Lemma 2.3** (`posSemidef_exists_dotProduct`) is proved below, in the Section H2
block of the spectral-theorem campaign, from Mathlib's spectral theorem for
Hermitian matrices (`Mathlib/Analysis/Matrix/Spectrum.lean`:
`Matrix.IsHermitian.eigenvectorBasis`, `.eigenvalues`, `.spectral_theorem`,
`Matrix.PosSemidef.eigenvalues_nonneg`).  **Theorem 2.4 (iii), (iv)** is left
for Section H4 of that campaign.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

/-! ## Reducible and bipartite matrices (Definitions 2.1, 2.2) -/

/-- **Definition 2.1.** A matrix is reducible if its index set admits a partition
into two nonempty parts with all cross entries zero. -/
def IsReducibleMatrix {X : Type*} [Fintype X] [DecidableEq X] (C : Matrix X X ℝ) : Prop :=
  ∃ Xp Xm : Finset X, Xp.Nonempty ∧ Xm.Nonempty ∧ Disjoint Xp Xm ∧
    Xp ∪ Xm = Finset.univ ∧ (∀ i ∈ Xp, ∀ j ∈ Xm, C i j = 0) ∧
      (∀ i ∈ Xm, ∀ j ∈ Xp, C i j = 0)

/-- **Definition 2.2.** A matrix is bipartite if its index set admits a partition
into two nonempty parts with both diagonal blocks zero. -/
def IsBipartiteMatrix {X : Type*} [Fintype X] [DecidableEq X] (C : Matrix X X ℝ) : Prop :=
  ∃ Xp Xm : Finset X, Xp.Nonempty ∧ Xm.Nonempty ∧ Disjoint Xp Xm ∧
    Xp ∪ Xm = Finset.univ ∧ (∀ i ∈ Xp, ∀ j ∈ Xp, C i j = 0) ∧
      (∀ i ∈ Xm, ∀ j ∈ Xm, C i j = 0)

/-- A matrix is irreducible when it is not reducible. -/
def IsIrreducibleMatrix {X : Type*} [Fintype X] [DecidableEq X] (C : Matrix X X ℝ) : Prop :=
  ¬ IsReducibleMatrix C

/-- If `C` is bipartite then `C²` is reducible (note 2 of Chapter 2). -/
theorem isReducibleMatrix_sq_of_isBipartiteMatrix {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ}
    (h : IsBipartiteMatrix C) : IsReducibleMatrix (C * C) := by
  obtain ⟨Xp, Xm, hne, hne', hdisj, hunion, hp, hm⟩ := h
  refine ⟨Xp, Xm, hne, hne', hdisj, hunion, ?_, ?_⟩
  · intro i hi j hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ Xp
    · rw [hp i hi k hk, zero_mul]
    · have hk' : k ∈ Xm := by
        have := Finset.mem_union.mp (hunion ▸ Finset.mem_univ k)
        exact this.resolve_left (fun h' => hk h')
      rw [hm k hk' j hj, mul_zero]
  · intro i hi j hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ Xm
    · rw [hm i hi k hk, zero_mul]
    · have hk' : k ∈ Xp := by
        have := Finset.mem_union.mp (hunion ▸ Finset.mem_univ k)
        exact this.resolve_right (fun h' => hk h')
      rw [hp k hk' j hj, mul_zero]

/-- Over `ℝ` the coercion `RCLike.ofReal` is the identity. -/
theorem rclike_ofReal_real (r : ℝ) : RCLike.ofReal r = r := by
  simp

/-- If `s * s = x` then `x * (a * b) = (s * a) * (s * b)`; used to insert the
square root of a nonnegative eigenvalue. -/
theorem mul_self_mul_sq_factor {R : Type*} [CommRing R] {s x a b : R} (h : s * s = x) :
    x * (a * b) = (s * a) * (s * b) := by
  rw [← h]; ring

/-- **Spectral expansion, entrywise.**  A Hermitian real matrix `B` is
`∑ k, λ k • (u k ⊗ u kᵀ)`, where `λ` are its eigenvalues and `u` an orthonormal
eigenbasis. -/
theorem hermitian_entry_sum_eigenvalues {X : Type*} [Fintype X] [DecidableEq X]
    {B : Matrix X X ℝ} (hH : B.IsHermitian) (i j : X) :
    B i j = ∑ k, hH.eigenvalues k *
      ((hH.eigenvectorBasis k).ofLp i * (hH.eigenvectorBasis k).ofLp j) := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  have hU : ∀ a b : X, (↑hH.eigenvectorUnitary : Matrix X X ℝ) a b
      = (hH.eigenvectorBasis b).ofLp a := fun a b =>
    Matrix.IsHermitian.eigenvectorUnitary_apply hH a b
  rw [Matrix.star_apply, hU i k, hU j k, star_trivial, Function.comp_apply, rclike_ofReal_real]
  ring

/-- **Real eigenvectors for real eigenvalues.**  A real eigenvalue of a real
matrix has a real eigenvector: the real and imaginary parts of a complex
eigenvector are themselves eigenvectors, and one of them is nonzero.
(The symmetry hypothesis `hsym` is not needed for this and is kept only because
it is part of the statement recorded in the campaign's spec.) -/
theorem exists_real_eigenvector {X : Type*} [Fintype X] [DecidableEq X]
    {B : Matrix X X ℝ} (hsym : Bᵀ = B) {θ : ℝ}
    (hθ : ∃ w : X → ℂ, w ≠ 0 ∧ (B.map (algebraMap ℝ ℂ)) *ᵥ w = (θ : ℂ) • w) :
    ∃ v : X → ℝ, v ≠ 0 ∧ B *ᵥ v = θ • v := by
  classical
  obtain ⟨w, hw, hAw⟩ := hθ
  -- coordinatewise, the real and imaginary parts of `w` are `θ`-eigenvectors of `B`
  have hcoord : ∀ i, (∑ j, ((B i j : ℝ) : ℂ) * w j) = ((θ : ℝ) : ℂ) * w i := by
    intro i
    have h := congrFun hAw i
    simpa [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul] using h
  have hre : ∀ i, ∑ j, B i j * (w j).re = θ * (w i).re := by
    intro i
    have h := congrArg Complex.re (hcoord i)
    rw [Complex.re_sum] at h
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero, zero_mul] at h
    exact h
  have him : ∀ i, ∑ j, B i j * (w j).im = θ * (w i).im := by
    intro i
    have h := congrArg Complex.im (hcoord i)
    rw [Complex.im_sum] at h
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] at h
    exact h
  have hsplit : (fun i => (w i).re) ≠ 0 ∨ (fun i => (w i).im) ≠ 0 := by
    by_contra h
    push Not at h
    obtain ⟨h1, h2⟩ := h
    apply hw
    funext i
    exact Complex.ext (by simpa using congrFun h1 i) (by simpa using congrFun h2 i)
  rcases hsplit with hre0 | him0
  · refine ⟨fun j => (w j).re, hre0, ?_⟩
    funext j
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using hre j
  · refine ⟨fun j => (w j).im, him0, ?_⟩
    funext j
    simpa [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using him j

/-! ## Positive semidefinite matrices are Gram matrices -/

/-- **Lemma 2.3.** A positive semidefinite real matrix is a Gram matrix.

Proof: Mathlib's spectral theorem for Hermitian matrices
(`Matrix.IsHermitian.spectral_theorem`, in `Mathlib/Analysis/Matrix/Spectrum.lean`)
writes `B = U * diagonal λ * Uᵀ` with `U` unitary and `λ` the real eigenvalues, so
entrywise `B i j = ∑ k, λ k * u k i * u k j` where `u k` is the orthonormal
eigenbasis (`hermitian_entry_sum_eigenvalues`).  For `B` positive semidefinite
`λ k ≥ 0`, hence `λ k = √(λ k) * √(λ k)` and `v i := fun k => √(λ k) * u k i`
gives `B i j = v i ⬝ᵥ v j`. -/
theorem posSemidef_exists_dotProduct {n : ℕ} {B : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) :
    ∃ v : Fin n → Fin n → ℝ, ∀ i j, B i j = v i ⬝ᵥ v j := by
  classical
  have hH : B.IsHermitian := hB.1
  have hnn : ∀ k, 0 ≤ hH.eigenvalues k :=
    fun k => (Matrix.IsHermitian.posSemidef_iff_eigenvalues_nonneg hH).mp hB k
  refine ⟨fun i k => Real.sqrt (hH.eigenvalues k) * (hH.eigenvectorBasis k).ofLp i, ?_⟩
  intro i j
  rw [hermitian_entry_sum_eigenvalues hH i j]
  show (∑ k, hH.eigenvalues k *
      ((hH.eigenvectorBasis k).ofLp i * (hH.eigenvectorBasis k).ofLp j)) =
    ∑ k, (Real.sqrt (hH.eigenvalues k) * (hH.eigenvectorBasis k).ofLp i) *
      (Real.sqrt (hH.eigenvalues k) * (hH.eigenvectorBasis k).ofLp j)
  refine Finset.sum_congr rfl fun k _ => ?_
  exact mul_self_mul_sq_factor (Real.mul_self_sqrt (hnn k))

/-! ## The Perron–Frobenius theorem -/

/- Theorem 2.4 (i), (ii) is proved in `Terwilliger/CollatzWielandt.lean` as
`Terwilliger.perron_frobenius` -/

/- **Theorem 2.4 (iii) and (iv)** is proved in `Terwilliger/CollatzWielandt.lean`
as `Terwilliger.perron_frobenius_min`: the Collatz–Wielandt maximiser those proofs
use lives in that file, which imports this one. -/
/- Corollary 2.5 (Lemma 1.2 of Chapter 1) is proved in
`Terwilliger/CollatzWielandt.lean` as `largest_eigenvalue_le_max_valency` and
`largest_eigenvalue_eq_valency`. -/

/-! ## Note 1 of Chapter 2 — a bipartite matrix has a spectrum symmetric about `0`

If `C` is bipartite with parts `Xp`, `Xm`, the diagonal matrix `S` that is `+1` on
`Xp` and `-1` on `Xm` is an involution satisfying `S * C * S = -C`.  Hence
`C *ᵥ v = θ • v` implies `C *ᵥ (S *ᵥ v) = (-θ) • (S *ᵥ v)`, so `θ ↦ -θ` preserves
the eigenvalue set: the eigenvalues of a bipartite symmetric matrix come in pairs
`θ, -θ`.  This is Note 1 of Chapter 2. -/

/-- The **sign-change involution** of the bipartition with positive part `Xp`: the
diagonal matrix that is `+1` on `Xp` and `-1` off `Xp`. -/
def signChange {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X) : Matrix X X ℝ :=
  Matrix.diagonal fun i => if i ∈ Xp then 1 else -1

theorem signChange_apply {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X) (i j : X) :
    signChange Xp i j = if i = j then (if i ∈ Xp then (1 : ℝ) else -1) else 0 := by
  rw [signChange, Matrix.diagonal_apply]

theorem signChange_transpose {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X) :
    (signChange Xp)ᵀ = signChange Xp := by
  rw [signChange, Matrix.diagonal_transpose]

theorem signChange_mul_self {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X) :
    signChange Xp * signChange Xp = 1 := by
  rw [signChange, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1 with i
  by_cases h : i ∈ Xp <;> simp [h]

theorem signChange_mulVec {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X)
    (u : X → ℝ) :
    signChange Xp *ᵥ u = fun i => (if i ∈ Xp then (1 : ℝ) else -1) * u i := by
  funext i
  rw [signChange, Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply, if_pos rfl]
  · intro j _ hj
    rw [Matrix.diagonal_apply, if_neg (Ne.symm hj), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem signChange_mulVec_mulVec {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X)
    (u : X → ℝ) : signChange Xp *ᵥ (signChange Xp *ᵥ u) = u := by
  rw [Matrix.mulVec_mulVec, signChange_mul_self, Matrix.one_mulVec]

theorem signChange_mulVec_ne_zero {X : Type*} [Fintype X] [DecidableEq X] (Xp : Finset X)
    {u : X → ℝ} (hu : u ≠ 0) : signChange Xp *ᵥ u ≠ 0 := by
  intro h
  rw [← signChange_mulVec_mulVec Xp u, h, Matrix.mulVec_zero] at hu
  exact hu rfl

/-- The sign-change involution conjugates a bipartite matrix to its negative. -/
theorem signChange_conj_of_bipartite {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} {Xp Xm : Finset X} (hdisj : Disjoint Xp Xm)
    (hunion : Xp ∪ Xm = Finset.univ) (hp : ∀ i ∈ Xp, ∀ j ∈ Xp, C i j = 0)
    (hm : ∀ i ∈ Xm, ∀ j ∈ Xm, C i j = 0) :
    signChange Xp * C * signChange Xp = -C := by
  have hmem : ∀ i : X, i ∈ Xp ∨ i ∈ Xm := by
    intro i
    have h : i ∈ Xp ∪ Xm := hunion ▸ Finset.mem_univ i
    exact Finset.mem_union.mp h
  have hni : ∀ {i : X}, i ∈ Xm → i ∉ Xp := fun hi => Finset.disjoint_right.mp hdisj hi
  ext i j
  rw [signChange, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply]
  rcases hmem i with hi | hi <;> rcases hmem j with hj | hj
  · rw [if_pos hi, if_pos hj, hp i hi j hj]; ring
  · rw [if_pos hi, if_neg (hni hj)]; ring
  · rw [if_neg (hni hi), if_pos hj]; ring
  · rw [if_neg (hni hi), if_neg (hni hj), hm i hi j hj]; ring

/-- On vectors, the sign change **anticommutes** with a bipartite matrix:
`C *ᵥ (S *ᵥ u) = -(S *ᵥ (C *ᵥ u))`. -/
theorem mulVec_signChange_of_bipartite {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} {Xp Xm : Finset X} (hdisj : Disjoint Xp Xm)
    (hunion : Xp ∪ Xm = Finset.univ) (hp : ∀ i ∈ Xp, ∀ j ∈ Xp, C i j = 0)
    (hm : ∀ i ∈ Xm, ∀ j ∈ Xm, C i j = 0) (u : X → ℝ) :
    C *ᵥ (signChange Xp *ᵥ u) = -(signChange Xp *ᵥ (C *ᵥ u)) := by
  have hmem : ∀ i : X, i ∈ Xp ∨ i ∈ Xm := by
    intro i
    have h : i ∈ Xp ∪ Xm := hunion ▸ Finset.mem_univ i
    exact Finset.mem_union.mp h
  have hni : ∀ {i : X}, i ∈ Xm → i ∉ Xp := fun hi => Finset.disjoint_right.mp hdisj hi
  funext i
  have hkey : ∀ j : X, C i j * ((if j ∈ Xp then (1 : ℝ) else -1) * u j)
      = -((if i ∈ Xp then (1 : ℝ) else -1) * (C i j * u j)) := by
    intro j
    rcases hmem i with hi | hi <;> rcases hmem j with hj | hj
    · rw [if_pos hi, if_pos hj, hp i hi j hj]; ring
    · rw [if_pos hi, if_neg (hni hj)]; ring
    · rw [if_neg (hni hi), if_pos hj]; ring
    · rw [if_neg (hni hi), if_neg (hni hj), hm i hi j hj]; ring
  have hL : (C *ᵥ (signChange Xp *ᵥ u)) i
      = ∑ j, C i j * ((if j ∈ Xp then (1 : ℝ) else -1) * u j) := by
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => by rw [signChange_mulVec]
  have hR : (-(signChange Xp *ᵥ (C *ᵥ u))) i
      = -((if i ∈ Xp then (1 : ℝ) else -1) * ∑ j, C i j * u j) := by
    simp only [Pi.neg_apply, signChange_mulVec, Matrix.mulVec, dotProduct]
  rw [hL, hR]
  have hsum : (∑ j, C i j * ((if j ∈ Xp then (1 : ℝ) else -1) * u j))
      = -((if i ∈ Xp then (1 : ℝ) else -1) * ∑ j, C i j * u j) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hkey j
  exact hsum

/-- A bipartite matrix is conjugated to its negative by a sign-change involution. -/
theorem exists_signChange_conj_neg_of_bipartite {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} (hbip : IsBipartiteMatrix C) :
    ∃ S : Matrix X X ℝ, S * S = 1 ∧ Sᵀ = S ∧ S * C * S = -C ∧
      ∀ u : X → ℝ, S *ᵥ (S *ᵥ u) = u := by
  obtain ⟨Xp, Xm, -, -, hdisj, hunion, hp, hm⟩ := hbip
  exact ⟨signChange Xp, signChange_mul_self Xp, signChange_transpose Xp,
    signChange_conj_of_bipartite hdisj hunion hp hm,
    signChange_mulVec_mulVec Xp⟩

/-- **Note 1 of Chapter 2.**  If `C` is bipartite then the map `θ ↦ -θ`
preserves the eigenvalue set, via the sign-change involution `S`. -/
theorem eigenvalue_neg_of_bipartite {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} (hsym : Cᵀ = C) (hbip : IsBipartiteMatrix C) :
    ∀ θ : ℝ, (∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = θ • u) ↔
      ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = (-θ) • u := by
  obtain ⟨Xp, Xm, -, -, hdisj, hunion, hp, hm⟩ := hbip
  have hstep : ∀ (θ : ℝ) (u : X → ℝ), u ≠ 0 → C *ᵥ u = θ • u →
      ∃ w : X → ℝ, w ≠ 0 ∧ C *ᵥ w = (-θ) • w := by
    intro θ u hu hCu
    refine ⟨signChange Xp *ᵥ u, signChange_mulVec_ne_zero Xp hu, ?_⟩
    rw [mulVec_signChange_of_bipartite hdisj hunion hp hm u, hCu, Matrix.mulVec_smul,
      neg_smul]
  intro θ
  constructor
  · rintro ⟨u, hu, hCu⟩
    exact hstep θ u hu hCu
  · rintro ⟨u, hu, hCu⟩
    simpa using hstep (-θ) u hu hCu

/-- **Note 1 of Chapter 2, extremal form.**  For a bipartite symmetric matrix the
eigenvalue set is symmetric about `0`, so the minimal eigenvalue is the negative of
the maximal one. -/
theorem sInf_eigenvalue_eq_neg_sSup_of_bipartite {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} (hsym : Cᵀ = C) (hbip : IsBipartiteMatrix C) :
    sInf {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u}
      = -sSup {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} := by
  have hT : -{μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u}
      = {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} := by
    ext x
    rw [Set.mem_neg]
    exact (eigenvalue_neg_of_bipartite hsym hbip x).symm
  have hneg : sInf (-{μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u})
      = sInf {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} := by rw [hT]
  calc sInf {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u}
      = sInf (-{μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u}) := hneg.symm
    _ = -sSup {μ : ℝ | ∃ u : X → ℝ, u ≠ 0 ∧ C *ᵥ u = μ • u} := Real.sInf_neg _

/-! ## A helper for Theorem 2.4 (iii): eigenvectors for distinct eigenvalues of a
symmetric matrix are orthogonal.  (Elementary; delete if the merged file already has
it under another name.) -/

/-- Eigenvectors of a real symmetric matrix for distinct eigenvalues are orthogonal. -/
theorem dotProduct_eq_zero_of_eigenvector_ne {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} (hsym : Cᵀ = C) {θ μ : ℝ} (hθμ : θ ≠ μ) {u v : X → ℝ}
    (hu : C *ᵥ u = θ • u) (hv : C *ᵥ v = μ • v) : u ⬝ᵥ v = 0 := by
  have hsymm_entry : ∀ i j : X, C i j = C j i := by
    intro i j
    have h := congrFun (congrFun hsym i) j
    simp only [Matrix.transpose_apply] at h
    exact h.symm
  have hsymm : ∀ a b : X → ℝ, (C *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (C *ᵥ b) := by
    intro a b
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hsymm_entry]
    ring
  have h1 : θ • (u ⬝ᵥ v) = (C *ᵥ u) ⬝ᵥ v := by
    rw [← smul_dotProduct, ← hu]
  have h2 : (C *ᵥ u) ⬝ᵥ v = u ⬝ᵥ (C *ᵥ v) := hsymm u v
  have h3 : u ⬝ᵥ (C *ᵥ v) = u ⬝ᵥ (μ • v) := by rw [hv]
  have h4 : u ⬝ᵥ (μ • v) = μ • (u ⬝ᵥ v) := by rw [dotProduct_smul]
  have hkey : θ • (u ⬝ᵥ v) = μ • (u ⬝ᵥ v) := h1.trans (h2.trans (h3.trans h4))
  have h0 : θ * (u ⬝ᵥ v) = μ * (u ⬝ᵥ v) := by
    simpa [smul_eq_mul] using hkey
  have h5 : (θ - μ) * (u ⬝ᵥ v) = 0 := by
    rw [sub_mul, sub_eq_zero]
    exact h0
  rcases mul_eq_zero.mp h5 with h | h
  · exact absurd (sub_eq_zero.mp h) hθμ
  · exact h

/-- Eigenvectors of a symmetric matrix for distinct eigenvalues are linearly
independent: if `a • u + b • v = 0` then `a = b = 0`. -/
theorem smul_add_smul_eq_zero_of_eigenvector_ne {X : Type*} [Fintype X] [DecidableEq X]
    {C : Matrix X X ℝ} (hsym : Cᵀ = C) {θ μ : ℝ} (hθμ : θ ≠ μ) {u v : X → ℝ}
    (hu : u ≠ 0) (hv : v ≠ 0) (huC : C *ᵥ u = θ • u) (hvC : C *ᵥ v = μ • v)
    {a b : ℝ} (h : a • u + b • v = 0) : a = 0 ∧ b = 0 := by
  have horth : u ⬝ᵥ v = 0 := dotProduct_eq_zero_of_eigenvector_ne hsym hθμ huC hvC
  have huu : u ⬝ᵥ u ≠ 0 := by
    intro h0
    exact hu ((dotProduct_self_eq_zero).mp h0)
  have h1 : a * (u ⬝ᵥ u) = 0 := by
    have h' := congrArg (fun w => w ⬝ᵥ u) h
    simp only [add_dotProduct, smul_dotProduct, zero_dotProduct] at h'
    rw [dotProduct_comm v u, horth, smul_zero, add_zero] at h'
    simpa [smul_eq_mul] using h'
  have ha : a = 0 := by
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact h'
    · exact absurd h' huu
  have hb : b = 0 := by
    have h2 : b • v = 0 := by
      rw [ha, zero_smul, zero_add] at h
      exact h
    rcases smul_eq_zero.mp h2 with h' | h'
    · exact h'
    · exact absurd h' hv
  exact ⟨ha, hb⟩

/-! ## Note 3 of Chapter 2, converse direction -/

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Auxiliary: if `C * C` has zero entries across the partition `(Xp, Xm)`, then `C`
has no entries inside `Xp`. -/
private theorem aux_no_inner {C : Matrix X X ℝ} (hnn : ∀ i j, 0 ≤ C i j) (hsym : Cᵀ = C)
    (hirr : IsIrreducibleMatrix C) {Xp Xm : Finset X} (hXpne : Xp.Nonempty)
    (hXmne : Xm.Nonempty) (hdisj : Disjoint Xp Xm) (hunion : Xp ∪ Xm = Finset.univ)
    (hpm : ∀ i ∈ Xp, ∀ j ∈ Xm, (C * C) i j = 0) :
    ∀ i ∈ Xp, ∀ j ∈ Xp, C i j = 0 := by
  have hstep : ∀ u ∈ Xp, ∀ j ∈ Xm, ∀ k, C u k * C k j = 0 := by
    intro u hu j hj k
    have h1 : (C * C) u j = 0 := hpm u hu j hj
    rw [Matrix.mul_apply] at h1
    exact (Finset.sum_eq_zero_iff_of_nonneg (f := fun k => C u k * C k j)
      (fun k _ => mul_nonneg (hnn u k) (hnn k j))).mp h1 k (Finset.mem_univ k)
  intro u₀ hu₀ v₀ hv₀
  by_contra huv
  have hkey : ∀ j ∈ Xm, C v₀ j = 0 := by
    intro j hj
    rcases mul_eq_zero.mp (hstep u₀ hu₀ j hj v₀) with h | h
    · exact absurd h huv
    · exact h
  have hmem : ∀ z : X, z ∈ Xp ∨ z ∈ Xm := by
    intro z
    exact Finset.mem_union.mp (hunion ▸ Finset.mem_univ z)
  have hclosed : ∀ z, z ∈ Xp → (∀ j ∈ Xm, C z j = 0) → ∀ k, C z k ≠ 0 →
      (k ∈ Xp ∧ ∀ j ∈ Xm, C k j = 0) := by
    intro z hz hzf k hzk
    have hkXp : k ∈ Xp := by
      rcases hmem k with h | h
      · exact h
      · exact absurd (hzf k h) hzk
    refine ⟨hkXp, fun j hj => ?_⟩
    rcases mul_eq_zero.mp (hstep z hz j hj k) with h | h
    · exact absurd h hzk
    · exact h
  have hreach : ∀ z : X, Relation.ReflTransGen (fun i j => C i j ≠ 0) v₀ z := by
    intro z
    by_contra hz
    set S : Set X := {y | Relation.ReflTransGen (fun i j => C i j ≠ 0) v₀ y} with hSdef
    have hv₀S : v₀ ∈ S := Relation.ReflTransGen.refl
    have hzS : z ∉ S := hz
    refine hirr ⟨Finset.univ.filter (· ∈ S), Finset.univ.filter (· ∉ S), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨v₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv₀S⟩⟩
    · exact ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzS⟩⟩
    · rw [Finset.disjoint_left]
      intro i hi hi'
      exact (Finset.mem_filter.mp hi').2 (Finset.mem_filter.mp hi).2
    · ext i
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro _; trivial
      · intro _
        by_cases h : i ∈ S
        · exact Or.inl h
        · exact Or.inr h
    · intro i hi j hj
      have hiS : i ∈ S := (Finset.mem_filter.mp hi).2
      by_contra hne
      exact (Finset.mem_filter.mp hj).2 (Relation.ReflTransGen.tail hiS hne)
    · intro i hi j hj
      have hjS : j ∈ S := (Finset.mem_filter.mp hj).2
      have hiS : i ∉ S := (Finset.mem_filter.mp hi).2
      by_contra hne
      have hne' : C j i ≠ 0 := by
        intro h0
        exact hne (by rw [← hsym]; exact h0)
      exact hiS (Relation.ReflTransGen.tail hjS hne')
  have hgood : ∀ z, Relation.ReflTransGen (fun i j => C i j ≠ 0) v₀ z →
      (z ∈ Xp ∧ ∀ j ∈ Xm, C z j = 0) := by
    intro z hz
    induction hz with
    | refl => exact ⟨hv₀, hkey⟩
    | tail _ hbc ih => exact hclosed _ ih.1 ih.2 _ hbc
  obtain ⟨j₀, hj₀⟩ := hXmne
  exact (Finset.disjoint_right.mp hdisj hj₀) (hgood j₀ (hreach j₀)).1

/-- **Note 3 of Chapter 2 (converse direction).**  A symmetric nonnegative
irreducible matrix whose square is reducible is bipartite. -/
theorem isBipartiteMatrix_of_sq_reducible {C : Matrix X X ℝ} (hsym : Cᵀ = C)
    (hirr : IsIrreducibleMatrix C) (hnn : ∀ i j, 0 ≤ C i j)
    (hsq : IsReducibleMatrix (C * C)) : IsBipartiteMatrix C := by
  obtain ⟨Xp, Xm, hXpne, hXmne, hdisj, hunion, hpm, hmp⟩ := hsq
  refine ⟨Xp, Xm, hXpne, hXmne, hdisj, hunion, ?_, ?_⟩
  · exact aux_no_inner hnn hsym hirr hXpne hXmne hdisj hunion hpm
  · exact aux_no_inner hnn hsym hirr hXmne hXpne hdisj.symm
      (by rw [Finset.union_comm]; exact hunion) hmp

end Terwilliger
