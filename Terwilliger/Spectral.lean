/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.Hermitian

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
# The spectral projections of a self-adjoint matrix

For a self-adjoint matrix `A` over `ℂ` (in our application `A = adj G`) we build,
by hand, the spectral projections `E_θ` of `A`:

* `eigFinset A` is the set of roots of the characteristic polynomial of `A`
  (`=` the set of eigenvalues, `isEigenvalue_iff_mem_eigFinset`);
* eigenvalues of a self-adjoint matrix are real (`eigenvalue_real`);
* the squarefree product `eigPoly A = ∏_{θ ∈ eigFinset A}(X - θ)` annihilates `A`
  (`aeval_eigPoly_eq_zero`), proved by induction on the dimension of an
  `A`-stable subspace, splitting off an eigenvector through the orthogonal
  decomposition `exists_orthogonal_decomp`; from it we get the workhorse
  `aeval_eq_zero_of_forall_eval_eq_zero`: a polynomial that vanishes at every
  eigenvalue annihilates `A`;
* `spectralProj A θ` is the Lagrange interpolant `∏_{ψ ≠ θ}(A - ψ)/(θ - ψ)`, and
  the projections are pairwise orthogonal idempotents summing to `1`
  (`spectralProj_mul_self`, `spectralProj_mul_of_ne`, `sum_spectralProj`), are
  polynomials in `A` (`adj_mul_spectralProj`, `aeval_mul_spectralProj`), are
  self-adjoint (`star_spectralProj`) and act as the identity on the `θ`-eigenspace
  (`spectralProj_mulVec_eigenvector`).

Mathlib in this snapshot has no spectral theorem for Hermitian matrices, so
everything is proved from scratch; the only input from the Hermitian layer is the
orthogonal decomposition of the standard module.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Eigenvalues -/

/-- `θ` is an eigenvalue of `A`: some nonzero vector is mapped to `θ • v`. -/
def IsEigenvalue (A : Matrix X X ℂ) (θ : ℂ) : Prop :=
  ∃ v : X → ℂ, v ≠ 0 ∧ A *ᵥ v = θ • v

/-- The (distinct) eigenvalues of `A`: the roots of the characteristic polynomial. -/
def eigFinset (A : Matrix X X ℂ) : Finset ℂ := A.charpoly.roots.toFinset

theorem scalar_eq_smul_one (c : ℂ) : (Matrix.scalar X) c = c • (1 : Matrix X X ℂ) := by
  rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

theorem scalar_mulVec (c : ℂ) (v : X → ℂ) : (Matrix.scalar X) c *ᵥ v = c • v := by
  rw [scalar_eq_smul_one, smul_mulVec, one_mulVec]

theorem mem_eigFinset_iff {A : Matrix X X ℂ} {θ : ℂ} :
    θ ∈ eigFinset A ↔ A.charpoly.eval θ = 0 := by
  rw [eigFinset, Multiset.mem_toFinset,
    Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero, Polynomial.IsRoot.def]

theorem isEigenvalue_iff_mem_eigFinset' {A : Matrix X X ℂ} {θ : ℂ} :
    IsEigenvalue A θ ↔ θ ∈ eigFinset A := by
  rw [mem_eigFinset_iff, Matrix.eval_charpoly]
  constructor
  · rintro ⟨v, hvne, hv⟩
    have hsub : (Matrix.scalar X θ - A) *ᵥ v = 0 := by
      rw [sub_mulVec, hv, scalar_mulVec, sub_self]
    exact Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hvne, hsub⟩
  · intro hdet
    obtain ⟨v, hvne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    refine ⟨v, hvne, ?_⟩
    have h2 : (Matrix.scalar X θ) *ᵥ v - A *ᵥ v = 0 := by
      rw [← sub_mulVec]; exact hv
    rw [scalar_mulVec, sub_eq_zero] at h2
    exact h2.symm

theorem isEigenvalue_iff_mem_eigFinset {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ} :
    IsEigenvalue A θ ↔ θ ∈ eigFinset A :=
  isEigenvalue_iff_mem_eigFinset'

/-- Eigenvalues of a self-adjoint matrix are real. -/
theorem eigenvalue_real {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : IsEigenvalue A θ) : ∃ t : ℝ, θ = (t : ℂ) := by
  obtain ⟨v, hvne, hv⟩ := hθ
  have hpair : star v ⬝ᵥ v ≠ 0 := fun h => hvne (star_dotProduct_self_eq_zero h)
  have h1 : star v ⬝ᵥ (A *ᵥ v) = θ * (star v ⬝ᵥ v) := by
    rw [hv, dotProduct_smul, smul_eq_mul]
  have h2 : star v ⬝ᵥ (A *ᵥ v) = star θ * (star v ⬝ᵥ v) := by
    rw [star_mulVec_dotProduct, hA, hv, star_smul, smul_dotProduct, smul_eq_mul]
  have h3 : θ * (star v ⬝ᵥ v) = star θ * (star v ⬝ᵥ v) := by rw [← h1, h2]
  have h4 : θ = star θ := mul_right_cancel₀ hpair h3
  refine ⟨θ.re, ?_⟩
  have h5 : (starRingEnd ℂ) θ = θ := h4.symm
  exact (Complex.conj_eq_iff_re.mp h5).symm

theorem eigenvalue_of_real {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) : ∃ t : ℝ, θ = (t : ℂ) :=
  eigenvalue_real hA ((isEigenvalue_iff_mem_eigFinset hA).mpr hθ)

/-! ## The squarefree annihilator -/

/-- The monic squarefree polynomial `∏_{θ ∈ eigFinset A} (X - C θ)`. -/
def eigPoly (A : Matrix X X ℂ) : Polynomial ℂ :=
  ∏ θ ∈ eigFinset A, (Polynomial.X - Polynomial.C θ)

theorem monic_eigPoly (A : Matrix X X ℂ) : (eigPoly A).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_eigPoly (A : Matrix X X ℂ) :
    (eigPoly A).natDegree = (eigFinset A).card := by
  rw [eigPoly, Polynomial.natDegree_prod _ _ fun i _ => (Polynomial.monic_X_sub_C i).ne_zero,
    Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C i, Finset.sum_const,
    smul_eq_mul, mul_one]

theorem eval_eigPoly_of_mem {A : Matrix X X ℂ} {θ : ℂ} (hθ : θ ∈ eigFinset A) :
    (eigPoly A).eval θ = 0 := by
  rw [eigPoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero hθ (by simp)

/-- A matrix killing every vector is zero. -/
theorem matrix_eq_zero_of_mulVec_eq_zero {M : Matrix X X ℂ} (h : ∀ v : X → ℂ, M *ᵥ v = 0) :
    M = 0 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, Matrix.zero_apply] at h1
  rw [Finset.sum_eq_single j] at h1
  · simpa using h1
  · intro b _ hb
    simp [Pi.single_eq_of_ne, hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- An `A`-stable subspace `U ≠ ⊥` contains an eigenvector of `A`. -/
theorem exists_eigenvector_mem_of_stable {A : Matrix X X ℂ} {U : Submodule ℂ (X → ℂ)}
    (hU : U ≠ ⊥) (hstab : ∀ u ∈ U, A *ᵥ u ∈ U) :
    ∃ (b : X → ℂ) (θ : ℂ), b ∈ U ∧ b ≠ 0 ∧ A *ᵥ b = θ • b := by
  classical
  haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hU
  have hstab' : ∀ u ∈ U, A.mulVecLin u ∈ U := hstab
  obtain ⟨θ, hθ⟩ := Module.End.exists_eigenvalue (A.mulVecLin.restrict hstab')
  rw [Module.End.hasEigenvalue_iff] at hθ
  obtain ⟨x, hxmem, hxne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hθ
  have hfx : A.mulVecLin.restrict hstab' x = θ • x :=
    (Module.End.mem_eigenspace_iff).mp hxmem
  refine ⟨(x : X → ℂ), θ, x.2, fun h => hxne (Subtype.ext h), ?_⟩
  have := congrArg (fun y : ↥U => (y : X → ℂ)) hfx
  simpa using this

theorem eigFinset_nonempty [Nonempty X] (A : Matrix X X ℂ) : (eigFinset A).Nonempty := by
  obtain ⟨b, θ, -, hbne, hbθ⟩ :=
    exists_eigenvector_mem_of_stable (A := A) (U := ⊤) (by simp) fun u _ => Submodule.mem_top
  refine Finset.nonempty_iff_ne_empty.mpr fun hempty => ?_
  have hmem : θ ∈ eigFinset A := isEigenvalue_iff_mem_eigFinset'.mp ⟨b, hbne, hbθ⟩
  rw [hempty] at hmem
  exact absurd hmem (Finset.notMem_empty θ)

/-- **The squarefree annihilator.** The product of the linear factors of the
eigenvalues of a self-adjoint matrix annihilates it. -/
theorem aeval_eigPoly_eq_zero {A : Matrix X X ℂ} (hA : star A = A) :
    (Polynomial.aeval A) (eigPoly A) = 0 := by
  classical
  have hreal : ∀ θ ∈ eigFinset A, star θ = θ := by
    intro θ hθ
    obtain ⟨t, rfl⟩ := eigenvalue_of_real hA hθ
    simp
  have key : ∀ n : ℕ, ∀ (U : Submodule ℂ (X → ℂ)), (∀ u ∈ U, A *ᵥ u ∈ U) →
      Module.finrank ℂ ↥U ≤ n → ∀ u ∈ U, (Polynomial.aeval A) (eigPoly A) *ᵥ u = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro U hstab hdim u hu
      by_cases hU : U = ⊥
      · rw [hU, Submodule.mem_bot] at hu
        rw [hu, mulVec_zero]
      · obtain ⟨b, θ, hbU, hbne, hbθ⟩ := exists_eigenvector_mem_of_stable hU hstab
        have hθS : θ ∈ eigFinset A := isEigenvalue_iff_mem_eigFinset'.mp ⟨b, hbne, hbθ⟩
        have hθreal : star θ = θ := hreal θ hθS
        set U₁ : Submodule ℂ (X → ℂ) := U ⊓ Module.End.eigenspace A.mulVecLin θ with hU₁def
        have hbU₁ : b ∈ U₁ := by
          rw [hU₁def, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
          exact ⟨hbU, by simpa using hbθ⟩
        set U₂ : Submodule ℂ (X → ℂ) := U ⊓ orthCompl U₁ with hU₂def
        have hbU₂ : b ∉ U₂ := by
          intro hb
          have h1 : b ∈ orthCompl U₁ := (Submodule.mem_inf.mp hb).2
          rw [mem_orthCompl] at h1
          exact hbne (star_dotProduct_self_eq_zero (h1 b hbU₁))
        have hU₂lt : U₂ < U := lt_of_le_of_ne (by rw [hU₂def]; exact inf_le_left) fun h => by
          rw [h] at hbU₂
          exact hbU₂ hbU
        have hfr : Module.finrank ℂ ↥U₂ < n :=
          lt_of_lt_of_le (Submodule.finrank_lt_finrank_of_lt hU₂lt) hdim
        have hstab₂ : ∀ z ∈ U₂, A *ᵥ z ∈ U₂ := by
          intro z hz
          rw [Submodule.mem_inf] at hz ⊢
          refine ⟨hstab z hz.1, ?_⟩
          rw [mem_orthCompl]
          intro s hs
          have hs1 : A *ᵥ s = θ • s :=
            (Module.End.mem_eigenspace_iff).mp (Submodule.mem_inf.mp hs).2
          rw [star_mulVec_dotProduct, hA, hs1, star_smul, hθreal, smul_dotProduct, smul_eq_mul,
            (mem_orthCompl.mp hz.2) s hs, mul_zero]
        obtain ⟨h, hhU₁, horth⟩ := exists_orthogonal_decomp (W := U₁) u
        have hhU : h ∈ U := (Submodule.mem_inf.mp hhU₁).1
        have hrU₂ : u - h ∈ U₂ := by
          rw [Submodule.mem_inf]
          exact ⟨Submodule.sub_mem _ hu hhU, mem_orthCompl.mpr horth⟩
        have hkill : (Polynomial.aeval A) (eigPoly A) *ᵥ h = 0 := by
          have hfac : eigPoly A
              = (∏ ψ ∈ (eigFinset A).erase θ, (Polynomial.X - Polynomial.C ψ))
                * (Polynomial.X - Polynomial.C θ) :=
            (Finset.prod_erase_mul _ _ hθS).symm
          rw [hfac, map_mul, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
            Algebra.algebraMap_eq_smul_one, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec,
            Matrix.smul_mulVec, Matrix.one_mulVec]
          have hh : A *ᵥ h = θ • h :=
            (Module.End.mem_eigenspace_iff).mp (Submodule.mem_inf.mp hhU₁).2
          rw [hh, sub_self, mulVec_zero]
        have hdecomp : h + (u - h) = u := by abel
        rw [← hdecomp, Matrix.mulVec_add, hkill, zero_add]
        exact ih (Module.finrank ℂ ↥U₂) hfr U₂ hstab₂ le_rfl (u - h) hrU₂
  have hall : ∀ v : X → ℂ, (Polynomial.aeval A) (eigPoly A) *ᵥ v = 0 := fun v =>
    key (Module.finrank ℂ ↥(⊤ : Submodule ℂ (X → ℂ))) ⊤ (fun u _ => Submodule.mem_top) le_rfl v
      Submodule.mem_top
  exact matrix_eq_zero_of_mulVec_eq_zero hall

/-- A polynomial vanishing at every eigenvalue annihilates `A`. -/
theorem aeval_eq_zero_of_forall_eval_eq_zero {A : Matrix X X ℂ} (hA : star A = A)
    {q : Polynomial ℂ} (hq : ∀ θ ∈ eigFinset A, q.eval θ = 0) :
    (Polynomial.aeval A) q = 0 := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · haveI : Subsingleton (Matrix X X ℂ) := ⟨fun a b => by ext i; exact isEmptyElim i⟩
    exact Subsingleton.elim _ _
  · have hne1 : eigPoly A ≠ 1 := by
      intro h
      have h1 : (eigFinset A).card = 0 := by
        rw [← natDegree_eigPoly A, h, Polynomial.natDegree_one]
      have h2 := eigFinset_nonempty A
      rw [Finset.card_eq_zero] at h1
      exact h2.ne_empty h1
    have hmod : q %ₘ eigPoly A = 0 := by
      refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (q %ₘ eigPoly A)
        (f := fun θ : ↥(eigFinset A) => (θ : ℂ)) (fun a b hab => Subtype.ext hab) ?_ ?_
      · intro θ
        have hroot : (eigPoly A).eval (θ : ℂ) = 0 := eval_eigPoly_of_mem θ.2
        have h := Polynomial.eval₂_modByMonic_eq_self_of_root (f := RingHom.id ℂ) (p := q)
          (q := eigPoly A) (x := (θ : ℂ)) (by simpa using hroot)
        rw [Polynomial.eval₂_id] at h
        rw [h]
        exact hq θ θ.2
      · rw [Fintype.card_coe, ← natDegree_eigPoly A]
        exact Polynomial.natDegree_modByMonic_lt q (monic_eigPoly A) hne1
    calc (Polynomial.aeval A) q
        = (Polynomial.aeval A) (q %ₘ eigPoly A + eigPoly A * (q /ₘ eigPoly A)) := by
            rw [Polynomial.modByMonic_add_div]
      _ = (Polynomial.aeval A) (q %ₘ eigPoly A)
            + (Polynomial.aeval A) (eigPoly A) * (Polynomial.aeval A) (q /ₘ eigPoly A) := by
            rw [map_add, map_mul]
      _ = 0 := by rw [hmod, map_zero, zero_add, aeval_eigPoly_eq_zero hA, zero_mul]

/-! ## Conjugation and polynomial calculus -/

theorem star_smul_matrix (c : ℂ) (M : Matrix X X ℂ) : star (c • M) = star c • star M := by
  ext i j
  simp [Matrix.star_apply]

/-- Conjugating a polynomial in `A` conjugates its coefficients. -/
theorem star_aeval {A : Matrix X X ℂ} (hA : star A = A) (q : Polynomial ℂ) :
    star ((Polynomial.aeval A) q) = (Polynomial.aeval A) (q.map (starRingEnd ℂ)) := by
  have hinj : Function.Injective (starRingEnd ℂ) := fun a b h => by
    have h2 := congrArg (starRingEnd ℂ) h
    simpa using h2
  rw [Polynomial.aeval_eq_sum_range (x := A),
    Polynomial.aeval_eq_sum_range (x := A),
    Polynomial.natDegree_map_eq_of_injective hinj q, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_smul_matrix, star_pow, hA, Polynomial.coeff_map]
  simp only [RCLike.star_def]

/-- Polynomials in `A` commute with `A`. -/
theorem aeval_mul_comm {A : Matrix X X ℂ} (p : Polynomial ℂ) :
    (Polynomial.aeval A) p * A = A * (Polynomial.aeval A) p := by
  have h1 : (Polynomial.aeval A) p * (Polynomial.aeval A) Polynomial.X
      = (Polynomial.aeval A) (p * Polynomial.X) := (map_mul (Polynomial.aeval A) p _).symm
  have h2 : (Polynomial.aeval A) Polynomial.X * (Polynomial.aeval A) p
      = (Polynomial.aeval A) (Polynomial.X * p) := (map_mul (Polynomial.aeval A) _ p).symm
  rw [Polynomial.aeval_X] at h1 h2
  rw [h1, h2, mul_comm]

/-- If `W` is stable under `A` then it is stable under every polynomial in `A`. -/
theorem aeval_mulVec_mem_of_stable {A : Matrix X X ℂ} {W : Submodule ℂ (X → ℂ)}
    (hW : ∀ w ∈ W, A *ᵥ w ∈ W) (p : Polynomial ℂ) :
    ∀ w ∈ W, (Polynomial.aeval A) p *ᵥ w ∈ W := by
  induction p using Polynomial.induction_on with
  | C a =>
    intro w hw
    rw [Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
    exact Submodule.smul_mem _ a hw
  | add p q hp hq =>
    intro w hw
    rw [map_add, Matrix.add_mulVec]
    exact Submodule.add_mem _ (hp w hw) (hq w hw)
  | monomial n a ih =>
    intro w hw
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, ← Matrix.mulVec_mulVec]
    exact ih _ (hW w hw)

/-! ## The Lagrange interpolant -/

/-- The Lagrange numerator `∏_{ψ ∈ S.erase θ} (X - C ψ)`. -/
def specFactor (S : Finset ℂ) (θ : ℂ) : Polynomial ℂ :=
  ∏ ψ ∈ S.erase θ, (Polynomial.X - Polynomial.C ψ)

/-- The Lagrange denominator `∏_{ψ ∈ S.erase θ} (θ - ψ)`. -/
def specDenom (S : Finset ℂ) (θ : ℂ) : ℂ :=
  ∏ ψ ∈ S.erase θ, (θ - ψ)

/-- The Lagrange polynomial of `θ` with respect to `S`. -/
def lagrangePoly (S : Finset ℂ) (θ : ℂ) : Polynomial ℂ :=
  Polynomial.C ((specDenom S θ)⁻¹) * specFactor S θ

theorem specFactor_eval_self (S : Finset ℂ) (θ : ℂ) :
    (specFactor S θ).eval θ = specDenom S θ := by
  simp [specFactor, specDenom, Polynomial.eval_prod]

theorem specFactor_eval_of_mem_erase {S : Finset ℂ} {θ ψ : ℂ} (h : ψ ∈ S.erase θ) :
    (specFactor S θ).eval ψ = 0 := by
  simp only [specFactor, Polynomial.eval_prod]
  exact Finset.prod_eq_zero h (by simp)

theorem specDenom_ne_zero (S : Finset ℂ) {θ : ℂ} (hθ : θ ∈ S) : specDenom S θ ≠ 0 := by
  simp only [specDenom, Finset.prod_ne_zero_iff]
  intro ψ hψ
  have hne : ψ ≠ θ := (Finset.mem_erase.mp hψ).1
  exact sub_ne_zero.mpr (Ne.symm hne)

theorem lagrangePoly_eval_self (S : Finset ℂ) {θ : ℂ} (hθ : θ ∈ S) :
    (lagrangePoly S θ).eval θ = 1 := by
  simp only [lagrangePoly, Polynomial.eval_mul, Polynomial.eval_C]
  rw [specFactor_eval_self, inv_mul_cancel₀ (specDenom_ne_zero S hθ)]

theorem lagrangePoly_eval_of_ne {S : Finset ℂ} {μ ν : ℂ} (hμ : μ ∈ S) (h : μ ≠ ν) :
    (lagrangePoly S ν).eval μ = 0 := by
  simp only [lagrangePoly, Polynomial.eval_mul, Polynomial.eval_C]
  rw [specFactor_eval_of_mem_erase (θ := ν) (ψ := μ) (by rw [Finset.mem_erase]; exact ⟨h, hμ⟩),
    mul_zero]

theorem specFactor_mul_X_sub_C (S : Finset ℂ) {θ : ℂ} (hθ : θ ∈ S) :
    specFactor S θ * (Polynomial.X - Polynomial.C θ)
      = ∏ ψ ∈ S, (Polynomial.X - Polynomial.C ψ) :=
  Finset.prod_erase_mul S (fun ψ => Polynomial.X - Polynomial.C ψ) hθ

theorem map_star_specFactor {S : Finset ℂ} (hS : ∀ ψ ∈ S, (starRingEnd ℂ) ψ = ψ) (θ : ℂ) :
    (specFactor S θ).map (starRingEnd ℂ) = specFactor S θ := by
  simp only [specFactor, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun ψ hψ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    hS ψ (Finset.mem_of_mem_erase hψ)]

theorem map_star_specDenom {S : Finset ℂ} {θ : ℂ} (hS : ∀ ψ ∈ S, (starRingEnd ℂ) ψ = ψ)
    (hθ : (starRingEnd ℂ) θ = θ) : (starRingEnd ℂ) (specDenom S θ) = specDenom S θ := by
  simp only [specDenom, map_prod]
  refine Finset.prod_congr rfl fun ψ hψ => ?_
  rw [map_sub, hθ, hS ψ (Finset.mem_of_mem_erase hψ)]

theorem map_star_lagrangePoly {S : Finset ℂ} {θ : ℂ} (hS : ∀ ψ ∈ S, (starRingEnd ℂ) ψ = ψ)
    (hθ : (starRingEnd ℂ) θ = θ) : (lagrangePoly S θ).map (starRingEnd ℂ) = lagrangePoly S θ := by
  simp only [lagrangePoly, Polynomial.map_mul, Polynomial.map_C, map_inv₀,
    map_star_specDenom hS hθ, map_star_specFactor hS]

/-! ## The spectral projections -/

/-- The spectral projection of `A` onto the `θ`-eigenspace:
`∏_{ψ ≠ θ} (A - ψ)/(θ - ψ)` (Lagrange interpolation over the eigenvalues). -/
def spectralProj (A : Matrix X X ℂ) (θ : ℂ) : Matrix X X ℂ :=
  (Polynomial.aeval A) (lagrangePoly (eigFinset A) θ)

theorem aeval_C_mul (A : Matrix X X ℂ) (c : ℂ) (p : Polynomial ℂ) :
    (Polynomial.aeval A) (Polynomial.C c * p) = c • (Polynomial.aeval A) p := by
  rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem spectralProj_eq_zero {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∉ eigFinset A) : spectralProj A θ = 0 := by
  have herase : (eigFinset A).erase θ = eigFinset A := Finset.erase_eq_of_notMem hθ
  have h : lagrangePoly (eigFinset A) θ
      = Polynomial.C ((specDenom (eigFinset A) θ)⁻¹) * eigPoly A := by
    simp only [lagrangePoly, specFactor, herase, eigPoly]
  rw [spectralProj, h, aeval_C_mul, aeval_eigPoly_eq_zero hA, smul_zero]

theorem spectralProj_mul_self {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) : spectralProj A θ * spectralProj A θ = spectralProj A θ := by
  have hq : ∀ ψ ∈ eigFinset A,
      (lagrangePoly (eigFinset A) θ * lagrangePoly (eigFinset A) θ
        - lagrangePoly (eigFinset A) θ).eval ψ = 0 := by
    intro ψ hψ
    rw [Polynomial.eval_sub, Polynomial.eval_mul]
    by_cases hψθ : ψ = θ
    · subst hψθ
      rw [lagrangePoly_eval_self _ hψ, mul_one, sub_self]
    · rw [lagrangePoly_eval_of_ne (S := eigFinset A) (ν := θ) hψ hψθ]
      simp
  have h := aeval_eq_zero_of_forall_eval_eq_zero hA hq
  rw [map_sub, map_mul, sub_eq_zero] at h
  simpa only [spectralProj] using h

theorem spectralProj_mul_of_ne' {A : Matrix X X ℂ} (hA : star A = A) {θ ψ : ℂ}
    (hθ : θ ∈ eigFinset A) (hψ : ψ ∈ eigFinset A) (h : θ ≠ ψ) :
    spectralProj A θ * spectralProj A ψ = 0 := by
  have hq : ∀ φ ∈ eigFinset A,
      (lagrangePoly (eigFinset A) θ * lagrangePoly (eigFinset A) ψ).eval φ = 0 := by
    intro φ hφ
    rw [Polynomial.eval_mul]
    by_cases hφθ : φ = θ
    · subst hφθ
      rw [lagrangePoly_eval_self _ hθ, lagrangePoly_eval_of_ne (S := eigFinset A) hθ h, mul_zero]
    · rw [lagrangePoly_eval_of_ne (S := eigFinset A) (ν := θ) hφ hφθ, zero_mul]
  have h2 := aeval_eq_zero_of_forall_eval_eq_zero hA hq
  rw [map_mul] at h2
  simpa only [spectralProj] using h2

/-- The spectral projections of distinct eigenvalues are orthogonal (no membership
hypothesis needed: a projection at a non-eigenvalue vanishes). -/
theorem spectralProj_mul_of_ne {A : Matrix X X ℂ} (hA : star A = A) {θ ψ : ℂ}
    (h : θ ≠ ψ) : spectralProj A θ * spectralProj A ψ = 0 := by
  by_cases hθ : θ ∈ eigFinset A
  · by_cases hψ : ψ ∈ eigFinset A
    · exact spectralProj_mul_of_ne' hA hθ hψ h
    · rw [spectralProj_eq_zero hA hψ, mul_zero]
  · rw [spectralProj_eq_zero hA hθ, zero_mul]

theorem adj_mul_spectralProj {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) : A * spectralProj A θ = θ • spectralProj A θ := by
  have hq : ∀ ψ ∈ eigFinset A,
      ((Polynomial.X - Polynomial.C θ) * lagrangePoly (eigFinset A) θ).eval ψ = 0 := by
    intro ψ hψ
    rw [Polynomial.eval_mul]
    by_cases hψθ : ψ = θ
    · subst hψθ; simp
    · rw [lagrangePoly_eval_of_ne (S := eigFinset A) (ν := θ) hψ hψθ, mul_zero]
  have h := aeval_eq_zero_of_forall_eval_eq_zero hA hq
  rw [map_mul, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_eq_smul_one] at h
  have h3 : (A - θ • 1) * spectralProj A θ = 0 := by simpa only [spectralProj] using h
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul] at h3
  rwa [sub_eq_zero] at h3

theorem sum_spectralProj {A : Matrix X X ℂ} (hA : star A = A) :
    ∑ θ ∈ eigFinset A, spectralProj A θ = 1 := by
  have hq : ∀ ψ ∈ eigFinset A,
      ((∑ θ ∈ eigFinset A, lagrangePoly (eigFinset A) θ) - 1).eval ψ = 0 := by
    intro ψ hψ
    rw [Polynomial.eval_sub, Polynomial.eval_finsetSum, Polynomial.eval_one,
      Finset.sum_eq_single ψ]
    · rw [lagrangePoly_eval_self _ hψ, sub_self]
    · intro b _ hb
      exact lagrangePoly_eval_of_ne (S := eigFinset A) (ν := b) hψ (Ne.symm hb)
    · intro h; exact absurd hψ h
  have h := aeval_eq_zero_of_forall_eval_eq_zero hA hq
  rw [map_sub, map_sum, Polynomial.aeval_one, sub_eq_zero] at h
  simpa only [spectralProj] using h

theorem aeval_mul_spectralProj {A : Matrix X X ℂ} (hA : star A = A) (q : Polynomial ℂ)
    {θ : ℂ} (hθ : θ ∈ eigFinset A) :
    (Polynomial.aeval A) q * spectralProj A θ = (q.eval θ) • spectralProj A θ := by
  have hq : ∀ ψ ∈ eigFinset A,
      (q * lagrangePoly (eigFinset A) θ
        - Polynomial.C (q.eval θ) * lagrangePoly (eigFinset A) θ).eval ψ = 0 := by
    intro ψ hψ
    rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_C]
    by_cases hψθ : ψ = θ
    · subst hψθ
      rw [lagrangePoly_eval_self _ hψ, mul_one, sub_self]
    · rw [lagrangePoly_eval_of_ne (S := eigFinset A) (ν := θ) hψ hψθ]
      simp
  have h := aeval_eq_zero_of_forall_eval_eq_zero hA hq
  have hkey : (Polynomial.aeval A) q * spectralProj A θ - (q.eval θ) • spectralProj A θ
      = (Polynomial.aeval A) (q * lagrangePoly (eigFinset A) θ
          - Polynomial.C (q.eval θ) * lagrangePoly (eigFinset A) θ) := by
    rw [map_sub, aeval_C_mul, map_mul]
    simp only [spectralProj]
  rw [← sub_eq_zero, hkey, h]

theorem star_spectralProj {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) : star (spectralProj A θ) = spectralProj A θ := by
  have hS : ∀ ψ ∈ eigFinset A, (starRingEnd ℂ) ψ = ψ := by
    intro ψ hψ
    obtain ⟨t, rfl⟩ := eigenvalue_of_real hA hψ
    simp
  rw [spectralProj, star_aeval hA, map_star_lagrangePoly hS (hS θ hθ)]

theorem spectralProj_mulVec_eigenvector {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) {v : X → ℂ} (hv : v ≠ 0) (hAv : A *ᵥ v = θ • v) :
    spectralProj A θ *ᵥ v = v := by
  have hdvd : (Polynomial.X - Polynomial.C θ) ∣ (lagrangePoly (eigFinset A) θ - 1) := by
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_one, lagrangePoly_eval_self _ hθ, sub_self]
  obtain ⟨q, hq⟩ := hdvd
  have h1 : spectralProj A θ - 1 = (Polynomial.aeval A) (lagrangePoly (eigFinset A) θ - 1) := by
    rw [spectralProj, map_sub, Polynomial.aeval_one]
  have hq' : lagrangePoly (eigFinset A) θ - 1 = q * (Polynomial.X - Polynomial.C θ) := by
    rw [hq, mul_comm]
  have key : spectralProj A θ - 1 = (Polynomial.aeval A) q * (A - θ • 1) := by
    rw [h1, hq', map_mul, Polynomial.aeval_sub, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one]
  have h2 : (spectralProj A θ - 1) *ᵥ v = 0 := by
    rw [key, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      hAv, sub_self, mulVec_zero]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h2
  exact h2

/-- Every `aeval` of `A` lies in the subalgebra generated by `A`. -/
theorem aeval_mem_adjoin (A : Matrix X X ℂ) (q : Polynomial ℂ) :
    (Polynomial.aeval A) q ∈ Algebra.adjoin ℂ ({A} : Set (Matrix X X ℂ)) := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C]
    exact Subalgebra.algebraMap_mem _ a
  | add p q hp hq =>
    rw [map_add]
    exact add_mem hp hq
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    exact mul_mem ih (Algebra.subset_adjoin (Set.mem_singleton A))

/-- The spectral projection is a polynomial in `A`.  (The notes' `Subalgebra.span`
does not exist in this Mathlib; `Algebra.adjoin` is the same subalgebra.) -/
theorem spectralProj_mem_span {A : Matrix X X ℂ} (hA : star A = A) (θ : ℂ) :
    spectralProj A θ ∈ Algebra.adjoin ℂ ({A} : Set (Matrix X X ℂ)) :=
  aeval_mem_adjoin A _

/-! ## The spectral theorem, complex forms -/

/-- **Spectral theorem, projection form.**  A self-adjoint matrix is the sum of
its eigenvalues times the spectral projections. -/
theorem spectral_theorem {A : Matrix X X ℂ} (hA : star A = A) :
    A = ∑ θ ∈ eigFinset A, θ • spectralProj A θ := by
  conv_lhs => rw [← mul_one A, ← sum_spectralProj hA]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun θ hθ => adj_mul_spectralProj hA hθ

/-- **Spectral theorem, eigenbasis form.**  A self-adjoint matrix admits an
orthonormal basis of eigenvectors. -/
theorem exists_orthonormal_eigenbasis {A : Matrix X X ℂ} (hA : star A = A) :
    ∃ (n : ℕ) (θ : Fin n → ℂ) (v : Fin n → X → ℂ),
      (∀ i, A *ᵥ v i = θ i • v i) ∧
      (∀ i j, star (v i) ⬝ᵥ v j = if i = j then 1 else 0) ∧
      (Submodule.span ℂ (Set.range v) = ⊤) := by
  classical
  have hAh : A.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hA
  set U : Matrix X X ℂ := (hAh.eigenvectorUnitary : Matrix X X ℂ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self hAh.eigenvectorUnitary
  have hU'U : star U * U = 1 := Unitary.coe_star_mul_self hAh.eigenvectorUnitary
  set e : Fin (Fintype.card X) ≃ X := (Fintype.equivFin X).symm with he
  have hUe : ∀ (j : X) (x : X), U x j = (hAh.eigenvectorBasis j).ofLp x := fun j x =>
    hAh.eigenvectorUnitary_apply x j
  have hmv : ∀ (M : Matrix X X ℂ) (y : X → ℂ), M *ᵥ y = ∑ j, y j • (fun x => M x j) := by
    intro M y
    funext x
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  set n : ℕ := Fintype.card X with hn
  set θf : Fin n → ℂ := fun i => ((hAh.eigenvalues (e i) : ℝ) : ℂ) with hθf
  set vf : Fin n → X → ℂ := fun i x => U x (e i) with hvf
  refine ⟨n, θf, vf, ?_, ?_, ?_⟩
  · intro i
    have hv : vf i = (hAh.eigenvectorBasis (e i)).ofLp := by
      simp [hvf, hUe]
    rw [hv]
    have h := hAh.mulVec_eigenvectorBasis (e i)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at h
    simpa [hθf] using h
  · intro i j
    have hdot : star (vf i) ⬝ᵥ vf j = ∑ x, star (U x (e i)) * U x (e j) := by
      simp [dotProduct, hvf]
    rw [hdot]
    have hmul : ∑ x, star (U x (e i)) * U x (e j) = if e i = e j then 1 else 0 := by
      have h2 := congrFun (congrFun hU'U (e i)) (e j)
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using h2
    rw [hmul]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij, e.injective.eq_iff]
  · rw [Submodule.eq_top_iff']
    intro w
    have hexp : w = ∑ j : X, ((star U) *ᵥ w) j • (fun x => U x j) := by
      calc w = 1 *ᵥ w := by rw [one_mulVec]
        _ = (U * star U) *ᵥ w := by rw [hUU]
        _ = U *ᵥ ((star U) *ᵥ w) := by rw [Matrix.mulVec_mulVec]
        _ = ∑ j : X, ((star U) *ᵥ w) j • (fun x => U x j) := hmv _ _
    rw [hexp, ← Equiv.sum_comp e]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The eigenvalues of `A * A` are the squares of the eigenvalues of `A`
(for `A` self-adjoint). -/
theorem eigFinset_sq {A : Matrix X X ℂ} (hA : star A = A) :
    eigFinset (A * A) = (eigFinset A).image (fun θ => θ * θ) := by
  classical
  have hAh : A.IsHermitian := Matrix.isHermitian_iff_isSelfAdjoint.mpr hA
  set U : Matrix X X ℂ := (hAh.eigenvectorUnitary : Matrix X X ℂ) with hU
  set D : Matrix X X ℂ := diagonal (RCLike.ofReal ∘ hAh.eigenvalues) with hD
  set a : X → ℂ := fun i => ((hAh.eigenvalues i : ℝ) : ℂ) * ((hAh.eigenvalues i : ℝ) : ℂ)
    with ha
  have hU'U : star U * U = 1 := Unitary.coe_star_mul_self hAh.eigenvectorUnitary
  have hAdec : A = U * D * star U := by
    rw [hAh.spectral_theorem, Unitary.conjStarAlgAut_apply]
  -- `A * A` is (unitarily) conjugate to `D * D`
  have hsq : A * A = U * (D * D) * star U := by
    rw [hAdec]
    calc (U * D * star U) * (U * D * star U)
        = U * D * (star U * U) * D * star U := by noncomm_ring
      _ = U * D * 1 * D * star U := by rw [hU'U]
      _ = U * (D * D) * star U := by rw [mul_one]; noncomm_ring
  have hchar : (A * A).charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)) := by
    rw [hsq, Matrix.charpoly_mul_comm (U * (D * D)) (star U), ← mul_assoc, hU'U, one_mul,
      hD, Matrix.diagonal_mul_diagonal, Matrix.charpoly_diagonal]
    simp only [Function.comp_apply, ha]
    exact Finset.prod_congr rfl fun i _ => rfl
  have hne : Finset.univ.prod (fun i => Polynomial.X - Polynomial.C (a i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _
  have hAAeig : eigFinset (A * A) = Finset.univ.image a := by
    rw [eigFinset, hchar, Polynomial.roots_prod _ Finset.univ hne]
    simp [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Multiset.toFinset_map]
  have hAeig : eigFinset A = Finset.univ.image (fun i => ((hAh.eigenvalues i : ℝ) : ℂ)) := by
    rw [eigFinset, hAh.roots_charpoly_eq_eigenvalues, Multiset.toFinset_map,
      Finset.val_toFinset]
    rfl
  rw [hAAeig, hAeig, Finset.image_image]
  rfl

end Terwilliger
