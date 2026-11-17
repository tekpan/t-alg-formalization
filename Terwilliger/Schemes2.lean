/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.AssociationScheme

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
# Commutative association schemes, continued (Chapters 20–27)

This file continues `Terwilliger/AssociationScheme.lean`.  It bundles the data
that the notes take for granted from Chapter 19 onwards — the primitive
idempotents `E_j` of the Bose–Mesner algebra, the eigenvalues `p_i(j)`, the dual
eigenvalues `q_i(j)` and the Krein parameters `q^h_{ij}` — into the structure
`SchemeData`, and then states the results of Chapters 20–27 for such data.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Definition 27.3: the Gaussian binomial `[i/1] = 1 + q + ⋯ + q^{i-1}`. -/
def gaussBinom (q : ℝ) (i : ℕ) : ℝ := ∑ k ∈ Finset.range i, q ^ k

/-- The data of a commutative scheme together with a choice of primitive
idempotents and the eigenvalues `p_i(j)`, `q_i(j)`.  Chapter 19 shows such data
exist for every commutative scheme. -/
structure SchemeData (X : Type*) [Fintype X] [DecidableEq X] (D : ℕ) where
  /-- The underlying scheme. -/
  scheme : AssociationScheme X D
  /-- The scheme is symmetric. -/
  symm : ∀ i x y, scheme.rel i x y ↔ scheme.rel i y x
  /-- The primitive idempotents. -/
  E : Fin (D + 1) → Matrix X X ℂ
  E_idem : ∀ i, E i * E i = E i
  E_orth : ∀ i j, i ≠ j → E i * E j = 0
  E_sum : ∑ i, E i = 1
  E_mem : ∀ i, E i ∈ scheme.boseMesnerSubmodule
  /-- `p_i(j)`: the eigenvalue of `Aᵢ` on `E_jV`. -/
  pcoef : Fin (D + 1) → Fin (D + 1) → ℂ
  A_eq : ∀ i, scheme.assocMatrix i = ∑ j, pcoef i j • E j
  /-- `q_i(j)`: the dual eigenvalue, `E_i = |X|⁻¹ ∑_j q_i(j) A_j`. -/
  qcoef : Fin (D + 1) → Fin (D + 1) → ℂ
  E_eq : ∀ i, E i = (1 / (Fintype.card X : ℂ)) • ∑ j, qcoef i j • scheme.assocMatrix j
  /-- The Krein parameters `q^h_{ij}`. -/
  krein : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℂ
  hadamard : ∀ i j, (fun x y => E i x y * E j x y)
    = (1 / (Fintype.card X : ℂ)) • ∑ h, krein i j h • E h

namespace SchemeData

variable {D : ℕ} (Y : SchemeData X D)

/-- The association matrix `Aᵢ`. -/
def A (i : Fin (D + 1)) : Matrix X X ℂ := Y.scheme.assocMatrix i

/-- The primitive idempotent `Eᵢ`. -/
def Eidem (i : Fin (D + 1)) : Matrix X X ℂ := Y.E i

/-- The dual idempotent `E*_i(x)`. -/
def dualIdem (x : X) (i : Fin (D + 1)) : Matrix X X ℂ :=
  diagonal fun y => if Y.scheme.rel i x y then 1 else 0

/-- The dual association matrix `A*_i(x) = ∑_j q_i(j) E*_j(x)`. -/
def dualA (x : X) (i : Fin (D + 1)) : Matrix X X ℂ :=
  ∑ j, Y.qcoef i j • Y.dualIdem x j

/-- The all-ones matrix `J = ∑ᵢ Aᵢ`. -/
def allOne : Matrix X X ℂ := fun _ _ => 1

@[simp]
theorem allOne_apply (x y : X) : (allOne : Matrix X X ℂ) x y = 1 := rfl

/-- The valency `kᵢ = p^0_{ii} = |{y ∣ rel i x y}|` (notes ch. 20, Lemma 20.1 (ii)).

DEVIATION (reported): the draft defined `kval i := Y.scheme.p i 0 0`, i.e. `p^i_{00}`.  For a pair
`(x,y) ∈ R_i` that is the number of `z` with `rel 0 x z ∧ rel 0 z y`, i.e. `z = x = y`, so it is
`1` for `i = 0` and `0` for `i ≠ 0` — not the valency.  With the draft definition Lemma 20.1 (ii)
is false (`X = Fin 2`, `D = 1`: `pcoef 1 0 = 1` while `p^1_{00} = 0`) and so is Lemma 20.2 (ii).
The notes' valency is `k_i = p^0_{ii'}`, and `Y.symm` gives `i' = i`. -/
def kval (i : Fin (D + 1)) : ℕ := Y.scheme.p 0 i i

/-- The multiplicity `mᵢ = rank Eᵢ`. -/
def mult (i : Fin (D + 1)) : ℕ := Module.finrank ℂ (LinearMap.range (Y.E i).mulVecLin)

/-! ### Preliminaries for Lemmas 20.1 and 20.2 -/

/-- The entries of `Aᵢ`. -/
theorem A_apply (i : Fin (D + 1)) (x y : X) :
    Y.A i x y = if Y.scheme.rel i x y then (1 : ℂ) else 0 :=
  Y.scheme.assocMatrix_apply i x y

/-- `Aᵢ` is the association matrix. -/
theorem A_def (i : Fin (D + 1)) : Y.A i = Y.scheme.assocMatrix i := rfl

/-- The relation of a pair of vertices is unique. -/
theorem rel_unique {i j : Fin (D + 1)} {x y : X}
    (hi : Y.scheme.rel i x y) (hj : Y.scheme.rel j x y) : i = j :=
  (Y.scheme.rel_total x y).unique hi hj

/-- `R_i` meets the diagonal only for `i = 0`. -/
theorem rel_self_iff (i : Fin (D + 1)) (x : X) : Y.scheme.rel i x x ↔ i = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ (Y.scheme.rel_zero x x).mpr rfl⟩
  exact (Y.rel_unique ((Y.scheme.rel_zero x x).mpr rfl) h).symm

/-- The valency is the row sum of `Aᵢ`. -/
theorem card_rel_row (i : Fin (D + 1)) (x : X) :
    (Finset.univ.filter fun y => Y.scheme.rel i x y).card = Y.kval i := by
  have hspec := Y.scheme.p_spec 0 i i x x ((Y.scheme.rel_zero x x).mpr rfl)
  have hfilter : (Finset.univ.filter fun y => Y.scheme.rel i x y)
      = (Finset.univ.filter fun z => Y.scheme.rel i x z ∧ Y.scheme.rel i z x) := by
    apply Finset.filter_congr
    intro z _
    exact ⟨fun h => ⟨h, (Y.symm i x z).mp h⟩, fun h => h.1⟩
  rw [hfilter, hspec]
  rfl

/-- The valency is the column sum of `Aᵢ`. -/
theorem card_rel_col (i : Fin (D + 1)) (y : X) :
    (Finset.univ.filter fun z => Y.scheme.rel i z y).card = Y.kval i := by
  have hfilter : (Finset.univ.filter fun z => Y.scheme.rel i z y)
      = (Finset.univ.filter fun z => Y.scheme.rel i y z) := by
    apply Finset.filter_congr
    intro z _
    exact (Y.symm i z y)
  rw [hfilter, Y.card_rel_row]

/-- The row sums of `Aᵢ` are the valencies. -/
theorem sum_A_row (i : Fin (D + 1)) (x : X) : (∑ y : X, Y.A i x y) = (Y.kval i : ℂ) := by
  have h1 : (∑ y : X, Y.A i x y)
      = ∑ y ∈ (Finset.univ : Finset X), if Y.scheme.rel i x y then (1 : ℂ) else 0 :=
    Finset.sum_congr rfl fun y _ => Y.A_apply i x y
  rw [h1, Finset.sum_boole, Y.card_rel_row]

/-- The column sums of `Aᵢ` are the valencies. -/
theorem sum_A_col (i : Fin (D + 1)) (y : X) : (∑ z : X, Y.A i z y) = (Y.kval i : ℂ) := by
  have h1 : (∑ z : X, Y.A i z y)
      = ∑ z ∈ (Finset.univ : Finset X), if Y.scheme.rel i z y then (1 : ℂ) else 0 :=
    Finset.sum_congr rfl fun z _ => Y.A_apply i z y
  rw [h1, Finset.sum_boole, Y.card_rel_col]

/-- The trace of `Aᵢ` is `|X|` for `i = 0` and `0` otherwise. -/
theorem trace_A (i : Fin (D + 1)) :
    (Y.A i).trace = if i = 0 then (Fintype.card X : ℂ) else 0 := by
  have hsum : (Y.A i).trace = ∑ x : X, if i = 0 then (1 : ℂ) else 0 := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Matrix.diag_apply, Y.A_apply, if_congr (Y.rel_self_iff i x) rfl rfl]
  rw [hsum]
  by_cases h : i = 0 <;> simp [h]

/-- The trace of the all-ones matrix is `|X|`. -/
theorem trace_allOne : (allOne : Matrix X X ℂ).trace = (Fintype.card X : ℂ) := by
  rw [Matrix.trace]
  simp [allOne]

/-- `trace (AᵢAⱼ) = p^0_{ij} |X|`. -/
theorem trace_A_mul (a b : Fin (D + 1)) :
    ((Y.A a) * (Y.A b)).trace = (Y.scheme.p 0 a b : ℂ) * (Fintype.card X : ℂ) := by
  have hexp : Y.A a * Y.A b = ∑ h : Fin (D + 1), (Y.scheme.p h a b : ℂ) • Y.A h :=
    Y.scheme.assocMatrix_mul a b
  rw [hexp, Matrix.trace_sum]
  have hterm : ∀ h : Fin (D + 1), ((Y.scheme.p h a b : ℂ) • Y.A h).trace
      = (Y.scheme.p h a b : ℂ) * (if h = 0 then (Fintype.card X : ℂ) else 0) := by
    intro h
    rw [Matrix.trace_smul, smul_eq_mul, Y.trace_A]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_eq_single 0]
  · rw [if_pos rfl]
  · intro h _ hne
    rw [if_neg hne, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (D + 1))) h

/-- `p^0_{ab} = 0` for `a ≠ b`. -/
theorem p_zero_of_ne (hX : 0 < Fintype.card X) {a b : Fin (D + 1)} (hab : a ≠ b) :
    Y.scheme.p 0 a b = 0 := by
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hX
  have hspec := Y.scheme.p_spec 0 a b x x ((Y.scheme.rel_zero x x).mpr rfl)
  rw [← hspec, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _ hcon
  exact hab (Y.rel_unique hcon.1 ((Y.symm b z x).mp hcon.2))

/-- `trace (AᵢAⱼA_h) = p^h_{ij} k_h |X|`. -/
theorem trace_A_mul_A_mul (hX : 0 < Fintype.card X) (i j h : Fin (D + 1)) :
    ((Y.A i * Y.A j) * Y.A h).trace
      = (Y.scheme.p h i j : ℂ) * ((Y.kval h : ℂ) * (Fintype.card X : ℂ)) := by
  have hexp : Y.A i * Y.A j = ∑ h' : Fin (D + 1), (Y.scheme.p h' i j : ℂ) • Y.A h' :=
    Y.scheme.assocMatrix_mul i j
  rw [hexp, Matrix.sum_mul, Matrix.trace_sum]
  have hterm : ∀ h' : Fin (D + 1), (((Y.scheme.p h' i j : ℂ) • Y.A h') * Y.A h).trace
      = (Y.scheme.p h' i j : ℂ) * ((Y.scheme.p 0 h' h : ℂ) * (Fintype.card X : ℂ)) := by
    intro h'
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Y.trace_A_mul]
  rw [Finset.sum_congr rfl fun h' _ => hterm h', Finset.sum_eq_single h]
  · rfl
  · intro h' _ hne
    rw [Y.p_zero_of_ne hX hne, Nat.cast_zero, zero_mul, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ h) h'

/-- `∑ᵢ Aᵢ` is the all-ones matrix. -/
theorem sum_A : (∑ i : Fin (D + 1), Y.A i) = (allOne : Matrix X X ℂ) := by
  ext x y
  rw [Matrix.sum_apply]
  obtain ⟨i₀, hi₀, huniq⟩ := Y.scheme.rel_total x y
  rw [Finset.sum_eq_single i₀]
  · rw [Y.A_apply, if_pos hi₀]
    rfl
  · intro i _ hi
    rw [Y.A_apply, if_neg (fun hc => hi (huniq i hc))]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

/-- `Aᵢ` times the all-ones matrix is `kᵢ` times the all-ones matrix. -/
theorem A_mul_one (i : Fin (D + 1)) :
    Y.A i * (allOne : Matrix X X ℂ) = (Y.kval i : ℂ) • allOne := by
  ext x y
  have hR : ((Y.kval i : ℂ) • (allOne : Matrix X X ℂ)) x y = (Y.kval i : ℂ) := by
    rw [Matrix.smul_apply, smul_eq_mul, allOne_apply, mul_one]
  rw [hR, Matrix.mul_apply]
  have h1 : (∑ z : X, Y.A i x z * (allOne : Matrix X X ℂ) z y) = ∑ z : X, Y.A i x z :=
    Finset.sum_congr rfl fun z _ => by rw [allOne_apply, mul_one]
  rw [h1, Y.sum_A_row]

/-- The all-ones matrix times `Aᵢ` is `kᵢ` times the all-ones matrix. -/
theorem one_mul_A (i : Fin (D + 1)) :
    (allOne : Matrix X X ℂ) * Y.A i = (Y.kval i : ℂ) • allOne := by
  ext x y
  have hR : ((Y.kval i : ℂ) • (allOne : Matrix X X ℂ)) x y = (Y.kval i : ℂ) := by
    rw [Matrix.smul_apply, smul_eq_mul, allOne_apply, mul_one]
  rw [hR, Matrix.mul_apply]
  have h1 : (∑ z : X, (allOne : Matrix X X ℂ) x z * Y.A i z y) = ∑ z : X, Y.A i z y :=
    Finset.sum_congr rfl fun z _ => by rw [allOne_apply, one_mul]
  rw [h1, Y.sum_A_col]

/-- The trivial idempotent is nonzero. -/
theorem E_zero_ne (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ)) : Y.E 0 ≠ 0 := by
  intro h
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hX
  have h2 : ((1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ)) x x = 0 := by
    rw [← hE0, h, Matrix.zero_apply]
  rw [Matrix.smul_apply, smul_eq_mul, allOne_apply, mul_one] at h2
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)) h2

/-- `Aᵢ` times the trivial idempotent is `kᵢ` times it. -/
theorem A_mul_E_zero
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ)) (i : Fin (D + 1)) :
    Y.A i * Y.E 0 = (Y.kval i : ℂ) • Y.E 0 := by
  conv_lhs => rw [hE0]
  rw [Matrix.mul_smul, Y.A_mul_one, smul_smul,
    mul_comm (1 / (Fintype.card X : ℂ)) (Y.kval i : ℂ), ← smul_smul, ← hE0]

/-- The trivial idempotent times `Aᵢ` is `kᵢ` times it. -/
theorem E_zero_mul_A
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ)) (i : Fin (D + 1)) :
    Y.E 0 * Y.A i = (Y.kval i : ℂ) • Y.E 0 := by
  conv_lhs => rw [hE0]
  rw [Matrix.smul_mul, Y.one_mul_A, smul_smul,
    mul_comm (1 / (Fintype.card X : ℂ)) (Y.kval i : ℂ), ← smul_smul, ← hE0]

/-- `Aᵢ E_j = p_i(j) E_j`. -/
theorem A_mul_E (i j : Fin (D + 1)) : Y.A i * Y.E j = Y.pcoef i j • Y.E j := by
  have h1 : Y.A i = ∑ k, Y.pcoef i k • Y.E k := Y.A_eq i
  rw [h1, Matrix.sum_mul, Finset.sum_eq_single j]
  · rw [Matrix.smul_mul, Y.E_idem]
  · intro k _ hk
    rw [Matrix.smul_mul, Y.E_orth k j hk, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `E_j A_i = p_i(j) E_j`. -/
theorem E_mul_A (j i : Fin (D + 1)) : Y.E j * Y.A i = Y.pcoef i j • Y.E j := by
  have h1 : Y.A i = ∑ k, Y.pcoef i k • Y.E k := Y.A_eq i
  rw [h1, Finset.mul_sum, Finset.sum_eq_single j]
  · rw [Matrix.mul_smul, Y.E_idem]
  · intro k _ hk
    rw [Matrix.mul_smul, Y.E_orth j k (Ne.symm hk), smul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Lemma 20.1 (i): `p_0(j) = 1`. -/
theorem pcoef_zero_row (hne : ∀ j, Y.E j ≠ 0) (j : Fin (D + 1)) : Y.pcoef 0 j = 1 := by
  have h1 := Y.A_mul_E 0 j
  rw [show Y.A 0 = 1 from Y.scheme.assocMatrix_zero, Matrix.one_mul] at h1
  have h2 : (Y.pcoef 0 j - 1) • Y.E j = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.1 h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (hne j)

/-- Lemma 20.1 (ii): `p_i(0) = kᵢ`. -/
theorem pcoef_zero_col (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (i : Fin (D + 1)) : Y.pcoef i 0 = (Y.kval i : ℂ) := by
  have h1 := Y.A_mul_E_zero hE0 i
  have h2 := Y.A_mul_E i 0
  rw [h2] at h1
  have h3 : (Y.pcoef i 0 - (Y.kval i : ℂ)) • Y.E 0 = 0 := by rw [sub_smul, h1, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (Y.E_zero_ne hX hE0)

/-- Lemma 20.1 (iii): `q_0(j) = 1`. -/
theorem qcoef_zero_row (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hk : ∀ j, Y.kval j ≠ 0) (j : Fin (D + 1)) : Y.qcoef 0 j = 1 := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have hk' : (Y.kval j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hk j)
  have hL : (Y.E 0 * Y.A j).trace = Y.qcoef 0 j * (Y.kval j : ℂ) := by
    have h1 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • ∑ k, Y.qcoef 0 k • Y.A k := Y.E_eq 0
    rw [h1, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum]
    have hterm : ∀ k : Fin (D + 1), (((Y.qcoef 0 k) • Y.A k) * Y.A j).trace
        = Y.qcoef 0 k * ((Y.scheme.p 0 k j : ℂ) * (Fintype.card X : ℂ)) := by
      intro k
      rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Y.trace_A_mul]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_eq_single j]
    · rw [show Y.scheme.p 0 j j = Y.kval j from rfl, smul_eq_mul]
      field_simp
    · intro k _ hkj
      rw [Y.p_zero_of_ne hX hkj, Nat.cast_zero, zero_mul, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hR : (Y.E 0 * Y.A j).trace = (Y.kval j : ℂ) := by
    rw [Y.E_zero_mul_A hE0, Matrix.trace_smul, smul_eq_mul]
    have htr : (Y.E 0).trace = 1 := by
      rw [hE0, Matrix.trace_smul, smul_eq_mul, trace_allOne]
      field_simp
    rw [htr, mul_one]
  rw [hL] at hR
  exact mul_right_cancel₀ hk' (by rw [hR, one_mul])

/-- Lemma 20.1 (iv): `q_i(0) = mᵢ`; the trace of a projection is its rank. -/
theorem qcoef_zero_col (hX : 0 < Fintype.card X) (i : Fin (D + 1)) :
    Y.qcoef i 0 = (Y.mult i : ℂ) := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have ha : (Y.E i).trace = Y.qcoef i 0 := by
    have h1 : Y.E i = (1 / (Fintype.card X : ℂ)) • ∑ k, Y.qcoef i k • Y.A k := Y.E_eq i
    rw [h1, Matrix.trace_smul, Matrix.trace_sum]
    have hterm : ∀ k : Fin (D + 1), ((Y.qcoef i k) • Y.A k).trace
        = Y.qcoef i k * (if k = 0 then (Fintype.card X : ℂ) else 0) := by
      intro k
      rw [Matrix.trace_smul, smul_eq_mul, Y.trace_A]
    rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_eq_single 0]
    · rw [if_pos rfl, smul_eq_mul]
      field_simp
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (D + 1))) h
  have hb : (Y.E i).trace = (Y.mult i : ℂ) := by
    have hidem : IsIdempotentElem (Y.E i).mulVecLin := by
      show (Y.E i).mulVecLin * (Y.E i).mulVecLin = (Y.E i).mulVecLin
      rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, Y.E_idem i]
    have hproj : LinearMap.IsProj (LinearMap.range (Y.E i).mulVecLin) (Y.E i).mulVecLin :=
      (LinearMap.isProj_range_iff_isIdempotentElem (Y.E i).mulVecLin).mpr hidem
    have h1 := hproj.trace
    have h2 : LinearMap.trace ℂ (X → ℂ) (Y.E i).mulVecLin = (Y.E i).trace := by
      have h3 := Matrix.trace_toLin'_eq (Y.E i)
      simpa only [Matrix.toLin'_apply'] using h3
    rw [h2] at h1
    exact h1
  rw [← ha, hb]

/-- A class with a pair of vertices has nonzero valency. -/
theorem kval_ne_zero_of_rel {j : Fin (D + 1)} (h : ∃ x y, Y.scheme.rel j x y) :
    Y.kval j ≠ 0 := by
  obtain ⟨x, y, hxy⟩ := h
  intro h0
  have hpos : 0 < (Finset.univ.filter fun y => Y.scheme.rel j x y).card :=
    Finset.card_pos.mpr ⟨y, by simp [hxy]⟩
  rw [Y.card_rel_row, h0] at hpos
  exact lt_irrefl 0 hpos


/-! ### The idempotents form a basis, so every class is nonempty

The draft's `SchemeData` does not record that the `Eᵢ` form a *basis* of the Bose–Mesner algebra
(Chapter 19) nor that `E₀ = |X|⁻¹J`; the next three lemmas derive the consequences used above:
`Eᵢ ≠ 0` for all `i` forces `R_i ≠ ∅` for all `i` (so the extra hypothesis `hrel` of Lemma 20.1
is automatic). -/

/-- Orthogonal nonzero idempotents are linearly independent. -/
theorem linearIndependent_E (hne : ∀ j, Y.E j ≠ 0) :
    LinearIndependent ℂ (fun i => Y.E i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have h2 : (∑ i : Fin (D + 1), g i • (Y.E k * Y.E i)) = g k • Y.E k := by
    rw [Finset.sum_eq_single k]
    · rw [Y.E_idem]
    · intro i _ hik
      rw [Y.E_orth k i (Ne.symm hik), smul_zero]
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  have h3 : (∑ i : Fin (D + 1), g i • (Y.E k * Y.E i))
      = Y.E k * (∑ i : Fin (D + 1), g i • Y.E i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [Matrix.mul_smul]
  have h : (∑ i : Fin (D + 1), g i • (Y.E k * Y.E i)) = 0 := by
    rw [h3, hg, Matrix.mul_zero]
  rw [h2] at h
  rcases smul_eq_zero.1 h with h' | h'
  · exact h'
  · exact absurd h' (hne k)

/-- The Bose–Mesner algebra has dimension `D + 1` when all `Eᵢ` are nonzero. -/
theorem finrank_boseMesner (hne : ∀ j, Y.E j ≠ 0) :
    Module.finrank ℂ ↥Y.scheme.boseMesnerSubmodule = D + 1 := by
  have hVE : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (fun i => Y.E i))) = D + 1 := by
    rw [finrank_span_eq_card (Y.linearIndependent_E hne)]
    simp
  have hle1 : Submodule.span ℂ (Set.range (fun i => Y.E i)) ≤ Y.scheme.boseMesnerSubmodule := by
    rw [Submodule.span_le]
    rintro M ⟨i, rfl⟩
    exact Y.E_mem i
  have hle2 : Y.scheme.boseMesnerSubmodule ≤ Submodule.span ℂ (Set.range (fun i => Y.E i)) := by
    rw [show Y.scheme.boseMesnerSubmodule = Submodule.span ℂ (Set.range (fun i => Y.A i)) from rfl,
      Submodule.span_le]
    rintro M ⟨i, rfl⟩
    show Y.A i ∈ Submodule.span ℂ (Set.range (fun i => Y.E i))
    have h1 : Y.A i = ∑ k, Y.pcoef i k • Y.E k := Y.A_eq i
    rw [h1]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h1 := Submodule.finrank_mono hle1
  have h2 := Submodule.finrank_mono hle2
  rw [hVE] at h1
  omega

/-- Every class of the scheme is nonempty when all `Eᵢ` are nonzero. -/
theorem rel_exists_of_E_ne_zero (hne : ∀ j, Y.E j ≠ 0) (j : Fin (D + 1)) :
    ∃ x y, Y.scheme.rel j x y := by
  classical
  by_contra hc
  push_neg at hc
  have hzero : Y.A j = 0 := by
    ext x y
    rw [Y.A_apply, Matrix.zero_apply, if_neg (hc x y)]
  have hsub : Y.scheme.boseMesnerSubmodule
      ≤ Submodule.span ℂ (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i)) := by
    rw [show Y.scheme.boseMesnerSubmodule = Submodule.span ℂ (Set.range (fun i => Y.A i)) from rfl,
      Submodule.span_le]
    rintro M ⟨i, rfl⟩
    by_cases hi : i = j
    · show Y.A i ∈ _
      rw [hi, hzero]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
  have h1 : Module.finrank ℂ ↥Y.scheme.boseMesnerSubmodule
      ≤ Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i))) :=
    Submodule.finrank_mono hsub
  have h2 : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i)))
      ≤ Fintype.card {i : Fin (D + 1) // i ≠ j} := by
    have h3 := finrank_span_le_card (R := ℂ)
      (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i))
    have h4 : (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i)).toFinset.card
        ≤ Fintype.card {i : Fin (D + 1) // i ≠ j} := by
      have hsub2 : (Set.range (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i)).toFinset
          ⊆ Finset.univ.image (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i) := by
        intro z hz
        simp only [Set.mem_toFinset, Set.mem_range] at hz
        obtain ⟨i, rfl⟩ := hz
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      have h5 : (Finset.univ.image (fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i)).card
          ≤ Fintype.card {i : Fin (D + 1) // i ≠ j} := by
        simpa using Finset.card_image_le
          (f := fun i : {i : Fin (D + 1) // i ≠ j} => Y.A i) (s := Finset.univ)
      exact le_trans (Finset.card_le_card hsub2) h5
    exact le_trans h3 h4
  have h5 : Fintype.card {i : Fin (D + 1) // i ≠ j} = D := by
    simp [Fintype.card_subtype_compl]
  have hfin := Y.finrank_boseMesner hne
  omega

/-- **Lemma 20.1.**  `p_0(j) = 1`, `p_i(0) = kᵢ`, `q_0(j) = 1`, `q_i(0) = mᵢ`.

Hypotheses (reported as additions to the draft statement, see the report): `X` is nonempty, `E₀`
is the trivial idempotent `|X|⁻¹J` (Lemma 19.1), and all `Eᵢ` are nonzero (Lemma 19.1: they form
a basis).  From `Eᵢ ≠ 0` we derive that every class is nonempty (`rel_exists_of_E_ne_zero`). -/
theorem p_zero_q_zero (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) :
    (∀ j, Y.pcoef 0 j = 1) ∧ (∀ i, Y.pcoef i 0 = (Y.kval i : ℂ)) ∧
      (∀ j, Y.qcoef 0 j = 1) ∧ (∀ i, Y.qcoef i 0 = (Y.mult i : ℂ)) :=
  ⟨Y.pcoef_zero_row hne, Y.pcoef_zero_col hX hE0,
    fun j => Y.qcoef_zero_row hX hE0 (fun j => Y.kval_ne_zero_of_rel (Y.rel_exists_of_E_ne_zero hne j)) j,
    Y.qcoef_zero_col hX⟩

/-- **Lemma 20.2.**  The symmetry relations for `p^h_{ij}` and `q^h_{ij}`, for a
symmetric commutative scheme (so that `i' = i` and `ĥ = h`). -/
theorem p_symmetry (hX : 0 < Fintype.card X) :
    (∀ i j h, Y.scheme.p h i j = Y.scheme.p h j i) ∧
      (∀ i j h, (Y.kval h : ℂ) * (Y.scheme.p h i j : ℂ)
        = (Y.kval j : ℂ) * (Y.scheme.p j i h : ℂ)) := by
  refine ⟨fun i j h => Y.scheme.p_comm h i j, fun i j h => ?_⟩
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have e1 := Y.trace_A_mul_A_mul hX i j h
  have e2 := Y.trace_A_mul_A_mul hX h i j
  have cyc : ((Y.A i * Y.A j) * Y.A h).trace = ((Y.A h * Y.A i) * Y.A j).trace :=
    Matrix.trace_mul_cycle (Y.A i) (Y.A j) (Y.A h)
  rw [e1, e2] at cyc
  have hkey : (Y.scheme.p h i j : ℂ) * (Y.kval h : ℂ)
      = (Y.scheme.p j h i : ℂ) * (Y.kval j : ℂ) :=
    mul_right_cancel₀ hcard (by rw [mul_assoc, mul_assoc]; exact cyc)
  calc (Y.kval h : ℂ) * (Y.scheme.p h i j : ℂ)
      = (Y.scheme.p h i j : ℂ) * (Y.kval h : ℂ) := mul_comm _ _
    _ = (Y.scheme.p j h i : ℂ) * (Y.kval j : ℂ) := hkey
    _ = (Y.kval j : ℂ) * (Y.scheme.p j h i : ℂ) := mul_comm _ _
    _ = (Y.kval j : ℂ) * (Y.scheme.p j i h : ℂ) := by rw [Y.scheme.p_comm j h i]

/- **Lemma 20.3 and Corollary 20.4** are stated and proved *after* the auxiliary
eigenspace lemmas below (they need `r2e_diagonal_col_eq`), immediately before
Lemma 21.1.  See the deviations recorded there. -/

/-- Entrywise (Hadamard) product of vectors. -/
def circleMul (u v : X → ℂ) : X → ℂ := fun x => u x * v x

/-- The eigenspace `E_jV`. -/
def eigenspace (j : Fin (D + 1)) : Submodule ℂ (X → ℂ) :=
  LinearMap.range (Y.E j).mulVecLin

/-! ## Auxiliaries for Lemma 21.1 and Lemma 23.4 (R2e) -/

/-- `|X|` is nonzero in `ℂ` as soon as `X` has a point. -/
theorem r2e_card_ne_zero (a : X) : (Fintype.card X : ℂ) ≠ 0 := by
  haveI : Nonempty X := ⟨a⟩
  exact Nat.cast_ne_zero.mpr (Fintype.card_pos (α := X)).ne'

/-- Membership in the eigenspace `E_jV`. -/
theorem r2e_mem_eigenspace {j : Fin (D + 1)} {u : X → ℂ} :
    u ∈ Y.eigenspace j ↔ ∃ x, Y.E j *ᵥ x = u := by
  show u ∈ LinearMap.range (Y.E j).mulVecLin ↔ _
  rw [LinearMap.mem_range]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, by rwa [Matrix.mulVecLin_apply] at hx⟩,
    fun ⟨x, hx⟩ => ⟨x, by rwa [Matrix.mulVecLin_apply]⟩⟩

/-- `circleMul` is multiplication by the diagonal matrix. -/
theorem r2e_circleMul_eq_diagonal (u v : X → ℂ) :
    circleMul u v = Matrix.diagonal u *ᵥ v := by
  funext z
  rw [Matrix.mulVec_diagonal]
  rfl

/-- The `b`-th column of `E j` is `E j *ᵥ e_b`. -/
theorem r2e_col (j : Fin (D + 1)) (b : X) :
    Y.E j *ᵥ (Pi.single b (1 : ℂ)) = fun z => Y.E j z b := by
  rw [Matrix.mulVec_single]
  funext z
  simp [Matrix.col_apply]

/-- The `(x,y)` entry of `E j` on the relation `R_i` is `|X|⁻¹ q_j(i)`. -/
theorem r2e_E_apply_of_rel {j i : Fin (D + 1)} {x y : X} (h : Y.scheme.rel i x y) :
    Y.E j x y = (1 / (Fintype.card X : ℂ)) * Y.qcoef j i := by
  have hsum : ∑ k, Y.qcoef j k * Y.scheme.assocMatrix k x y = Y.qcoef j i := by
    obtain ⟨i₀, hi₀, huniq⟩ := Y.scheme.rel_total x y
    have hii : i = i₀ := huniq i h
    subst hii
    rw [Finset.sum_eq_single i]
    · rw [show Y.scheme.assocMatrix i x y = 1 by
        rw [AssociationScheme.assocMatrix_apply, if_pos hi₀]]
      ring
    · intro k _ hk
      rw [show Y.scheme.assocMatrix k x y = 0 by
        rw [AssociationScheme.assocMatrix_apply, if_neg]
        intro hkx
        exact hk (huniq k hkx)]
      ring
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hE := Y.E_eq j
  rw [show Y.E j = (1 / (Fintype.card X : ℂ)) •
      ∑ k, Y.qcoef j k • Y.scheme.assocMatrix k from hE]
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [hsum]

/-- The diagonal of `dualA a j` is `|X|` times the `a`-th column of `E j`. -/
theorem r2e_dualA_apply_self (a z : X) (j : Fin (D + 1)) :
    Y.dualA a j z z = (Fintype.card X : ℂ) * Y.E j z a := by
  have hdual : Y.dualA a j z z
      = ∑ h, Y.qcoef j h * (if Y.scheme.rel h a z then 1 else 0) := by
    simp only [SchemeData.dualA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [SchemeData.dualIdem, Matrix.diagonal_apply, if_pos rfl]
  rw [hdual]
  obtain ⟨h₀, hh₀, huniq⟩ := Y.scheme.rel_total a z
  have hsum : ∑ h, Y.qcoef j h * (if Y.scheme.rel h a z then 1 else 0) = Y.qcoef j h₀ := by
    rw [Finset.sum_eq_single h₀]
    · rw [if_pos hh₀, mul_one]
    · intro h _ hh
      rw [if_neg (fun hrel => hh (huniq h hrel)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ h₀) h
  rw [hsum]
  have hrel' : Y.scheme.rel h₀ z a := (Y.symm h₀ a z).mp hh₀
  have hE := r2e_E_apply_of_rel Y (j := j) (i := h₀) (x := z) (y := a) hrel'
  rw [hE, one_div, ← mul_assoc, mul_inv_cancel₀ (r2e_card_ne_zero a), one_mul]

/-- `dualA a j` is `|X|` times the diagonal matrix of the `a`-th column of `E j`. -/
theorem r2e_diagonal_col_eq (a : X) (j : Fin (D + 1)) :
    Matrix.diagonal (fun z => Y.E j z a) = (1 / (Fintype.card X : ℂ)) • Y.dualA a j := by
  ext z z'
  simp only [Matrix.diagonal_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : z = z'
  · subst h
    rw [if_pos rfl, r2e_dualA_apply_self Y a z j, one_div, ← mul_assoc,
      inv_mul_cancel₀ (r2e_card_ne_zero a), one_mul]
  · rw [if_neg h]
    have hz : Y.dualA a j z z' = 0 := by
      simp only [SchemeData.dualA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [SchemeData.dualIdem, Matrix.diagonal_apply, if_neg h, mul_zero]
    rw [hz, mul_zero]

/-- `|X|` is nonzero in `ℂ` for a nonempty `X`. -/
theorem r2d_card_ne (hX : 0 < Fintype.card X) :
    (Fintype.card X : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)

/-- The association matrices are symmetric. -/
theorem r2d_A_transpose (j : Fin (D + 1)) : (Y.A j)ᵀ = Y.A j := by
  ext x y
  rw [Matrix.transpose_apply, Y.A_apply, Y.A_apply]
  exact if_congr (Y.symm j x y).symm rfl rfl

/-- Every element of the Bose–Mesner algebra is symmetric. -/
theorem r2d_boseMesner_transpose {M : Matrix X X ℂ}
    (hM : M ∈ Y.scheme.boseMesnerSubmodule) : Mᵀ = M := by
  induction hM using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨j, rfl⟩ := hx
      exact r2d_A_transpose Y j
  | zero => rw [Matrix.transpose_zero]
  | add a b _ _ ha hb => rw [Matrix.transpose_add, ha, hb]
  | smul c a _ ha => rw [Matrix.transpose_smul, ha]

/-- The primitive idempotents are symmetric. -/
theorem r2d_E_transpose (i : Fin (D + 1)) : (Y.E i)ᵀ = Y.E i :=
  r2d_boseMesner_transpose Y (Y.E_mem i)

/-- The primitive idempotents are real (given that they are self-adjoint). -/
theorem r2d_E_conj (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (i : Fin (D + 1)) (x y : X) :
    (starRingEnd ℂ) (Y.E i x y) = Y.E i x y := by
  have h := congrFun (congrFun (hherm i) y) x
  rw [Matrix.conjTranspose_apply] at h
  have hsym : Y.E i y x = Y.E i x y := by
    have h2 : (Y.E i)ᵀ x y = (Y.E i) x y := by rw [r2d_E_transpose Y i]
    rwa [Matrix.transpose_apply] at h2
  change star (Y.E i x y) = Y.E i x y
  rw [h]
  exact hsym

/-- The trace of the primitive idempotent `Eᵢ` is its multiplicity `mᵢ`. -/
theorem r2d_trace_E (i : Fin (D + 1)) : (Y.E i).trace = (Y.mult i : ℂ) := by
  have hidem : IsIdempotentElem (Y.E i).mulVecLin := by
    show (Y.E i).mulVecLin * (Y.E i).mulVecLin = (Y.E i).mulVecLin
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, Y.E_idem i]
  have hproj : LinearMap.IsProj (LinearMap.range (Y.E i).mulVecLin) (Y.E i).mulVecLin :=
    (LinearMap.isProj_range_iff_isIdempotentElem (Y.E i).mulVecLin).mpr hidem
  have h1 := hproj.trace
  have h2 : LinearMap.trace ℂ (X → ℂ) (Y.E i).mulVecLin = (Y.E i).trace := by
    have h3 := Matrix.trace_toLin'_eq (Y.E i)
    simpa only [Matrix.toLin'_apply'] using h3
  rw [h2] at h1
  exact h1

/-- A nonzero idempotent has nonzero multiplicity. -/
theorem r2d_mult_ne_zero (hne : ∀ j, Y.E j ≠ 0) (i : Fin (D + 1)) : Y.mult i ≠ 0 := by
  intro h0
  apply hne i
  have h1 : LinearMap.range (Y.E i).mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    exact h0
  rw [LinearMap.range_eq_bot] at h1
  apply Matrix.toLin'.injective
  show Matrix.toLin' (Y.E i) = Matrix.toLin' 0
  simp [Matrix.toLin'_apply', h1]


/-- Every diagonal entry of `Eⱼ` is `|X|⁻¹ mⱼ`. -/
theorem r2d_E_diag (hX : 0 < Fintype.card X) (j : Fin (D + 1)) (x : X) :
    Y.E j x x = (1 / (Fintype.card X : ℂ)) * (Y.mult j : ℂ) := by
  have key : (∑ k, Y.qcoef j k • Y.scheme.assocMatrix k) x x = (Y.mult j : ℂ) := by
    rw [Matrix.sum_apply]
    have h2 : ∀ k : Fin (D + 1),
        (Y.qcoef j k • Y.scheme.assocMatrix k) x x
          = Y.qcoef j k * (if k = 0 then 1 else 0) := by
      intro k
      rw [Matrix.smul_apply, smul_eq_mul, AssociationScheme.assocMatrix_apply,
        if_congr (Y.rel_self_iff k x).symm rfl rfl]
    rw [Finset.sum_congr rfl fun k _ => h2 k, Finset.sum_eq_single (0 : Fin (D + 1))]
    · rw [if_pos rfl, mul_one, Y.qcoef_zero_col hX]
    · intro k _ hk
      rw [if_neg hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin (D + 1))) h
  rw [Y.E_eq j, Matrix.smul_apply, smul_eq_mul, key]

/-- The dual matrix `A*_j(x)` is `|X|` times the diagonal matrix of the `x`-column
of `Eⱼ`. -/
theorem r2d_dualA_eq (hX : 0 < Fintype.card X) (x : X) (j : Fin (D + 1)) :
    Y.dualA x j = (Fintype.card X : ℂ) • Matrix.diagonal (fun z => Y.E j z x) := by
  have hc : (Fintype.card X : ℂ) ≠ 0 := r2d_card_ne hX
  have h := r2e_diagonal_col_eq Y x j
  rw [h, smul_smul, mul_one_div_cancel hc, one_smul]

/-- `A*_j(x)` is self-adjoint. -/
theorem r2d_dualA_herm (hX : 0 < Fintype.card X)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (x : X) (j : Fin (D + 1)) :
    (Y.dualA x j)ᴴ = Y.dualA x j := by
  rw [r2d_dualA_eq Y hX x j, conjTranspose_smul]
  have hc : star (Fintype.card X : ℂ) = (Fintype.card X : ℂ) := by simp
  rw [hc]
  congr 1
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases hab : b = a
  · subst hab
    rw [if_pos rfl]
    exact r2d_E_conj Y hherm j b x
  · rw [if_neg hab, if_neg (Ne.symm hab), star_zero]

/-- The entries of the Hadamard product of two idempotents, expanded in the `E`-basis. -/
theorem r2d_hadamard_apply (a b : Fin (D + 1)) (u v : X) :
    Y.E a u v * Y.E b u v
      = (1 / (Fintype.card X : ℂ)) * ∑ h, Y.krein a b h * Y.E h u v := by
  have h := congrFun (congrFun (Y.hadamard a b) u) v
  simpa [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] using h

/-- `∑_{u,v} (E_a)_{uv}(E_b)_{uv} = δ_{ab} m_a`. -/
theorem r2d_sum_E_mul_E (a b : Fin (D + 1)) :
    ∑ u, ∑ v, Y.E a u v * Y.E b u v
      = if a = b then (Y.mult a : ℂ) else 0 := by
  have h1 : (∑ u, ∑ v, Y.E a u v * Y.E b u v) = ((Y.E a) * (Y.E b)ᵀ).trace := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Matrix.transpose_apply]
  rw [h1, r2d_E_transpose Y b]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, Y.E_idem, r2d_trace_E]
  · rw [if_neg hab, Y.E_orth a b hab, Matrix.trace_zero]

/-- Trace computation: for symmetric `P, Q` with `P` idempotent, the trace of
`P D Q D P` (`D` diagonal) is `∑_{u,v} d u d v (P_{uv} Q_{uv})`. -/
theorem r2d_trace_diag5 (P Q : Matrix X X ℂ) (d : X → ℂ)
    (hP : Pᵀ = P) (hPP : P * P = P) (hQ : Qᵀ = Q) :
    (P * Matrix.diagonal d * Q * Matrix.diagonal d * P).trace
      = ∑ u, ∑ v, d u * d v * (P u v * Q u v) := by
  set Dm : Matrix X X ℂ := Matrix.diagonal d with hDm
  have step1 : (P * Dm * Q * Dm * P).trace = (P * (P * Dm * Q * Dm)).trace := by
    rw [Matrix.trace_mul_comm (P * Dm * Q * Dm) P]
  have e1 : P * (P * Dm * Q * Dm) = P * P * Dm * Q * Dm := by
    simp only [Matrix.mul_assoc]
  have e2 : P * P * Dm * Q * Dm = P * Dm * Q * Dm := by rw [hPP]
  have step2 : (P * Dm * Q * Dm).trace = (Dm * P * Dm * Q).trace := by
    rw [Matrix.trace_mul_comm (P * Dm * Q) Dm]
    have e3 : Dm * (P * Dm * Q) = Dm * P * Dm * Q := by simp only [Matrix.mul_assoc]
    rw [e3]
  rw [step1, e1, e2, step2]
  have hfin : (Dm * P * Dm * Q).trace = ∑ u, ∑ v, d u * P u v * d v * Q v u := by
    rw [Matrix.trace]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hDm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [hfin]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  have hv : Q v u = Q u v := by
    have h2 : Qᵀ u v = Q u v := by rw [hQ]
    rwa [Matrix.transpose_apply] at h2
  rw [hv]
  ring


/-- Symmetry of the idempotents, entrywise. -/
theorem r2d_E_symm_apply (i : Fin (D + 1)) (x y : X) : Y.E i x y = Y.E i y x := by
  have h2 : (Y.E i)ᵀ y x = (Y.E i) y x := by rw [r2d_E_transpose Y i]
  rw [Matrix.transpose_apply] at h2
  exact h2

/-- Entries of a triple product. -/
theorem r2d_mul3_apply (A B C : Matrix X X ℂ) (x : X) :
    (A * B * C) x x = ∑ u, ∑ v, A x v * B v u * C u x := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]

/-- Entries of a triple product, matching the order of `r2d_key2`. -/
theorem r2d_mul3_apply' (A B C : Matrix X X ℂ) (x : X) :
    (A * B * C) x x = ∑ u, ∑ v, A x u * B u v * C v x := by
  rw [r2d_mul3_apply, Finset.sum_comm]

/-- Auxiliary form of the key computation. -/
theorem r2d_key2_aux (A B M : Matrix X X ℂ) (x : X)
    (hB : Bᵀ = B) :
    (∑ u, ∑ v, A x u * B x v * M u v) = (A * M * B) x x := by
  rw [r2d_mul3_apply']
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
  have h1 : B x v = B v x := by
    have h2 : Bᵀ v x = B v x := by rw [hB]
    rw [Matrix.transpose_apply] at h2
    exact h2
  rw [h1]
  ring

/-- **The key Krein computation.** `∑_{u,v} (E_β)_{xu}(E_β)_{xv}(E_α)_{uv}(E_γ)_{uv}
= |X|⁻¹ q^β_{αγ} (E_β)_{xx}`. -/
theorem r2d_key2 (hX : 0 < Fintype.card X) (x : X) (α β γ : Fin (D + 1)) :
    (∑ u, ∑ v, Y.E β x u * Y.E β x v * (Y.E α u v * Y.E γ u v))
      = (1 / (Fintype.card X : ℂ)) * Y.krein α γ β * (Y.E β x x) := by
  rw [r2d_key2_aux (Y.E β) (Y.E β) (fun u v => Y.E α u v * Y.E γ u v) x
    (r2d_E_transpose Y β)]
  rw [Y.hadamard α γ]
  have hmat : (Y.E β * ((1 / (Fintype.card X : ℂ)) •
        ∑ h, Y.krein α γ h • Y.E h) * Y.E β)
      = (1 / (Fintype.card X : ℂ)) • (Y.krein α γ β • Y.E β) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have hfix : ∀ h : Fin (D + 1),
        Y.E β * Y.E h * Y.E β = if h = β then Y.E β else 0 := by
      intro h
      by_cases hb : h = β
      · subst hb
        rw [if_pos rfl, Y.E_idem, Y.E_idem]
      · rw [if_neg hb, Y.E_orth β h (Ne.symm hb), Matrix.zero_mul]
    rw [Matrix.mul_sum, Finset.sum_mul]
    have hstep : ∀ h : Fin (D + 1),
        Y.E β * (Y.krein α γ h • Y.E h) * Y.E β
          = Y.krein α γ h • (if h = β then Y.E β else 0) := by
      intro h
      rw [Matrix.mul_smul, Matrix.smul_mul, hfix]
    rw [Finset.sum_congr rfl fun h _ => hstep h]
    rw [Finset.sum_eq_single β]
    · rw [if_pos rfl]
    · intro h _ hh
      rw [if_neg hh, smul_zero]
    · intro h
      exact absurd (Finset.mem_univ β) h
  rw [hmat, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  ring


/-- **The master identity.** `tr(E_α A*_β(x) E_γ A*_β(x) E_α) = m_β q^β_{αγ}`. -/
theorem r2d_key (hX : 0 < Fintype.card X) (x : X) (α β γ : Fin (D + 1)) :
    (Y.E α * Y.dualA x β * Y.E γ * Y.dualA x β * Y.E α).trace
      = (Y.mult β : ℂ) * Y.krein α γ β := by
  have hc : (Fintype.card X : ℂ) ≠ 0 := r2d_card_ne hX
  have hsym : (∑ u, ∑ v, Y.E β u x * Y.E β v x * (Y.E α u v * Y.E γ u v))
      = (∑ u, ∑ v, Y.E β x u * Y.E β x v * (Y.E α u v * Y.E γ u v)) := by
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [r2d_E_symm_apply Y β u x, r2d_E_symm_apply Y β v x]
  have hD : Y.dualA x β
      = Matrix.diagonal (fun z => (Fintype.card X : ℂ) * Y.E β z x) := by
    rw [r2d_dualA_eq Y hX x β]
    ext a b
    rw [Matrix.smul_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      rw [if_pos rfl, if_pos rfl, smul_eq_mul]
    · rw [if_neg hab, if_neg hab, smul_zero]
  have hfac2 : (∑ u, ∑ v, ((Fintype.card X : ℂ) * Y.E β u x) *
        ((Fintype.card X : ℂ) * Y.E β v x) * (Y.E α u v * Y.E γ u v))
      = (Fintype.card X : ℂ) ^ 2 *
          (∑ u, ∑ v, Y.E β u x * Y.E β v x * (Y.E α u v * Y.E γ u v)) := by
    have h1 : ∀ u v : X, ((Fintype.card X : ℂ) * Y.E β u x) *
        ((Fintype.card X : ℂ) * Y.E β v x) * (Y.E α u v * Y.E γ u v)
        = (Fintype.card X : ℂ) ^ 2 *
            (Y.E β u x * Y.E β v x * (Y.E α u v * Y.E γ u v)) := by
      intro u v
      ring
    rw [Finset.sum_congr rfl (fun u _ => Finset.sum_congr rfl (fun v _ => h1 u v))]
    simp only [Finset.mul_sum]
  rw [hD, r2d_trace_diag5 (Y.E α) (Y.E γ)
      (fun z => (Fintype.card X : ℂ) * Y.E β z x)
      (r2d_E_transpose Y α) (Y.E_idem α) (r2d_E_transpose Y γ), hfac2,
    hsym, r2d_key2 Y hX x α β γ, r2d_E_diag Y hX β x]
  field_simp

/-- `trace (M N)` as an entrywise sum, for symmetric `N`. -/
theorem r2d_trace_mul_apply (M N : Matrix X X ℂ) (hN : Nᵀ = N) :
    (M * N).trace = ∑ u, ∑ v, M u v * N u v := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  have h : N v u = N u v := by
    have h2 : Nᵀ u v = N u v := by rw [hN]
    rw [Matrix.transpose_apply] at h2
    exact h2
  rw [h]

/-- The squared Frobenius norm as a trace. -/
theorem r2d_trace_mul_herm (M : Matrix X X ℂ) :
    (M * Mᴴ).trace = ((∑ u, ∑ v, Complex.normSq (M u v) : ℝ) : ℂ) := by
  rw [Matrix.trace, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Matrix.conjTranspose_apply]
  exact Complex.mul_conj _

/-- `(E_α A*_β E_γ)ᴴ = E_γ A*_β E_α`. -/
theorem r2d_S_herm (hX : 0 < Fintype.card X)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (x : X) (α β γ : Fin (D + 1)) :
    (Y.E α * Y.dualA x β * Y.E γ)ᴴ = Y.E γ * Y.dualA x β * Y.E α := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hherm α, hherm γ,
    r2d_dualA_herm Y hX hherm x β, Matrix.mul_assoc]

/-- `τ₃(a,b,c) = ∑_{u,v} (E_a)_{uv}(E_b)_{uv}(E_c)_{uv} = |X|⁻¹ m_c q^c_{ab}`. -/
theorem r2d_tau3 (hX : 0 < Fintype.card X) (a b cc : Fin (D + 1)) :
    (∑ u, ∑ v, Y.E a u v * Y.E b u v * Y.E cc u v)
      = (1 / (Fintype.card X : ℂ)) * (Y.mult cc : ℂ) * Y.krein a b cc := by
  rw [← r2d_trace_mul_apply (fun u v => Y.E a u v * Y.E b u v) (Y.E cc)
    (r2d_E_transpose Y cc)]
  have hM : (fun u v => Y.E a u v * Y.E b u v)
      = (1 / (Fintype.card X : ℂ)) • ∑ h, Y.krein a b h • Y.E h := Y.hadamard a b
  rw [hM, Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul]
  have hterm : ∀ h : Fin (D + 1),
      ((Y.krein a b h • Y.E h) * Y.E cc).trace
        = Y.krein a b h * (if h = cc then (Y.mult cc : ℂ) else 0) := by
    intro h
    rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
    congr 1
    by_cases hc : h = cc
    · subst hc
      rw [if_pos rfl, Y.E_idem, r2d_trace_E]
    · rw [if_neg hc, Y.E_orth h cc hc, Matrix.trace_zero]
  rw [Finset.sum_congr rfl fun h _ => hterm h, Finset.sum_eq_single cc]
  · rw [if_pos rfl]
    ring
  · intro h _ hh
    rw [if_neg hh, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ cc) h

/-- The cyclic symmetry `m_c q^c_{ab} = m_a q^a_{bc}` (Lemma 20.2 (iv), symmetric case). -/
theorem r2d_krein_cycle (hX : 0 < Fintype.card X) (a b cc : Fin (D + 1)) :
    (Y.mult cc : ℂ) * Y.krein a b cc = (Y.mult a : ℂ) * Y.krein b cc a := by
  have hc : (Fintype.card X : ℂ) ≠ 0 := r2d_card_ne hX
  have h4 : ∀ z : ℂ, (Fintype.card X : ℂ) * ((1 / (Fintype.card X : ℂ)) * z) = z := by
    intro z
    rw [← mul_assoc, mul_one_div_cancel hc, one_mul]
  have h1 := r2d_tau3 Y hX a b cc
  have h2 := r2d_tau3 Y hX b cc a
  have h3 : (∑ u, ∑ v, Y.E a u v * Y.E b u v * Y.E cc u v)
      = (∑ u, ∑ v, Y.E b u v * Y.E cc u v * Y.E a u v) := by
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    ring
  rw [h1, h2] at h3
  have h5 := congrArg (fun z => (Fintype.card X : ℂ) * z) h3
  simp only [mul_assoc] at h5
  rw [h4, h4] at h5
  exact h5

/-- `q^h_{ij} = 0 ↔ q^k_{ji} = 0` for the pair of index conventions. -/
theorem r2d_krein_zero_swap (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (i j k : Fin (D + 1)) : Y.krein i k j = 0 ↔ Y.krein j i k = 0 := by
  have hmj : (Y.mult j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne j)
  have hmk : (Y.mult k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne k)
  have e1 := r2d_krein_cycle Y hX i k j
  have e2 := r2d_krein_cycle Y hX k j i
  constructor
  · intro h0
    rw [h0, mul_zero] at e1
    rw [e2] at e1
    rcases mul_eq_zero.mp e1.symm with h | h
    · exact absurd h hmk
    · exact h
  · intro h0
    rw [h0, mul_zero] at e2
    rw [← e1] at e2
    rcases mul_eq_zero.mp e2 with h | h
    · exact absurd h hmj
    · exact h

/-- **Lemma 20.2 (iii), symmetric case:** `q^h_{ij} = q^h_{ji}`. -/
theorem r2d_krein_swap (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (i j h : Fin (D + 1)) : Y.krein i j h = Y.krein j i h := by
  have hLI := Y.linearIndependent_E hne
  have hc : (Fintype.card X : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have h12 : (1 / (Fintype.card X : ℂ)) • ∑ k, Y.krein i j k • Y.E k
      = (1 / (Fintype.card X : ℂ)) • ∑ k, Y.krein j i k • Y.E k := by
    rw [← Y.hadamard i j, ← Y.hadamard j i]
    funext a b
    ring
  have heq : (∑ k, Y.krein i j k • Y.E k) = (∑ k, Y.krein j i k • Y.E k) := by
    have h3 := congrArg (fun M => (Fintype.card X : ℂ) • M) h12
    rw [smul_smul, smul_smul, mul_one_div_cancel hc, one_smul, one_smul] at h3
    exact h3
  have hzero : (∑ k, (Y.krein i j k - Y.krein j i k) • Y.E k) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
  have h := (Fintype.linearIndependent_iff.mp hLI)
    (fun k => Y.krein i j k - Y.krein j i k) hzero h
  exact sub_eq_zero.mp h

/-- **Lemma 20.2 (iv), symmetric case:** `m_h q^h_{ij} = m_j q^j_{ih}`. -/
theorem r2d_krein_smul_swap_last (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (i j h : Fin (D + 1)) :
    (Y.mult h : ℂ) * Y.krein i j h = (Y.mult j : ℂ) * Y.krein i h j := by
  have e1 := r2d_krein_cycle Y hX i j h
  have e2 := r2d_krein_swap Y hX hne j h i
  have e3 := r2d_krein_cycle Y hX i h j
  rw [e2, ← e3] at e1
  exact e1

/-- `q^h_{ij} = 0 ↔ q^j_{ih} = 0`. -/
theorem r2d_krein_zero_perm (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (i j h : Fin (D + 1)) : Y.krein i j h = 0 ↔ Y.krein i h j = 0 := by
  have hmj : (Y.mult j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne j)
  have hmh : (Y.mult h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne h)
  have e := r2d_krein_smul_swap_last Y hX hne i j h
  constructor
  · intro h0
    rw [h0, mul_zero] at e
    rcases mul_eq_zero.mp e.symm with h1 | h1
    · exact absurd h1 hmj
    · exact h1
  · intro h0
    rw [h0, mul_zero] at e
    rcases mul_eq_zero.mp e with h1 | h1
    · exact absurd h1 hmh
    · exact h1

/-- `q^h_{ij} ≠ 0 ↔ q^j_{ih} ≠ 0`. -/
theorem r2d_krein_ne_zero_perm (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (i j h : Fin (D + 1)) : Y.krein i j h ≠ 0 ↔ Y.krein i h j ≠ 0 :=
  not_congr (r2d_krein_zero_perm Y hX hne i j h)

/-- **Corollary 20.4 (Krein condition).**  `q^h_{ij}` is a nonnegative real.

DEVIATIONS (draft statement refutable — see the wave-2 audit):
* the draft `theorem krein_nonneg (i j h : Fin (D + 1))` fails when some `E h = 0`
  (one-point scheme, `D = 1`, `E 1 = 0`, `krein 1 1 1 = -1` is consistent with every
  field of `SchemeData`), so we add `hne : ∀ h, Y.E h ≠ 0` (wave-2 fix 4);
* `hX : 0 < Fintype.card X` is needed because the computation is carried out at a
  vertex `x` and divides by `|X|`;
* `hherm : ∀ i, (E i)ᴴ = E i` is needed because the notes' argument identifies
  `q^h_{ij} m_h` with the sum of the squared absolute values of the entries of
  `E_i A*_j E_h`, which uses `(E_i A*_j E_h)ᴴ = E_h A*_j E_i`; `SchemeData` implies
  that the `Eᵢ` are *symmetric* (proved as `r2d_E_transpose`) but not that they are
  real/Hermitian.

Route: `r2d_key` (`tr(E_α A*_β E_γ A*_β E_α) = m_β q^β_{αγ}`) combined with
`r2d_trace_mul_herm` (`tr(M Mᴴ) = ∑_{u,v} |M_{uv}|²`). -/
theorem krein_nonneg (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (i j h : Fin (D + 1)) :
    ∃ r : ℝ, 0 ≤ r ∧ Y.krein i j h = (r : ℂ) := by
  obtain ⟨x⟩ := Fintype.card_pos_iff.mp hX
  have hm : (Y.mult h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne h)
  have hassoc : (Y.E i * Y.dualA x h * Y.E j) * (Y.E j * Y.dualA x h * Y.E i)
      = (Y.E i * Y.dualA x h * Y.E j * Y.dualA x h * Y.E i) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Y.E j) (Y.E j) (Y.dualA x h * Y.E i), Y.E_idem j]
  have hkey : ((Y.E i * Y.dualA x h * Y.E j) * (Y.E i * Y.dualA x h * Y.E j)ᴴ).trace
      = (Y.mult h : ℂ) * Y.krein i j h := by
    rw [r2d_S_herm Y hX hherm x i h j, hassoc]
    exact r2d_key Y hX x i h j
  have hnorm := r2d_trace_mul_herm (Y.E i * Y.dualA x h * Y.E j)
  rw [hkey] at hnorm
  refine ⟨(∑ u, ∑ v, Complex.normSq ((Y.E i * Y.dualA x h * Y.E j) u v)) /
      (Y.mult h : ℝ), div_nonneg ?_ (by positivity), ?_⟩
  · exact Finset.sum_nonneg fun u _ =>
      Finset.sum_nonneg fun v _ => Complex.normSq_nonneg _
  · rw [Complex.ofReal_div, Complex.ofReal_natCast, eq_div_iff hm, mul_comm]
    exact hnorm

/-! ### The `p`-side of Lemma 20.3 (salvaged from the wave-1 `p`-side proofs) -/

/-- The `(u,v)` entry of `E*_i A_j E*_k`. -/
theorem r2d_entry (x u v : X) (i j k : Fin (D + 1)) :
    (Y.dualIdem x i * Y.A j * Y.dualIdem x k) u v
      = if Y.scheme.rel i x u then
          (if Y.scheme.rel j u v then (if Y.scheme.rel k x v then 1 else 0) else 0)
        else 0 := by
  simp only [SchemeData.dualIdem]
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Y.A_apply]
  by_cases h1 : Y.scheme.rel i x u <;> by_cases h2 : Y.scheme.rel j u v <;>
    by_cases h3 : Y.scheme.rel k x v <;> simp [h1, h2, h3]

/-- `E*_i A_j E*_k = 0` iff there is no triple `x ~i u ~j v ~k x`. -/
theorem r2d_eq_zero_iff (x : X) (i j k : Fin (D + 1)) :
    (Y.dualIdem x i * Y.A j * Y.dualIdem x k = 0) ↔
      ¬ ∃ u v : X, Y.scheme.rel i x u ∧ Y.scheme.rel j u v ∧ Y.scheme.rel k x v := by
  constructor
  · rintro h ⟨u, v, h1, h2, h3⟩
    have hh := congrFun (congrFun h u) v
    rw [r2d_entry Y x u v i j k, if_pos h1, if_pos h2, if_pos h3, Matrix.zero_apply] at hh
    exact one_ne_zero hh
  · rintro h
    ext u v
    rw [r2d_entry Y x u v i j k, Matrix.zero_apply]
    by_cases h1 : Y.scheme.rel i x u
    · by_cases h2 : Y.scheme.rel j u v
      · by_cases h3 : Y.scheme.rel k x v
        · exact absurd ⟨u, v, h1, h2, h3⟩ h
        · simp [h1, h2, h3]
      · simp [h1, h2]
    · simp [h1]

/-- The valency as a count of the relation. -/
theorem r2d_val_card (x : X) (k : Fin (D + 1)) :
    (Finset.univ.filter fun z => Y.scheme.rel k x z).card = Y.scheme.p 0 k k := by
  have hz : (Finset.univ.filter fun z => Y.scheme.rel k x z ∧ Y.scheme.rel k z x).card
      = Y.scheme.p 0 k k := Y.scheme.p_spec 0 k k x x ((Y.scheme.rel_zero x x).mpr rfl)
  rw [← hz]
  congr 1
  apply Finset.filter_congr
  intro z _
  exact ⟨fun h => ⟨h, (Y.symm k z x).mpr h⟩, fun h => h.1⟩

/-- Lemma 20.3 (i): `E*_i A_j E*_k = 0 ↔ p^k_{ij} = 0` (for `R_k(x) ≠ ∅`). -/
theorem r2d_vanishing_p (x : X) (i j k : Fin (D + 1))
    (hk : ∃ z : X, Y.scheme.rel k x z) :
    (Y.dualIdem x i * Y.A j * Y.dualIdem x k = 0 ↔ Y.scheme.p k i j = 0) := by
  rw [r2d_eq_zero_iff]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := hk
    have hspec := Y.scheme.p_spec k i j x z hz
    have hcard : (Finset.univ.filter fun w => Y.scheme.rel i x w ∧ Y.scheme.rel j w z).card = 0 := by
      by_contra hne
      obtain ⟨w, hw⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hne)
      rw [Finset.mem_filter] at hw
      exact h ⟨w, z, hw.2.1, hw.2.2, hz⟩
    rw [hcard] at hspec
    omega
  · rintro hp ⟨u, v, h1, h2, h3⟩
    have hspec := Y.scheme.p_spec k i j x v h3
    have hmem : u ∈ Finset.univ.filter (fun w => Y.scheme.rel i x w ∧ Y.scheme.rel j w v) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ u, h1, h2⟩
    have hpos : 0 < (Finset.univ.filter fun w => Y.scheme.rel i x w ∧ Y.scheme.rel j w v).card :=
      Finset.card_pos.mpr ⟨u, hmem⟩
    rw [hspec] at hpos
    omega


/-- One direction of Lemma 20.3 (ii), with no hypothesis on the `Eᵢ`:
`q^β_{αγ} = 0` kills `E_α A*_β E_γ`.  (Used by Lemma 21.1, which cannot carry `hne`.) -/
theorem r2d_krein_zero_implies (hX : 0 < Fintype.card X)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (x : X) (α β γ : Fin (D + 1))
    (h0 : Y.krein α γ β = 0) : Y.E α * Y.dualA x β * Y.E γ = 0 := by
  have hassoc : (Y.E α * Y.dualA x β * Y.E γ) * (Y.E γ * Y.dualA x β * Y.E α)
      = (Y.E α * Y.dualA x β * Y.E γ * Y.dualA x β * Y.E α) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Y.E γ) (Y.E γ) (Y.dualA x β * Y.E α), Y.E_idem γ]
  have hkey : ((Y.E α * Y.dualA x β * Y.E γ) * (Y.E α * Y.dualA x β * Y.E γ)ᴴ).trace
      = (Y.mult β : ℂ) * Y.krein α γ β := by
    rw [r2d_S_herm Y hX hherm x α β γ, hassoc]
    exact r2d_key Y hX x α β γ
  have hnorm := r2d_trace_mul_herm (Y.E α * Y.dualA x β * Y.E γ)
  rw [hkey, h0, mul_zero] at hnorm
  have hsum : (∑ u, ∑ v, Complex.normSq ((Y.E α * Y.dualA x β * Y.E γ) u v) : ℝ) = 0 := by
    exact_mod_cast hnorm.symm
  ext u v
  have h1 : ∀ u ∈ (Finset.univ : Finset X),
      (∑ v, Complex.normSq ((Y.E α * Y.dualA x β * Y.E γ) u v)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun u _ => Finset.sum_nonneg fun v _ => Complex.normSq_nonneg _)).mp hsum
  have h2 : Complex.normSq ((Y.E α * Y.dualA x β * Y.E γ) u v) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => Complex.normSq_nonneg _)).mp (h1 u (Finset.mem_univ u)) v (Finset.mem_univ v)
  rw [Matrix.zero_apply]
  exact Complex.normSq_eq_zero.mp h2

/-- **Lemma 20.3 (vanishing conditions).**  `E*_iA_jE*_k = 0 ↔ p^k_{ij} = 0` and
`E_iA*_jE_k = 0 ↔ q^k_{ji} = 0`.

DEVIATIONS (the draft statement is refutable — wave-2 fixes 3–4 plus one further
hypothesis):
* (i) fails when `R_k(x) = ∅`: then `E*_iA_jE*_k = 0` while `p^k_{ij}` is not
  constrained by the axioms.  We add `hk : ∃ z, Y.scheme.rel k x z` (fix 3).
* (ii) fails when `E_j = 0` (the parameter `q` is then unconstrained); we add
  `hne : ∀ h, Y.E h ≠ 0` (fix 4), which gives `m_j ≠ 0`.
* `hherm : ∀ i, (E i)ᴴ = E i` is needed for the same reason as in 20.4 (the notes'
  norm computation conjugates the idempotents; `SchemeData` gives symmetry only).
  No separate `0 < |X|` is needed: it follows from `hk`.

Route: (i) is a block-matrix count (`r2d_entry`, `r2d_eq_zero_iff`, `r2d_vanishing_p`);
(ii) is `r2d_key` + `r2d_trace_mul_herm` (as in 20.4) together with the cyclic
symmetry `r2d_krein_cycle` / `r2d_krein_zero_swap` which converts `q^j_{ik}`
(the index produced by the trace identity) into `q^k_{ji}`. -/
theorem vanishing_condition (hne : ∀ j, Y.E j ≠ 0)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j) (x : X) (i j k : Fin (D + 1))
    (hk : ∃ z : X, Y.scheme.rel k x z) :
    (Y.dualIdem x i * Y.A j * Y.dualIdem x k = 0 ↔ Y.scheme.p k i j = 0) ∧
      (Y.Eidem i * Y.dualA x j * Y.Eidem k = 0 ↔ Y.krein j i k = 0) := by
  have hX : 0 < Fintype.card X := by
    obtain ⟨z, _⟩ := hk
    exact Fintype.card_pos_iff.mpr ⟨z⟩
  refine ⟨r2d_vanishing_p Y x i j k hk, ?_⟩
  have hmj : (Y.mult j : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (r2d_mult_ne_zero Y hne j)
  have hassoc : (Y.E i * Y.dualA x j * Y.E k) * (Y.E k * Y.dualA x j * Y.E i)
      = (Y.E i * Y.dualA x j * Y.E k * Y.dualA x j * Y.E i) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (Y.E k) (Y.E k) (Y.dualA x j * Y.E i), Y.E_idem k]
  have hkey2 : ((Y.E i * Y.dualA x j * Y.E k) * (Y.E i * Y.dualA x j * Y.E k)ᴴ).trace
      = (Y.mult j : ℂ) * Y.krein i k j := by
    rw [r2d_S_herm Y hX hherm x i j k, hassoc]
    exact r2d_key Y hX x i j k
  have hnorm := r2d_trace_mul_herm (Y.E i * Y.dualA x j * Y.E k)
  rw [hkey2] at hnorm
  -- hnorm : ↑m_j * krein i k j = ↑N
  constructor
  · intro hS
    have hS' : Y.E i * Y.dualA x j * Y.E k = 0 := hS
    have h0 : Y.krein i k j = 0 := by
      have h2 : ((Y.E i * Y.dualA x j * Y.E k) *
          (Y.E i * Y.dualA x j * Y.E k)ᴴ).trace = 0 := by
        rw [hS']
        simp
      rw [hkey2] at h2
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h hmj
      · exact h
    exact (r2d_krein_zero_swap Y hX hne i j k).mp h0
  · intro h0
    have h0' : Y.krein i k j = 0 := (r2d_krein_zero_swap Y hX hne i j k).mpr h0
    rw [h0', mul_zero] at hnorm
    have hsum : (∑ u, ∑ v, Complex.normSq ((Y.E i * Y.dualA x j * Y.E k) u v) : ℝ) = 0 := by
      exact_mod_cast hnorm.symm
    ext u v
    have h1 : ∀ u ∈ (Finset.univ : Finset X),
        (∑ v, Complex.normSq ((Y.E i * Y.dualA x j * Y.E k) u v)) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun u _ => Finset.sum_nonneg fun v _ => Complex.normSq_nonneg _)).mp hsum
    have h2 : Complex.normSq ((Y.E i * Y.dualA x j * Y.E k) u v) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => Complex.normSq_nonneg _)).mp (h1 u (Finset.mem_univ u)) v (Finset.mem_univ v)
    rw [Matrix.zero_apply]
    exact Complex.normSq_eq_zero.mp h2

/-- Forward direction of Lemma 21.1: vanishing Norton product forces
`q^j_{jj} = 0`.  Uses only `hadamard` (the definition of the Krein parameters). -/
theorem r2e_norton_forward (j : Fin (D + 1)) (hj : Y.E j ≠ 0)
    (hL : ∀ u ∈ Y.eigenspace j, ∀ v ∈ Y.eigenspace j,
      Y.E j *ᵥ circleMul u v = 0) :
    Y.krein j j j = 0 := by
  have hne : Nonempty X := by
    by_contra h
    haveI : IsEmpty X := not_nonempty_iff.mp h
    exact hj (Subsingleton.elim (Y.E j) 0)
  haveI := hne
  have hcard : (Fintype.card X : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos (α := X)).ne'
  have hW : ∀ a b : X, ∑ z, Y.E j a z * (Y.E j z b * Y.E j z b) = 0 := by
    intro a b
    have hb : (fun z => Y.E j z b) ∈ Y.eigenspace j := by
      rw [r2e_mem_eigenspace Y]
      exact ⟨Pi.single b 1, r2e_col Y j b⟩
    have h0 := congrFun (hL _ hb _ hb) a
    simp only [circleMul, Matrix.mulVec, dotProduct, Pi.zero_apply] at h0
    exact h0
  have hW2 : ∀ a b : X, ∑ z, Y.E j a z * (Y.E j z b * Y.E j z b)
      = (1 / (Fintype.card X : ℂ)) * (Y.krein j j j * Y.E j a b) := by
    intro a b
    have h1 : ∀ z, Y.E j z b * Y.E j z b
        = (1 / (Fintype.card X : ℂ)) * ∑ h, Y.krein j j h * Y.E h z b := by
      intro z
      have hh := congrFun (congrFun (Y.hadamard j j) z) b
      simpa [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] using hh
    have h2 : (∑ z, Y.E j a z * ∑ h, Y.krein j j h * Y.E h z b)
        = ∑ h, Y.krein j j h * ∑ z, Y.E j a z * Y.E h z b := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun h _ => Finset.sum_congr rfl fun z _ => by ring
    calc ∑ z, Y.E j a z * (Y.E j z b * Y.E j z b)
        = ∑ z, Y.E j a z * ((1 / (Fintype.card X : ℂ)) *
            ∑ h, Y.krein j j h * Y.E h z b) :=
          Finset.sum_congr rfl fun z _ => by rw [h1 z]
      _ = (1 / (Fintype.card X : ℂ)) * ∑ z, Y.E j a z *
            ∑ h, Y.krein j j h * Y.E h z b := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = (1 / (Fintype.card X : ℂ)) * ∑ h, Y.krein j j h *
            ∑ z, Y.E j a z * Y.E h z b := by
          rw [h2]
      _ = (1 / (Fintype.card X : ℂ)) * ∑ h, Y.krein j j h * ((Y.E j * Y.E h) a b) := by
          have hh : (∑ h, Y.krein j j h * ∑ z, Y.E j a z * Y.E h z b)
              = ∑ h, Y.krein j j h * ((Y.E j * Y.E h) a b) :=
            Finset.sum_congr rfl fun h _ => by rw [← Matrix.mul_apply]
          rw [hh]
      _ = (1 / (Fintype.card X : ℂ)) * (Y.krein j j j * Y.E j a b) := by
          have hh : (∑ h, Y.krein j j h * ((Y.E j * Y.E h) a b))
              = Y.krein j j j * Y.E j a b := by
            rw [Finset.sum_eq_single j]
            · rw [Y.E_idem j]
            · intro h _ hk
              rw [Y.E_orth j h (Ne.symm hk), Matrix.zero_apply, mul_zero]
            · intro h
              exact absurd (Finset.mem_univ j) h
          rw [hh]
  have hfinal : ∀ a b : X, Y.krein j j j * Y.E j a b = 0 := by
    intro a b
    have h : (1 / (Fintype.card X : ℂ)) * (Y.krein j j j * Y.E j a b) = 0 := by
      rw [← hW2 a b, hW a b]
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 (by rw [one_div]; exact inv_ne_zero hcard)
    · exact h1
  obtain ⟨a, b, hab⟩ : ∃ a b : X, Y.E j a b ≠ 0 := by
    by_contra h
    refine hj ?_
    ext a b
    by_contra hab
    exact h ⟨a, b, hab⟩
  rcases mul_eq_zero.mp (hfinal a b) with h | h
  · exact h
  · exact absurd h hab

/-- Backward direction of Lemma 21.1: `q^j_{jj} = 0` kills the Norton product.
Uses the vanishing condition (Lemma 20.3) for `E_j A*_a(j) E_j = 0`. -/
theorem r2e_norton_backward (hX : 0 < Fintype.card X)
    (hherm : ∀ i, (Y.E i)ᴴ = Y.E i) (j : Fin (D + 1)) (hk : Y.krein j j j = 0) :
    ∀ u ∈ Y.eigenspace j, ∀ v ∈ Y.eigenspace j,
      Y.E j *ᵥ circleMul u v = 0 := by
  intro u hu v hv
  obtain ⟨x, hx⟩ := (r2e_mem_eigenspace Y).mp hu
  obtain ⟨y, hy⟩ := (r2e_mem_eigenspace Y).mp hv
  rw [← hx, ← hy]
  have hstep : ∀ a : X, Y.E j * Y.dualA a j * Y.E j = 0 :=
    fun a => r2d_krein_zero_implies Y hX hherm a j j j hk
  have hdiag1 : Matrix.diagonal (Y.E j *ᵥ x)
      = ∑ a, x a • Matrix.diagonal (fun z => Y.E j z a) := by
    ext z z'
    simp only [Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases h : z = z'
    · subst h
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    · rw [if_neg h]
      simp only [if_neg h, mul_zero, Finset.sum_const_zero]
  have hdiag : Matrix.diagonal (Y.E j *ᵥ x)
      = ∑ a, (x a * (1 / (Fintype.card X : ℂ))) • Y.dualA a j := by
    rw [hdiag1]
    exact Finset.sum_congr rfl fun a _ => by rw [r2e_diagonal_col_eq Y a j, smul_smul]
  have hzero : (∑ a, (x a * (1 / (Fintype.card X : ℂ))) •
      (Y.E j * Y.dualA a j * Y.E j)) = 0 := by
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => by rw [hstep a, smul_zero])]
    simp
  calc Y.E j *ᵥ circleMul (Y.E j *ᵥ x) (Y.E j *ᵥ y)
      = (Y.E j * Matrix.diagonal (Y.E j *ᵥ x)) *ᵥ (Y.E j *ᵥ y) := by
        rw [r2e_circleMul_eq_diagonal, Matrix.mulVec_mulVec]
    _ = (∑ a, (x a * (1 / (Fintype.card X : ℂ))) • (Y.E j * Y.dualA a j)) *ᵥ (Y.E j *ᵥ y) := by
        rw [hdiag, Matrix.mul_sum]
        simp only [Matrix.mul_smul]
    _ = (∑ a, (x a * (1 / (Fintype.card X : ℂ))) • (Y.E j * Y.dualA a j * Y.E j)) *ᵥ y := by
        rw [Matrix.mulVec_mulVec, Matrix.sum_mul]
        simp only [Matrix.smul_mul]
    _ = 0 := by
        rw [hzero, zero_mulVec]

/-- **Lemma 21.1 (part).**  The Norton product on `E_jV` vanishes identically if
and only if `q^j_{jj} = 0`.

NOTE (R2e): the hypothesis `hj : Y.E j ≠ 0` is needed.  With `E j = 0` the left
hand side holds vacuously while `krein j j j` is left unconstrained by the
fields of `SchemeData` (one-point scheme with `D = 1`, `E 1 = 0`,
`krein 1 1 1 = 5`: every field holds, the left hand side is true and
`krein 1 1 1 ≠ 0`).  The sibling statement `representation_of_idempotent`
already carries this hypothesis.

RIPPLE (wave 2, W-h): the backward direction was proved from the *draft* of
Lemma 20.3 (ii), which is false as stated.  The corrected Lemma 20.3 (see above)
needs the self-adjointness `hherm` of the primitive idempotents, so this statement
carries it too.  `hherm` holds in every genuine scheme but is not derivable from
the `SchemeData` fields (only transpose symmetry is; see the note at 20.4).
`0 < |X|`, which 20.3 also needs, is derived here from `hj`. -/
theorem norton_algebra_vanishes
    (hherm : ∀ i, (Y.E i)ᴴ = Y.E i) (j : Fin (D + 1)) (hj : Y.E j ≠ 0) :
    (∀ u ∈ Y.eigenspace j, ∀ v ∈ Y.eigenspace j,
        Y.E j *ᵥ circleMul u v = 0) ↔ Y.krein j j j = 0 := by
  have hX : 0 < Fintype.card X := by
    rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
    · exfalso
      haveI : IsEmpty X := Fintype.card_eq_zero_iff.mp h
      exact hj (Subsingleton.elim _ _)
    · exact h
  exact ⟨r2e_norton_forward Y j hj, r2e_norton_backward Y hX hherm j⟩

/-- **Definition 22.2.**  `Y` is `Q`-polynomial if the Krein parameters vanish
strictly inside the "triangle inequality" and are nonzero on its boundary.

STATEMENT FIX (R2f, wave-2 fix 5, applied): lecture 22's Definition `q-polynomial`
prescribes all *three* vanishing cases (`q^h_{ij} = 0` when one of `h, i, j` exceeds the sum
of the other two) and all *three* boundary cases (`≠ 0` when one of them equals the sum of
the other two).  The draft recorded only `i + j < h` and `h = i + j`.  Runs of the draft
definition also read the conclusion `q_polynomial_iff` with the Krein index order
`q^j_{1h}`, whereas the notes' Lemma `q-conditions` (i)⇒(ii) is about `q^h_{1j}`. -/
def IsQPolynomial : Prop :=
  (∀ h i j : Fin (D + 1), (i : ℕ) + (j : ℕ) < (h : ℕ) → Y.krein i j h = 0) ∧
    (∀ h i j : Fin (D + 1), (h : ℕ) + (j : ℕ) < (i : ℕ) → Y.krein i j h = 0) ∧
    (∀ h i j : Fin (D + 1), (h : ℕ) + (i : ℕ) < (j : ℕ) → Y.krein i j h = 0) ∧
    (∀ h i j : Fin (D + 1), (i : ℕ) + (j : ℕ) = (h : ℕ) → Y.krein i j h ≠ 0) ∧
    (∀ h i j : Fin (D + 1), (h : ℕ) + (j : ℕ) = (i : ℕ) → Y.krein i j h ≠ 0) ∧
    (∀ h i j : Fin (D + 1), (h : ℕ) + (i : ℕ) = (j : ℕ) → Y.krein i j h ≠ 0)

/-- **Lemma 22.3 (Lemma `q-conditions`, (i) ⇒ (ii)).**  For a symmetric scheme, `Q`-polynomiality
implies the vanishing of the `q^h_{1j}` off the diagonal band and their nonvanishing on it.

NOTE (R2f): the direction proved here is the notes' (i)⇒(ii) of Lemma `q-conditions`; it is the
whole content of the draft statement (which hypothesised `Y.IsQPolynomial` and *concluded* the
band conditions).  The converse (ii)⇒(i) is not derivable from the `SchemeData` axioms: the notes
derive it from the symmetry relations `m_h q^h_{ij} = m_j q^j_{ih} = m_i q^i_{hj}`
(Lemma `phijqhij`), which need the multiplicities `m_h` and the Hermitian structure of the `Eᵢ`
(`star (E i) = E i`), neither of which `SchemeData` records (compare wave-2 fix 2). -/
theorem q_polynomial_iff (hY : Y.IsQPolynomial) :
    (∀ h j : Fin (D + 1), (h : ℕ) + 1 < (j : ℕ) ∨ (j : ℕ) + 1 < (h : ℕ) →
        Y.krein 1 h j = 0) ∧
      (∀ h j : Fin (D + 1), (h : ℕ) + 1 = (j : ℕ) ∨ (j : ℕ) + 1 = (h : ℕ) →
        Y.krein 1 h j ≠ 0) := by
  rcases Nat.eq_zero_or_pos D with hD | hD
  · subst hD
    refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩ <;> omega
  · have h1 : ((1 : Fin (D + 1)) : ℕ) = 1 := by simp; omega
    refine ⟨fun h j hj => ?_, fun h j hj => ?_⟩
    · rcases hj with hj | hj
      · exact hY.1 j 1 h (by omega)
      · exact hY.2.2.1 j 1 h (by omega)
    · rcases hj with hj | hj
      · exact hY.2.2.2.1 j 1 h (by omega)
      · exact hY.2.2.2.2.2 j 1 h (by omega)

/-- **Definition 23.2 (in Gram-matrix form).**  A representation of `Y`: a
matrix `E` with `E_{xy}` depending only on the relation between `x` and `y` (R2),
whose rows are stable under the sphere sums (R3), and which is nonzero. -/
structure IsRepresentation (E : Matrix X X ℂ) : Prop where
  gram : ∀ i, ∃ σ : ℂ, ∀ x y, Y.scheme.rel i x y → E x y = σ
  sphere : ∀ i, ∃ α : ℂ, E * Y.A i = α • E
  nondeg : E ≠ 0

/-- **Lemma 23.4.**  Each primitive idempotent gives a representation, and its
Gram entries are `|X|⁻¹ q_j(i)` on the relation `R_i`. -/
theorem representation_of_idempotent (j : Fin (D + 1)) (hj : Y.E j ≠ 0) :
    Y.IsRepresentation (Y.E j) ∧
      (∀ i x y, Y.scheme.rel i x y → (Y.E j) x y = (1 / (Fintype.card X : ℂ)) * Y.qcoef j i) := by
  have hmain : ∀ i x y, Y.scheme.rel i x y →
      (Y.E j) x y = (1 / (Fintype.card X : ℂ)) * Y.qcoef j i :=
    fun i x y h => r2e_E_apply_of_rel Y h
  have hsphere : ∀ i, ∃ α : ℂ, Y.E j * Y.A i = α • Y.E j := by
    intro i
    refine ⟨Y.pcoef i j, ?_⟩
    have hmul : Y.E j * Y.A i
        = ∑ k, Y.pcoef i k • (Y.E j * Y.E k) := by
      have h1 : Y.A i = ∑ k, Y.pcoef i k • Y.E k := Y.A_eq i
      calc Y.E j * Y.A i = Y.E j * ∑ k, Y.pcoef i k • Y.E k := by rw [h1]
        _ = ∑ k, Y.E j * (Y.pcoef i k • Y.E k) := Finset.mul_sum ..
        _ = ∑ k, Y.pcoef i k • (Y.E j * Y.E k) :=
              Finset.sum_congr rfl fun k _ => Matrix.mul_smul _ _ _
    rw [hmul, Finset.sum_eq_single j]
    · rw [Y.E_idem j]
    · intro k _ hk
      rw [Y.E_orth j k (Ne.symm hk), smul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  refine ⟨⟨?_, hsphere, hj⟩, hmain⟩
  intro i
  exact ⟨_, hmain i⟩

/-- The balanced condition of Theorem 24.2 (ic), in the matrix form used in the
proof: `A₁A*A₂ - A₂A*A₁` is a combination of the commutators `[A*, A_h]`. -/
def IsBalanced (x : X) : Prop :=
  ∃ r : Fin (D + 1) → ℂ,
    Y.A 1 * Y.dualA x 1 * Y.A 2 - Y.A 2 * Y.dualA x 1 * Y.A 1
      = ∑ h ∈ (Finset.univ : Finset (Fin (D + 1))).filter (fun h => 1 ≤ h),
          r h • (Y.dualA x 1 * Y.A h - Y.A h * Y.dualA x 1)

/-! ### Theorem 24.2 (balanced conditions): the Chapter 24 infrastructure (R2f)

The notes' proof of (ia) ⇒ (ib) runs through four claims (lecture 24): the space
`L = {mA*n - nA*m ∣ m, n ∈ M}` has dimension `≤ D` (Claim 1), the `D` matrices
`A*A_h - A_hA*` (`1 ≤ h ≤ D`) are linearly independent in `L` (Claim 2 (i)) and hence
form a basis of `L`, and `A₁A*A₂ - A₂A*A₁ ∈ L` therefore expands in that basis (Claim 2 (ii)).

The formal proof below follows the same route, with `L` replaced by the reduced form
`balancedSpan = span{EᵢA*Eᵢ₊₁ - Eᵢ₊₁A*Eᵢ ∣ 0 ≤ i < D}` (Claim 1's *conclusion*: the
non-adjacent terms vanish by the Q-polynomial band condition) and the linear independence
of the `A*A_h - A_hA*` obtained from the notes' column-at-`x` computation. -/

/-- `A*_j(x)` is diagonal. -/
theorem dualA_apply_of_ne (x : X) (j : Fin (D + 1)) {y z : X} (hyz : y ≠ z) :
    Y.dualA x j y z = 0 := by
  simp only [SchemeData.dualA, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [SchemeData.dualIdem, Matrix.diagonal_apply, if_neg hyz, mul_zero]

/-- On a class `Rᵢ(x)` the diagonal entry of `A*_j(x)` is the dual eigenvalue `q_j(i)`. -/
theorem dualA_apply_self (hX : 0 < Fintype.card X) {x y : X} {i j : Fin (D + 1)}
    (h : Y.scheme.rel i y x) : Y.dualA x j y y = Y.qcoef j i := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  rw [r2e_dualA_apply_self Y x y j,
    r2e_E_apply_of_rel Y (j := j) (i := i) (x := y) (y := x) h]
  field_simp

/-- Column `x` of the commutator `[A*₁(x), A_h]`: the notes' Chapter 24, Claim 2 (i)
computation.  `A*₁(x)` being diagonal, the two products collapse to single terms. -/
theorem commutator_apply_self (x : X) (h : Fin (D + 1)) (y : X) :
    (Y.dualA x 1 * Y.A h - Y.A h * Y.dualA x 1) y x
      = (Y.dualA x 1 y y - Y.dualA x 1 x x) * Y.A h y x := by
  rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
  have h1 : ∀ b : X, Y.dualA x 1 y b * Y.A h b x
      = if b = y then Y.dualA x 1 y y * Y.A h y x else 0 := by
    intro b
    by_cases hb : b = y
    · rw [hb, if_pos rfl]
    · rw [dualA_apply_of_ne Y x 1 (fun hc => hb hc.symm), zero_mul, if_neg hb]
  have h2 : ∀ b : X, Y.A h y b * Y.dualA x 1 b x
      = if b = x then Y.A h y x * Y.dualA x 1 x x else 0 := by
    intro b
    by_cases hb : b = x
    · rw [hb, if_pos rfl]
    · rw [dualA_apply_of_ne Y x 1 hb, mul_zero, if_neg hb]
  rw [Finset.sum_congr rfl (fun b _ => h1 b), Finset.sum_congr rfl (fun b _ => h2 b)]
  simp
  ring

/-- Column `x` of `A_h` is the indicator vector of the class `R_h(x)`; the columns for
`h ≠ 0` are linearly independent. -/
theorem linearIndependent_col_A (hne : ∀ j, Y.E j ≠ 0) (x : X) :
    LinearIndependent ℂ
      (fun h : {h : Fin (D + 1) // h ≠ 0} => (fun y => Y.A h.1 y x)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  have hz : ∃ z, Y.scheme.rel k.1 x z := by
    have hpos : 0 < (Finset.univ.filter fun z => Y.scheme.rel k.1 x z).card := by
      rw [Y.card_rel_row]
      exact Nat.pos_of_ne_zero (Y.kval_ne_zero_of_rel (Y.rel_exists_of_E_ne_zero hne k.1))
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    exact ⟨z, (Finset.mem_filter.mp hz).2⟩
  obtain ⟨z, hxzk⟩ := hz
  have hzk : Y.scheme.rel k.1 z x := (Y.symm k.1 x z).mp hxzk
  have h2 : ∀ h : {h : Fin (D + 1) // h ≠ 0},
      (g h • (fun y => Y.A h.1 y x)) z = if h = k then g h else 0 := by
    intro h
    show g h * Y.A h.1 z x = _
    rw [Y.A_apply]
    by_cases hh : h = k
    · subst hh
      rw [if_pos hzk, mul_one, if_pos rfl]
    · rw [if_neg hh, if_neg (fun hrel => hh (Subtype.ext (Y.rel_unique hrel hzk))), mul_zero]
  have h3 : (∑ h : {h : Fin (D + 1) // h ≠ 0},
      (g h • (fun y => Y.A h.1 y x)) z) = g k := by
    rw [Finset.sum_congr rfl (fun h _ => h2 h)]
    simp
  have h4 : (∑ h : {h : Fin (D + 1) // h ≠ 0},
      (g h • (fun y => Y.A h.1 y x)) z) = 0 := by
    have := congrFun hg z
    simpa using this
  rw [h3] at h4
  exact h4

/-- The generator `EᵢA*Eᵢ₊₁ - Eᵢ₊₁A*Eᵢ` of the notes' space `L` (Chapter 24, Claim 1). -/
def commTerm (x : X) (i : Fin D) : Matrix X X ℂ :=
  Y.E ⟨i.1, by omega⟩ * Y.dualA x 1 * Y.E ⟨(i.1 : ℕ) + 1, by omega⟩
    - Y.E ⟨(i.1 : ℕ) + 1, by omega⟩ * Y.dualA x 1 * Y.E ⟨i.1, by omega⟩

/-- The notes' space `L` (Chapter 24, Claim 1) in reduced form: under the Q-polynomial band
condition only the adjacent terms `EᵢA*Eᵢ₊₁ - Eᵢ₊₁A*Eᵢ` survive, so `L` is spanned by `D`
matrices (`i = 0, …, D-1`). -/
def balancedSpan (x : X) : Submodule ℂ (Matrix X X ℂ) :=
  Submodule.span ℂ (Set.range fun i : Fin D => Y.commTerm x i)

theorem commTerm_mem (x : X) (i : Fin D) : Y.commTerm x i ∈ Y.balancedSpan x :=
  Submodule.subset_span ⟨i, rfl⟩

/-- `1 : Fin (D+1)` is the honest index `1` when `D ≥ 1` (the `OfNat` instance of `Fin` is
the mod-`D+1` one, so this needs a case distinction). -/
theorem one_val_of_le {D : ℕ} (hD : 1 ≤ D) : ((1 : Fin (D + 1)) : ℕ) = 1 := by
  simp
  omega

/-- The Q-polynomial band condition: `EᵢA*₁E_k = 0` when the classes `Rᵢ(x)`, `R_k(x)` are
more than two apart.  This is Lemma 20.3 (ii) (`vanishing_condition`) applied to the vanishing
clauses of Definition 22.2; the hypothesis `hvan` is exactly Lemma 20.3 (ii) for `j = 1`. -/
theorem band_of_qpoly {x : X} (hY : Y.IsQPolynomial)
    (hvan : ∀ i k : Fin (D + 1),
      Y.E i * Y.dualA x 1 * Y.E k = 0 ↔ Y.krein 1 i k = 0)
    (hD1 : 1 ≤ D)
    {i k : Fin (D + 1)} (hik : (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ)) :
    Y.E i * Y.dualA x 1 * Y.E k = 0 := by
  have h1v := one_val_of_le (D := D) hD1
  rcases hik with hik | hik
  · exact (hvan i k).mpr (hY.1 k 1 i (by omega))
  · exact (hvan i k).mpr (hY.2.2.1 k 1 i (by omega))


/-- Non-adjacent pairs contribute nothing to `L`: `EᵢA*E_k - E_kA*Eᵢ ∈ balancedSpan`. -/
theorem pair_mem_balancedSpan {x : X}
    (hband : ∀ i k : Fin (D + 1), (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ) →
      Y.E i * Y.dualA x 1 * Y.E k = 0)
    (i k : Fin (D + 1)) :
    Y.E i * Y.dualA x 1 * Y.E k - Y.E k * Y.dualA x 1 * Y.E i ∈ Y.balancedSpan x := by
  rcases lt_trichotomy (i : ℕ) (k : ℕ) with hlt | heq | hgt
  · rcases Nat.lt_or_ge (k : ℕ) ((i : ℕ) + 2) with h2 | h2
    · have hk : k = ⟨(i.1 : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hk]
      exact Y.commTerm_mem x ⟨i.1, by omega⟩
    · rw [hband i k (Or.inl h2), hband k i (Or.inr h2), sub_self]
      exact Submodule.zero_mem _
  · have hik : i = k := Fin.ext heq
    subst hik
    rw [sub_self]
    exact Submodule.zero_mem _
  · rcases Nat.lt_or_ge (i : ℕ) ((k : ℕ) + 2) with h2 | h2
    · have hi : i = ⟨(k.1 : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
      rw [hi]
      have hmem := Y.commTerm_mem x ⟨k.1, by omega⟩
      have hneg : -Y.commTerm x ⟨k.1, by omega⟩ ∈ Y.balancedSpan x := Submodule.neg_mem _ hmem
      simpa only [commTerm, neg_sub] using hneg
    · rw [hband i k (Or.inr h2), hband k i (Or.inl h2), sub_self]
      exact Submodule.zero_mem _

/-- `A*₁(x)E_j - E_jA*₁(x) ∈ L`: expand `A* = A*·1 = ∑_k E_kA*` and `A* = 1·A* = ∑_k A*E_k`. -/
theorem dualA_mul_E_sub_mem {x : X}
    (hband : ∀ i k : Fin (D + 1), (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ) →
      Y.E i * Y.dualA x 1 * Y.E k = 0)
    (j : Fin (D + 1)) :
    Y.dualA x 1 * Y.E j - Y.E j * Y.dualA x 1 ∈ Y.balancedSpan x := by
  have h1 : Y.dualA x 1 * Y.E j = ∑ k, Y.E k * Y.dualA x 1 * Y.E j := by
    calc Y.dualA x 1 * Y.E j = 1 * Y.dualA x 1 * Y.E j := by rw [Matrix.one_mul]
      _ = (∑ k, Y.E k) * Y.dualA x 1 * Y.E j := by rw [Y.E_sum]
      _ = ∑ k, Y.E k * Y.dualA x 1 * Y.E j := by rw [Finset.sum_mul, Finset.sum_mul]
  have h2 : Y.E j * Y.dualA x 1 = ∑ k, Y.E j * Y.dualA x 1 * Y.E k := by
    conv_lhs => rw [← Matrix.mul_one (Y.E j * Y.dualA x 1), ← Y.E_sum, Matrix.mul_sum]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  exact Submodule.sum_mem _ fun k _ => Y.pair_mem_balancedSpan hband k j

/-- The abelian-group identity `a + c - (b + d) = (a - b) + (c - d)`. -/
theorem sub_add_sub (a b c d : Matrix X X ℂ) : a + c - (b + d) = (a - b) + (c - d) := by
  abel

/-- Bilinearity: the commutator of any two elements of `span(E)` lies in `L`. -/
theorem commutator_mem_of_mem {x : X}
    (hband : ∀ i k : Fin (D + 1), (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ) →
      Y.E i * Y.dualA x 1 * Y.E k = 0) :
    ∀ m ∈ Submodule.span ℂ (Set.range Y.E), ∀ n ∈ Submodule.span ℂ (Set.range Y.E),
      m * Y.dualA x 1 * n - n * Y.dualA x 1 * m ∈ Y.balancedSpan x := by
  intro m hm
  induction hm using Submodule.span_induction with
  | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      intro n hn
      induction hn using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨k, rfl⟩ := hb
          exact Y.pair_mem_balancedSpan hband i k
      | zero =>
          simp
      | add u v _ _ hu hv =>
          rw [Matrix.mul_add, add_mul, add_mul, sub_add_sub]
          exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, ← smul_sub]
          exact Submodule.smul_mem _ c hu
  | zero =>
      intro n _
      simp
  | add u v _ _ hu hv =>
      intro n hn
      rw [add_mul, add_mul, Matrix.mul_add, sub_add_sub]
      exact Submodule.add_mem _ (hu n hn) (hv n hn)
  | smul c u _ hu =>
      intro n hn
      rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub]
      exact Submodule.smul_mem _ c (hu n hn)

/-- `Aᵢ ∈ span(E)`. -/
theorem A_mem_span_E (i : Fin (D + 1)) : Y.A i ∈ Submodule.span ℂ (Set.range Y.E) := by
  rw [show Y.A i = ∑ k, Y.pcoef i k • Y.E k from Y.A_eq i]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

/-- The family `A*A_h - A_hA*`, `h ≠ 0`, whose span is the right-hand side of `IsBalanced x`. -/
def balancedFamily (x : X) : {h : Fin (D + 1) // h ≠ 0} → Matrix X X ℂ :=
  fun h => Y.dualA x 1 * Y.A h.1 - Y.A h.1 * Y.dualA x 1

/-- `A*A_h - A_hA* ∈ L`: expand `A_h = ∑_j p_h(j)E_j` and use `dualA_mul_E_sub_mem`. -/
theorem balancedFamily_mem {x : X}
    (hband : ∀ i k : Fin (D + 1), (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ) →
      Y.E i * Y.dualA x 1 * Y.E k = 0)
    (h : {h : Fin (D + 1) // h ≠ 0}) : Y.balancedFamily x h ∈ Y.balancedSpan x := by
  have h1 : Y.dualA x 1 * Y.A h.1
      = ∑ j, Y.pcoef h.1 j • (Y.dualA x 1 * Y.E j) := by
    rw [show Y.A h.1 = ∑ j, Y.pcoef h.1 j • Y.E j from Y.A_eq h.1, Matrix.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mul_smul _ _ _
  have h2 : Y.A h.1 * Y.dualA x 1
      = ∑ j, Y.pcoef h.1 j • (Y.E j * Y.dualA x 1) := by
    rw [show Y.A h.1 = ∑ j, Y.pcoef h.1 j • Y.E j from Y.A_eq h.1, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Matrix.smul_mul _ _ _
  have h3 : Y.balancedFamily x h
      = ∑ j, Y.pcoef h.1 j • (Y.dualA x 1 * Y.E j - Y.E j * Y.dualA x 1) := by
    show Y.dualA x 1 * Y.A h.1 - Y.A h.1 * Y.dualA x 1 = _
    rw [h1, h2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_sub _ _ _).symm
  rw [h3]
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Y.dualA_mul_E_sub_mem hband j)

/-- For every class `R_k(x)` there is a point `z` with `(z,x) ∈ R_k`. -/
theorem exists_rel_left (hne : ∀ j, Y.E j ≠ 0) (x : X) (k : Fin (D + 1)) :
    ∃ z, Y.scheme.rel k z x := by
  have hpos : 0 < (Finset.univ.filter fun z => Y.scheme.rel k x z).card := by
    rw [Y.card_rel_row]
    exact Nat.pos_of_ne_zero (Y.kval_ne_zero_of_rel (Y.rel_exists_of_E_ne_zero hne k))
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
  exact ⟨z, (Y.symm k x z).mp (Finset.mem_filter.mp hz).2⟩

/-- Evaluating the column at `x` of a combination of the matrices `A_h` (`h ≠ 0`) at a point
`z` with `(z,x) ∈ R_k` recovers the coefficient of `A_k`. -/
theorem sum_apply_col_eq (x : X) (g : {h : Fin (D + 1) // h ≠ 0} → ℂ)
    {k : {h : Fin (D + 1) // h ≠ 0}} {z : X} (hz : Y.scheme.rel k.1 z x) :
    (∑ h : {h : Fin (D + 1) // h ≠ 0}, g h * Y.A h.1 z x) = g k := by
  have h2 : ∀ h : {h : Fin (D + 1) // h ≠ 0},
      g h * Y.A h.1 z x = if h = k then g h else 0 := by
    intro h
    rw [Y.A_apply]
    by_cases hh : h = k
    · subst hh
      rw [if_pos hz, mul_one, if_pos rfl]
    · rw [if_neg hh, if_neg (fun hrel => hh (Subtype.ext (Y.rel_unique hrel hz))), mul_zero]
  rw [Finset.sum_congr rfl (fun h _ => h2 h)]
  simp

/-- The `D` matrices `A*A_h - A_hA*` (`h ≠ 0`) are linearly independent (the notes'
Chapter 24, Claim 2 (i)), provided the dual eigenvalues `q₁(h)`, `h ≠ 0`, differ from `q₁(0)`. -/
theorem linearIndependent_balancedFamily (hX : 0 < Fintype.card X)
    (hne : ∀ j, Y.E j ≠ 0)
    (hdual : ∀ h : Fin (D + 1), h ≠ 0 → Y.qcoef 1 h ≠ Y.qcoef 1 0) (x : X) :
    LinearIndependent ℂ (Y.balancedFamily x) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg k
  obtain ⟨z, hz⟩ := Y.exists_rel_left hne x k.1
  have h1 : (∑ h : {h : Fin (D + 1) // h ≠ 0}, g h * Y.balancedFamily x h z x) = 0 := by
    have h2 : (∑ h : {h : Fin (D + 1) // h ≠ 0}, g h • Y.balancedFamily x h) z x = 0 := by
      rw [hg]
      rfl
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] using h2
  have h2 : ∀ h : {h : Fin (D + 1) // h ≠ 0}, g h * Y.balancedFamily x h z x
      = (Y.dualA x 1 z z - Y.dualA x 1 x x) * (g h * Y.A h.1 z x) := by
    intro h
    show g h * (Y.dualA x 1 * Y.A h.1 - Y.A h.1 * Y.dualA x 1) z x = _
    rw [Y.commutator_apply_self x h.1 z]
    ring
  rw [Finset.sum_congr rfl (fun h _ => h2 h), ← Finset.mul_sum] at h1
  rw [Y.sum_apply_col_eq x g hz] at h1
  have h4 : Y.dualA x 1 z z - Y.dualA x 1 x x = Y.qcoef 1 k.1 - Y.qcoef 1 0 := by
    rw [Y.dualA_apply_self hX hz,
      Y.dualA_apply_self hX (i := 0) ((Y.scheme.rel_zero x x).mpr rfl)]
  rw [h4] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (sub_ne_zero.mpr (hdual k.1 k.2))
  · exact h

/-- `L` is spanned by `D` matrices, so it has dimension at most `D` (Chapter 24, Claim 1). -/
theorem finrank_balancedSpan_le (x : X) : Module.finrank ℂ ↥(Y.balancedSpan x) ≤ D := by
  have h := finrank_span_le_card (R := ℂ) (s := Set.range fun i : Fin D => Y.commTerm x i)
  have h2 : (Set.range fun i : Fin D => Y.commTerm x i).toFinset.card ≤ D := by
    have hsub : (Set.range fun i : Fin D => Y.commTerm x i).toFinset
        ⊆ Finset.univ.image (fun i : Fin D => Y.commTerm x i) := by
      intro z hz
      simp only [Set.mem_toFinset, Set.mem_range] at hz
      obtain ⟨i, rfl⟩ := hz
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    have h5 : (Finset.univ.image (fun i : Fin D => Y.commTerm x i)).card ≤ D := by
      simpa using Finset.card_image_le (f := fun i : Fin D => Y.commTerm x i) (s := Finset.univ)
    exact le_trans (Finset.card_le_card hsub) h5
  have h' : Module.finrank ℂ ↥(Y.balancedSpan x)
      ≤ (Set.range fun i : Fin D => Y.commTerm x i).toFinset.card := h
  exact le_trans h' h2

/-- The trace of `Eᵢ` is `qᵢ(0)` (the first half of Lemma 20.1 (iv)). -/
theorem trace_E (hX : 0 < Fintype.card X) (i : Fin (D + 1)) :
    (Y.E i).trace = Y.qcoef i 0 := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have h1 : Y.E i = (1 / (Fintype.card X : ℂ)) • ∑ k, Y.qcoef i k • Y.A k := Y.E_eq i
  rw [h1, Matrix.trace_smul, Matrix.trace_sum]
  have hterm : ∀ k : Fin (D + 1), ((Y.qcoef i k) • Y.A k).trace
      = Y.qcoef i k * (if k = 0 then (Fintype.card X : ℂ) else 0) := by
    intro k
    rw [Matrix.trace_smul, smul_eq_mul, Y.trace_A]
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_eq_single 0]
  · rw [if_pos rfl, smul_eq_mul]
    field_simp
  · intro k _ hk
    rw [if_neg hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (0 : Fin (D + 1))) h

/-- `trace (A_k A_l) = p^0_{kl}|X| = δ_{kl} k_k |X|`. -/
theorem trace_A_mul_A (hX : 0 < Fintype.card X) (k l : Fin (D + 1)) :
    ((Y.A k) * (Y.A l)).trace
      = (if k = l then (Y.kval k : ℂ) else 0) * (Fintype.card X : ℂ) := by
  rw [Y.trace_A_mul]
  congr 1
  by_cases h : k = l
  · subst h
    rw [if_pos rfl, SchemeData.kval]
  · rw [if_neg h, Y.p_zero_of_ne hX h, Nat.cast_zero]

/-- `trace (EᵢA_l) = qᵢ(l) k_l`. -/
theorem trace_E_mul_A (hX : 0 < Fintype.card X) (i l : Fin (D + 1)) :
    (Y.E i * Y.A l).trace = Y.qcoef i l * (Y.kval l : ℂ) := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  rw [show Y.E i = (1 / (Fintype.card X : ℂ)) • ∑ k, Y.qcoef i k • Y.A k from Y.E_eq i,
    Matrix.smul_mul, Matrix.sum_mul, Matrix.trace_smul, Matrix.trace_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_eq_single l]
  · rw [Y.trace_A_mul_A hX l l, if_pos rfl]
    field_simp
  · intro k _ hk
    rw [Y.trace_A_mul_A hX k l, if_neg hk, zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ l) h

/-- The Q-matrix orthogonality relation `∑_k k_k qᵢ(k) qⱼ(k) = |X| δᵢⱼ qᵢ(0)`
(the `m = 0` coefficient of `EᵢEⱼ = δᵢⱼEᵢ` in the basis `A_0, …, A_D`), proved by traces. -/
theorem q_orthogonality (hX : 0 < Fintype.card X) (i j : Fin (D + 1)) :
    (∑ k : Fin (D + 1), (Y.kval k : ℂ) * (Y.qcoef i k * Y.qcoef j k))
      = if i = j then (Fintype.card X : ℂ) * Y.qcoef i 0 else 0 := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have hpt : ∀ l : Fin (D + 1),
      (Y.E i * (Y.qcoef j l • Y.A l)).trace = Y.qcoef j l * (Y.E i * Y.A l).trace := by
    intro l
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  have h1 : (Y.E i * Y.E j).trace
      = (1 / (Fintype.card X : ℂ)) *
          ∑ l : Fin (D + 1), Y.qcoef j l * (Y.E i * Y.A l).trace := by
    rw [show Y.E j = (1 / (Fintype.card X : ℂ)) • ∑ l, Y.qcoef j l • Y.A l from Y.E_eq j,
      Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum]
    rw [Finset.sum_congr rfl (fun l _ => hpt l), smul_eq_mul]
  have hs : (∑ l : Fin (D + 1), Y.qcoef j l * (Y.E i * Y.A l).trace)
      = ∑ l : Fin (D + 1), Y.qcoef j l * (Y.qcoef i l * (Y.kval l : ℂ)) :=
    Finset.sum_congr rfl fun l _ => by rw [Y.trace_E_mul_A hX i l]
  rw [hs] at h1
  have htr : (Y.E i * Y.E j).trace = if i = j then Y.qcoef i 0 else 0 := by
    by_cases h : i = j
    · subst h
      rw [Y.E_idem i, Y.trace_E hX i, if_pos rfl]
    · rw [Y.E_orth i j h, Matrix.trace_zero, if_neg h]
  have h := h1.symm.trans htr
  have hL : (∑ l : Fin (D + 1), Y.qcoef j l * (Y.qcoef i l * (Y.kval l : ℂ)))
      = ∑ k : Fin (D + 1), (Y.kval k : ℂ) * (Y.qcoef i k * Y.qcoef j k) :=
    Finset.sum_congr rfl fun l _ => by ring
  rw [hL] at h
  have h2 : (Fintype.card X : ℂ) * ((1 / (Fintype.card X : ℂ)) *
      (∑ k : Fin (D + 1), (Y.kval k : ℂ) * (Y.qcoef i k * Y.qcoef j k)))
      = ∑ k : Fin (D + 1), (Y.kval k : ℂ) * (Y.qcoef i k * Y.qcoef j k) := by
    field_simp
  rw [← h2, h]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

/-- `Eᵢ ≠ 0` forces the multiplicity `mᵢ` to be nonzero. -/
theorem mult_ne_zero (hne : ∀ j, Y.E j ≠ 0) (i : Fin (D + 1)) : Y.mult i ≠ 0 := by
  intro h0
  refine hne i ?_
  have hbot : LinearMap.range (Y.E i).mulVecLin = ⊥ := by
    rw [← Submodule.finrank_eq_zero]
    exact h0
  ext a b
  have hmem : (Y.E i *ᵥ (Pi.single b (1 : ℂ))) ∈ LinearMap.range (Y.E i).mulVecLin :=
    LinearMap.mem_range.mpr ⟨_, rfl⟩
  rw [hbot] at hmem
  have hz : (Y.E i *ᵥ Pi.single b (1 : ℂ)) = 0 := by simpa using hmem
  rw [r2e_col Y i b] at hz
  simpa using congrFun hz a

/-- `qᵢ(0) ≠ 0`. -/
theorem qcoef_zero_ne (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0) (i : Fin (D + 1)) :
    Y.qcoef i 0 ≠ 0 := by
  rw [Y.qcoef_zero_col hX i]
  exact Nat.cast_ne_zero.mpr (Y.mult_ne_zero hne i)

/-- The `Q`-matrix is nonsingular: a linear combination of its rows that vanishes identically
is trivial (consequence of the orthogonality relation `q_orthogonality`). -/
theorem qcoef_sum_zero (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0)
    {c : Fin (D + 1) → ℂ} (h : ∀ m, ∑ j, c j * Y.qcoef j m = 0) (i : Fin (D + 1)) :
    c i = 0 := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have e1 : (∑ j, c j * ∑ m, (Y.kval m : ℂ) * (Y.qcoef i m * Y.qcoef j m))
      = c i * ((Fintype.card X : ℂ) * Y.qcoef i 0) := by
    rw [Finset.sum_congr rfl (fun j _ => by rw [Y.q_orthogonality hX i j])]
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl]
    · intro j _ hj
      rw [if_neg (Ne.symm hj), mul_zero]
    · intro h'
      exact absurd (Finset.mem_univ i) h'
  have e2 : (∑ j, c j * ∑ m, (Y.kval m : ℂ) * (Y.qcoef i m * Y.qcoef j m)) = 0 := by
    have h2 : (∑ j, c j * ∑ m, (Y.kval m : ℂ) * (Y.qcoef i m * Y.qcoef j m))
        = ∑ m, ((Y.kval m : ℂ) * Y.qcoef i m) * (∑ j, c j * Y.qcoef j m) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    simp [h]
  rw [e2] at e1
  rcases mul_eq_zero.mp e1.symm with h' | h'
  · exact h'
  · exact absurd h' (mul_ne_zero hcard (Y.qcoef_zero_ne hX hne i))

/-- The dual association matrices `A*_j(x)` are linearly independent (= the `Q`-matrix is
nonsingular). -/
theorem linearIndependent_dualA (hX : 0 < Fintype.card X) (hne : ∀ j, Y.E j ≠ 0) (x : X) :
    LinearIndependent ℂ (fun j : Fin (D + 1) => Y.dualA x j) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  refine Y.qcoef_sum_zero hX hne (c := c) ?_ i
  intro m
  obtain ⟨z, hz⟩ := Y.exists_rel_left hne x m
  have h1 : (∑ j, c j • Y.dualA x j) z z = 0 := by
    rw [hc]
    rfl
  rw [Matrix.sum_apply] at h1
  have h2 : ∀ j : Fin (D + 1), (c j • Y.dualA x j) z z = c j * Y.qcoef j m := by
    intro j
    rw [Matrix.smul_apply, smul_eq_mul, Y.dualA_apply_self hX (j := j) hz]
  rw [Finset.sum_congr rfl (fun j _ => h2 j)] at h1
  exact h1

/-- The Krein parameters give the entries of the Hadamard product: on the class `R_m(x)`,
`qᵢ(m) qⱼ(m) = ∑_k q^k_{ij} q_k(m)` (the definition `hadamard` evaluated at an entry). -/
theorem krein_q_identity (hX : 0 < Fintype.card X) (i j : Fin (D + 1)) {a x : X}
    {m : Fin (D + 1)} (hm : Y.scheme.rel m a x) :
    Y.qcoef i m * Y.qcoef j m = ∑ k, Y.krein i j k * Y.qcoef k m := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hX)
  have h := congrFun (congrFun (Y.hadamard i j) a) x
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul] at h
  rw [r2e_E_apply_of_rel Y (j := i) (i := m) (x := a) (y := x) hm,
    r2e_E_apply_of_rel Y (j := j) (i := m) (x := a) (y := x) hm] at h
  have h2 : ∀ k : Fin (D + 1),
      Y.krein i j k * Y.E k a x = Y.krein i j k * ((1 / (Fintype.card X : ℂ)) * Y.qcoef k m) := by
    intro k
    rw [r2e_E_apply_of_rel Y (j := k) (i := m) (x := a) (y := x) hm]
  rw [Finset.sum_congr rfl (fun k _ => h2 k)] at h
  have hsum : (∑ k : Fin (D + 1), Y.krein i j k * ((1 / (Fintype.card X : ℂ)) * Y.qcoef k m))
      = (1 / (Fintype.card X : ℂ)) * ∑ k, Y.krein i j k * Y.qcoef k m := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hsum] at h
  calc Y.qcoef i m * Y.qcoef j m
      = (Fintype.card X : ℂ) * ((Fintype.card X : ℂ) *
          ((1 / (Fintype.card X : ℂ)) * Y.qcoef i m *
            ((1 / (Fintype.card X : ℂ)) * Y.qcoef j m))) := by field_simp
    _ = (Fintype.card X : ℂ) * ((Fintype.card X : ℂ) *
          ((1 / (Fintype.card X : ℂ)) *
            ((1 / (Fintype.card X : ℂ)) * ∑ k, Y.krein i j k * Y.qcoef k m))) := by rw [h]
    _ = ∑ k, Y.krein i j k * Y.qcoef k m := by field_simp

/-- The dual association matrices multiply with the Krein parameters as structure constants:
`A*ᵢA*ⱼ = ∑_k q^k_{ij} A*_k` (Chapter 20). -/
theorem dualA_mul_dualA (hX : 0 < Fintype.card X) (x : X) (i j : Fin (D + 1)) :
    Y.dualA x i * Y.dualA x j = ∑ k, Y.krein i j k • Y.dualA x k := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  by_cases hab : a = b
  · subst hab
    obtain ⟨m, hm, -⟩ := Y.scheme.rel_total a x
    have hL : (∑ z, Y.dualA x i a z * Y.dualA x j z a)
        = Y.qcoef i m * Y.qcoef j m := by
      rw [Finset.sum_eq_single a]
      · rw [Y.dualA_apply_self hX (j := i) hm, Y.dualA_apply_self hX (j := j) hm]
      · intro z _ hz
        rw [Y.dualA_apply_of_ne x i (Ne.symm hz), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ a) h
    have hR : (∑ k : Fin (D + 1), (Y.krein i j k • Y.dualA x k) a a)
        = ∑ k, Y.krein i j k * Y.qcoef k m := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Y.dualA_apply_self hX (j := k) hm]
    rw [hL, hR, Y.krein_q_identity hX i j hm]
  · have h1 : (∑ z, Y.dualA x i a z * Y.dualA x j z b) = 0 := by
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hza : z = a
      · subst hza
        rw [Y.dualA_apply_of_ne x j hab, mul_zero]
      · rw [Y.dualA_apply_of_ne x i (Ne.symm hza), zero_mul]
    have h2 : (∑ k : Fin (D + 1), (Y.krein i j k • Y.dualA x k) a b) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Y.dualA_apply_of_ne x k hab, mul_zero]
    rw [h1, h2]

/-! ### Distinctness of the dual eigenvalues `q₁(m)` (Lemma `q-conditions`, (iii) ⇒ (iv))

The notes derive it from: each `A*_j` is a polynomial in `A*_1` of degree `≤ j`, the `A*_j` span
the same `D+1`-dimensional space as `1, A*_1, …, A*_1^D`, and there are only `D+1` eigenvalues;
hence the powers are linearly independent and no nonzero polynomial of degree `≤ D` annihilates
`A*_1`. -/

/-- `∑_m E*_m(x) = 1`: the dual idempotents are the sphere indicators. -/
theorem sum_dualIdem (x : X) : (∑ m : Fin (D + 1), Y.dualIdem x m) = 1 := by
  ext a b
  rw [Matrix.sum_apply, Matrix.one_apply]
  simp only [SchemeData.dualIdem, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    simp only [SchemeData.dualIdem, Matrix.diagonal_apply, eq_self_iff_true, if_true]
    obtain ⟨m₀, hm₀, huniq⟩ := Y.scheme.rel_total x a
    have hside : ∀ m ∈ (Finset.univ : Finset (Fin (D + 1))), m ≠ m₀ →
        (if Y.scheme.rel m x a then (1 : ℂ) else 0) = 0 := by
      intro m _ hm
      rw [if_neg (fun h => hm (huniq m h))]
    have hout : m₀ ∉ (Finset.univ : Finset (Fin (D + 1))) →
        (if Y.scheme.rel m₀ x a then (1 : ℂ) else 0) = 0 :=
      fun h => absurd (Finset.mem_univ m₀) h
    rw [Finset.sum_eq_single m₀ hside hout, if_pos hm₀]
  · rw [if_neg hab]
    refine Finset.sum_eq_zero fun m _ => ?_
    simp only [SchemeData.dualIdem, Matrix.diagonal_apply, if_neg hab]

/-- `A*_0(x) = 1`. -/
theorem dualA_zero (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) (x : X) : Y.dualA x 0 = 1 := by
  have hk : ∀ j, Y.kval j ≠ 0 :=
    fun j => Y.kval_ne_zero_of_rel (Y.rel_exists_of_E_ne_zero hne j)
  have hone : ∀ m : Fin (D + 1), Y.qcoef 0 m = 1 := fun m => Y.qcoef_zero_row hX hE0 hk m
  show (∑ m, Y.qcoef 0 m • Y.dualIdem x m) = 1
  rw [Finset.sum_congr rfl (fun m _ => by rw [hone m, one_smul]), Y.sum_dualIdem x]

/-- The span of `1, A*₁, …, A*₁^j`. -/
def powersSpan (x : X) (j : ℕ) : Submodule ℂ (Matrix X X ℂ) :=
  Submodule.span ℂ (Set.range fun k : Fin (j + 1) => (Y.dualA x 1) ^ (k : ℕ))

theorem powersSpan_mono (x : X) {a b : ℕ} (hab : a ≤ b) : Y.powersSpan x a ≤ Y.powersSpan x b := by
  rw [powersSpan, Submodule.span_le]
  rintro M ⟨k, rfl⟩
  exact Submodule.subset_span ⟨⟨k.1, by omega⟩, rfl⟩

/-- Multiplying `A*₁ · powersSpan x a` lands in `powersSpan x (a+1)`. -/
theorem dualA_mul_powersSpan (x : X) {a : ℕ} {v : Matrix X X ℂ}
    (hv : v ∈ Y.powersSpan x a) : Y.dualA x 1 * v ∈ Y.powersSpan x (a + 1) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
      obtain ⟨k, rfl⟩ := hw
      rw [← pow_succ']
      exact Submodule.subset_span ⟨⟨k.1 + 1, by omega⟩, rfl⟩
  | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [Matrix.mul_add]; exact Submodule.add_mem _ hu hw
  | smul c w _ hw => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hw

/-- `A*_j ∈ span{1, A*₁, …, A*₁^j}` for `j ≤ D`. -/
theorem dualA_mem_powers (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) (hD1 : 1 ≤ D) (hY : Y.IsQPolynomial)
    (hvan : ∀ i k : Fin (D + 1),
      Y.E i * Y.dualA x 1 * Y.E k = 0 ↔ Y.krein 1 i k = 0) (x : X) :
    ∀ j : ℕ, ∀ (_ : j ≤ D), Y.dualA x ⟨j, by omega⟩ ∈ Y.powersSpan x j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj
    rcases j with _ | _ | m
    · rw [show Y.dualA x ⟨0, by omega⟩ = (Y.dualA x 1) ^ 0 from by
        rw [pow_zero]
        exact Y.dualA_zero hX hE0 hne x]
      exact Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
    · have h1v := one_val_of_le (D := D) hD1
      have h1eq : (⟨1, by omega⟩ : Fin (D + 1)) = 1 := Fin.ext (by
        simp only [Fin.val_mk]
        omega)
      rw [show Y.dualA x ⟨1, by omega⟩ = (Y.dualA x 1) ^ 1 from by rw [pow_one, h1eq]]
      exact Submodule.subset_span ⟨⟨1, by omega⟩, rfl⟩
    · -- the recurrence at index `m+1`
      have hm : m ≤ D := by omega
      have hm1 : m + 1 ≤ D := by omega
      have hmem1 : Y.dualA x ⟨m + 1, by omega⟩ ∈ Y.powersSpan x (m + 1) := ih (m + 1) (by omega) (by omega)
      have hmem0 : Y.dualA x ⟨m, by omega⟩ ∈ Y.powersSpan x m := ih m (by omega) (by omega)
      -- multiplication rule and the Q-polynomial band
      have hmul := Y.dualA_mul_dualA hX x 1 ⟨m + 1, by omega⟩
      have hband : ∀ k : Fin (D + 1), k ≠ ⟨m, by omega⟩ → k ≠ ⟨m + 1, by omega⟩ →
          k ≠ ⟨m + 2, by omega⟩ → Y.krein 1 ⟨m + 1, by omega⟩ k = 0 := by
        intro k h0 h1 h2
        have hval : ((⟨m + 1, by omega⟩ : Fin (D + 1)) : ℕ) = m + 1 := rfl
        have hq := (Y.q_polynomial_iff hY).1 ⟨m + 1, by omega⟩ k
        rcases lt_trichotomy (k.1) (m + 1) with hlt | heq | hgt
        · have hkm : k.1 ≠ m := fun hc => h0 (Fin.ext (by simpa using hc))
          refine hq (Or.inr ?_)
          omega
        · exact absurd (Fin.ext (by simpa using heq)) h1
        · have hkm2 : k.1 ≠ m + 2 := fun hc => h2 (Fin.ext (by simpa using hc))
          refine hq (Or.inl ?_)
          omega
      have hc : Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ ≠ 0 :=
        (Y.q_polynomial_iff hY).2 ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ (Or.inl (by simp))
      have hsum : (∑ k : Fin (D + 1), Y.krein 1 ⟨m + 1, by omega⟩ k • Y.dualA x k)
          = Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ • Y.dualA x ⟨m + 2, by omega⟩
            + Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩ • Y.dualA x ⟨m + 1, by omega⟩
            + Y.krein 1 ⟨m + 1, by omega⟩ ⟨m, by omega⟩ • Y.dualA x ⟨m, by omega⟩ := by
        have hsub : ({⟨m + 2, by omega⟩, ⟨m + 1, by omega⟩, ⟨m, by omega⟩} :
            Finset (Fin (D + 1))) ⊆ Finset.univ := Finset.subset_univ _
        have hzero_out : ∀ k ∈ (Finset.univ : Finset (Fin (D + 1))),
            k ∉ ({⟨m + 2, by omega⟩, ⟨m + 1, by omega⟩, ⟨m, by omega⟩} :
              Finset (Fin (D + 1))) →
            Y.krein 1 ⟨m + 1, by omega⟩ k • Y.dualA x k = 0 := by
          intro k _ hk
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
          rw [hband k hk.2.2 hk.2.1 hk.1, zero_smul]
        rw [← Finset.sum_subset hsub hzero_out]
        rw [Finset.sum_insert (by simp), Finset.sum_insert (by simp), Finset.sum_singleton]
        abel
      have hrec : Y.dualA x ⟨m + 2, by omega⟩ = (Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩)⁻¹ •
          (Y.dualA x 1 * Y.dualA x ⟨m + 1, by omega⟩
            - Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩ • Y.dualA x ⟨m + 1, by omega⟩
            - Y.krein 1 ⟨m + 1, by omega⟩ ⟨m, by omega⟩ • Y.dualA x ⟨m, by omega⟩) := by
        have hkey : Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 2, by omega⟩ •
            Y.dualA x ⟨m + 2, by omega⟩
            = Y.dualA x 1 * Y.dualA x ⟨m + 1, by omega⟩
              - Y.krein 1 ⟨m + 1, by omega⟩ ⟨m + 1, by omega⟩ • Y.dualA x ⟨m + 1, by omega⟩
              - Y.krein 1 ⟨m + 1, by omega⟩ ⟨m, by omega⟩ • Y.dualA x ⟨m, by omega⟩ := by
          rw [hmul, hsum]
          abel
        rw [← hkey]
        exact (inv_smul_smul₀ hc (Y.dualA x ⟨m + 2, by omega⟩)).symm
      rw [hrec]
      refine Submodule.smul_mem _ _ ?_
      refine Submodule.sub_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · exact Y.dualA_mul_powersSpan x hmem1
      · exact Y.powersSpan_mono x (by omega) (Submodule.smul_mem _ _ hmem1)
      · exact Y.powersSpan_mono x (by omega) (Submodule.smul_mem _ _ hmem0)

/-- `(A*₁)^m ∈ span{A*_0, …, A*_D}`. -/
theorem pow_mem_span_dualA (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) (x : X) :
    ∀ m : ℕ, (Y.dualA x 1) ^ m ∈ Submodule.span ℂ (Set.range fun j : Fin (D + 1) => Y.dualA x j) := by
  intro m
  induction m with
  | zero =>
      have h := Y.dualA_zero hX hE0 hne x
      rw [pow_zero, ← h]
      exact Submodule.subset_span ⟨0, rfl⟩
  | succ m ih =>
      rw [pow_succ']
      -- `A*₁` carries `W` into `W`
      have hmulW : ∀ v ∈ Submodule.span ℂ (Set.range fun j : Fin (D + 1) => Y.dualA x j),
          Y.dualA x 1 * v ∈ Submodule.span ℂ (Set.range fun j : Fin (D + 1) => Y.dualA x j) := by
        intro v hv
        induction hv using Submodule.span_induction with
        | mem w hw =>
            obtain ⟨j, rfl⟩ := hw
            rw [Y.dualA_mul_dualA hX x 1 j]
            exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
        | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [Matrix.mul_add]; exact Submodule.add_mem _ hu hw
        | smul c w _ hw => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hw
      exact hmulW _ ih

/-- **The powers of `A*₁(x)` are linearly independent** up to the dimension `D+1`. -/
theorem linearIndependent_powers_dualA (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) (hD1 : 1 ≤ D) (hD3 : 3 ≤ D) (hY : Y.IsQPolynomial)
    (hvan : ∀ i k : Fin (D + 1),
      Y.E i * Y.dualA x 1 * Y.E k = 0 ↔ Y.krein 1 i k = 0) (x : X) :
    LinearIndependent ℂ (fun k : Fin (D + 1) => (Y.dualA x 1) ^ (k : ℕ)) := by
  set W := Submodule.span ℂ (Set.range fun j : Fin (D + 1) => Y.dualA x j) with hW
  have hfrW : Module.finrank ℂ ↥W = D + 1 := by
    rw [finrank_span_eq_card (Y.linearIndependent_dualA hX hne x)]
    simp
  have hle : Y.powersSpan x D ≤ W := by
    rw [powersSpan, Submodule.span_le]
    rintro M ⟨k, rfl⟩
    exact Y.pow_mem_span_dualA hX hE0 hne x (k : ℕ)
  have hge : W ≤ Y.powersSpan x D := by
    rw [Submodule.span_le]
    rintro M ⟨j, rfl⟩
    refine Y.powersSpan_mono x (show (j : ℕ) ≤ D from by omega) ?_
    exact Y.dualA_mem_powers hX hE0 hne hD1 hY hvan x (j : ℕ) (by omega)
  have heq : Y.powersSpan x D = W := le_antisymm hle hge
  rw [linearIndependent_iff_card_eq_finrank_span]
  have hspan : Submodule.span ℂ (Set.range fun k : Fin (D + 1) => (Y.dualA x 1) ^ (k : ℕ))
      = Y.powersSpan x D := rfl
  rw [Set.finrank, hspan, heq, hfrW]
  simp

/-- **The dual eigenvalues `q₁(m)` are distinct** (for distinct relation indices). -/
theorem qcoef_one_injective (hX : 0 < Fintype.card X)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hne : ∀ j, Y.E j ≠ 0) (hD1 : 1 ≤ D) (hD3 : 3 ≤ D) (hY : Y.IsQPolynomial)
    (hvan : ∀ i k : Fin (D + 1),
      Y.E i * Y.dualA x 1 * Y.E k = 0 ↔ Y.krein 1 i k = 0) (x : X) :
    Function.Injective (Y.qcoef 1) := by
  have hind := Y.linearIndependent_powers_dualA hX hE0 hne hD1 hD3 hY hvan x
  intro a b hab
  by_contra hne_ab
  -- the polynomial `∏_{m ≠ b} (X - q₁(m))` of degree `D` annihilates `A*₁`
  set p : Polynomial ℂ := ∏ m ∈ (Finset.univ.erase b), (Polynomial.X - Polynomial.C (Y.qcoef 1 m))
    with hp
  have hfac : ∀ m ∈ (Finset.univ.erase b),
      (Polynomial.X - Polynomial.C (Y.qcoef 1 m)) ≠ 0 := by
    intro m _
    exact Polynomial.X_sub_C_ne_zero _
  have hdeg : p.natDegree = D := by
    rw [hp, Polynomial.natDegree_prod _ _ hfac]
    rw [Finset.sum_congr rfl (fun m _ => Polynomial.natDegree_X_sub_C (Y.qcoef 1 m))]
    rw [Finset.sum_const, smul_eq_mul, mul_one]
    simp [Finset.card_erase_of_mem (Finset.mem_univ b)]
  have heval : ∀ m : Fin (D + 1), Polynomial.eval (Y.qcoef 1 m) p = 0 := by
    intro m
    rw [hp, Polynomial.eval_prod]
    by_cases hmb : m = b
    · subst hmb
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hne_ab, Finset.mem_univ a⟩) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, hab]
      ring
    · refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hmb, Finset.mem_univ m⟩) ?_
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
  -- `p(A*₁) = 0`, entrywise
  have hdiag : Y.dualA x 1 = Matrix.diagonal (fun y => Y.dualA x 1 y y) := by
    ext y z
    by_cases hyz : y = z
    · subst hyz; rw [Matrix.diagonal_apply, if_pos rfl]
    · rw [Matrix.diagonal_apply, if_neg hyz, Y.dualA_apply_of_ne x 1 hyz]
  have hzero : Polynomial.aeval (Y.dualA x 1) p = 0 := by
    ext y z
    rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.zero_apply]
    by_cases hyz : y = z
    · subst hyz
      obtain ⟨m, hm, -⟩ := Y.scheme.rel_total y x
      have hterm : ∀ k ∈ Finset.range (p.natDegree + 1),
          (p.coeff k • (Y.dualA x 1) ^ k) y y = p.coeff k * (Y.qcoef 1 m) ^ k := by
        intro k _
        rw [Matrix.smul_apply, smul_eq_mul, hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply,
          if_pos rfl, Pi.pow_apply, Y.dualA_apply_self hX (j := 1) hm]
      rw [Finset.sum_congr rfl hterm, ← Polynomial.eval_eq_sum_range, heval m]
    · refine Finset.sum_eq_zero fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, hdiag, Matrix.diagonal_pow, Matrix.diagonal_apply,
        if_neg hyz, mul_zero]
  have hp_ne : p ≠ 0 := by
    rw [hp]
    exact Finset.prod_ne_zero_iff.mpr (fun m _ => Polynomial.X_sub_C_ne_zero (Y.qcoef 1 m))
  have hcoeff : p.coeff p.natDegree ≠ 0 := by
    have h := Polynomial.leadingCoeff_ne_zero.mpr hp_ne
    rwa [Polynomial.leadingCoeff] at h
  have hdep_range : (∑ k ∈ Finset.range (D + 1), p.coeff k • (Y.dualA x 1) ^ k) = 0 := by
    have h := hzero
    rw [Polynomial.aeval_eq_sum_range] at h
    rwa [hdeg] at h
  have hdep : (∑ k : Fin (D + 1), p.coeff (k : ℕ) • (Y.dualA x 1) ^ (k : ℕ)) = 0 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i • (Y.dualA x 1) ^ i) (D + 1), hdep_range]
  have hk := Fintype.linearIndependent_iff.mp hind (fun k : Fin (D + 1) => p.coeff (k : ℕ)) hdep
    ⟨p.natDegree, by omega⟩
  exact hcoeff (by simpa using hk)

/-- `Eᵢ ≠ 0` for all `i` forces `X` to be nonempty. -/
theorem card_pos_of_E_ne_zero (hne : ∀ j, Y.E j ≠ 0) : 0 < Fintype.card X := by
  rcases Nat.eq_zero_or_pos (Fintype.card X) with h | h
  · exfalso
    have hE : IsEmpty X := Fintype.card_eq_zero_iff.mp h
    refine hne 0 ?_
    ext x y
    exact (hE.false x).elim
  · exact h

/-- **Theorem 24.2 (balanced conditions), direction (ia) ⇒ (ic)** (Chapter 24, lecture 24's
proof: Claims 1–3).  If `Y` is `Q`-polynomial then the balanced condition holds.

Hypotheses (reported as deviations from the draft statement): `X` nonempty, `Eᵢ ≠ 0` for all `i`
(so that `(Eᵢ)` is a basis of the Bose–Mesner algebra and every class is nonempty, cf. wave-2
fix 1), the distinctness `q₁(h) ≠ q₁(0)` of the dual eigenvalues (Lemma `q-conditions`
(iii)⇒(iv); it is what makes the `D` columns in Claim 2 (i) independent), and Lemma 20.3 (ii)
(`vanishing_condition`, the item of wave-2 section W-h) in the form `hvan`.

NOTE (reported): the *converse* (ic) ⇒ (ia) — the `⟸` of the draft's `↔` — is not proved in
lecture 24 (the chapter proves (ia) ⇒ (ib) and the coefficient formula (ii) only), so the
equivalence is not claimed here.  The `P`-polynomial hypothesis of wave-2 fix 6 is not needed
for the direction proved, and `SchemeData` records no `P`-polynomial predicate. -/
theorem balanced (x : X) (hD : 3 ≤ D) (hne : ∀ j, Y.E j ≠ 0)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hY : Y.IsQPolynomial)
    (hvan : ∀ i k : Fin (D + 1),
      Y.E i * Y.dualA x 1 * Y.E k = 0 ↔ Y.krein 1 i k = 0) :
    Y.IsBalanced x := by
  have hX : 0 < Fintype.card X := Y.card_pos_of_E_ne_zero hne
  have hdual : ∀ h : Fin (D + 1), h ≠ 0 → Y.qcoef 1 h ≠ Y.qcoef 1 0 := by
    intro h hh hc
    exact hh (Y.qcoef_one_injective hX hE0 hne (by omega) hD hY hvan x hc)
  have hband : ∀ i k : Fin (D + 1), (i : ℕ) + 2 ≤ (k : ℕ) ∨ (k : ℕ) + 2 ≤ (i : ℕ) →
      Y.E i * Y.dualA x 1 * Y.E k = 0 := by
    intro i k hik
    exact Y.band_of_qpoly hY hvan (by omega) hik
  have hXmem : Y.A 1 * Y.dualA x 1 * Y.A 2 - Y.A 2 * Y.dualA x 1 * Y.A 1
      ∈ Y.balancedSpan x :=
    Y.commutator_mem_of_mem hband (Y.A 1) (Y.A_mem_span_E 1) (Y.A 2) (Y.A_mem_span_E 2)
  -- the family `A*A_h - A_hA*` (`h ≠ 0`) is independent and lies in `L`; both spaces have dim `D`
  have hind := Y.linearIndependent_balancedFamily hX hne hdual x
  have hVL : Submodule.span ℂ (Set.range (Y.balancedFamily x)) ≤ Y.balancedSpan x := by
    rw [Submodule.span_le]
    rintro M ⟨h, rfl⟩
    exact Y.balancedFamily_mem hband h
  have hfrV : Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (Y.balancedFamily x))) = D := by
    rw [finrank_span_eq_card hind]
    simp
  have hfrL : Module.finrank ℂ ↥(Y.balancedSpan x) ≤
      Module.finrank ℂ ↥(Submodule.span ℂ (Set.range (Y.balancedFamily x))) := by
    rw [hfrV]
    exact Y.finrank_balancedSpan_le x
  have hEq : Submodule.span ℂ (Set.range (Y.balancedFamily x)) = Y.balancedSpan x :=
    Submodule.eq_of_le_of_finrank_le hVL hfrL
  have hXV : Y.A 1 * Y.dualA x 1 * Y.A 2 - Y.A 2 * Y.dualA x 1 * Y.A 1
      ∈ Submodule.span ℂ (Set.range (Y.balancedFamily x)) := by
    rw [hEq]
    exact hXmem
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hXV
  have h1v : ((1 : Fin (D + 1)) : ℕ) = 1 := one_val_of_le (D := D) (by omega)
  have hfilter : (Finset.univ : Finset (Fin (D + 1))).filter (fun h => 1 ≤ h)
      = Finset.univ.filter (fun h => h ≠ 0) := by
    apply Finset.filter_congr
    intro h _
    rw [Fin.le_def, h1v]
    constructor
    · intro hle heq
      rw [heq] at hle
      simp at hle
    · intro hne
      have hv : (h : ℕ) ≠ 0 := fun hc => hne (Fin.ext (by simpa using hc))
      omega
  refine ⟨fun h => if hh : h ≠ 0 then c ⟨h, hh⟩ else 0, ?_⟩
  rw [← hc, hfilter]
  rw [Finset.sum_subtype (p := fun h : Fin (D + 1) => h ≠ 0)
    (s := Finset.univ.filter (fun h : Fin (D + 1) => h ≠ 0))
    (f := fun h => (if hh : h ≠ 0 then c ⟨h, hh⟩ else 0)
      • (Y.dualA x 1 * Y.A h - Y.A h * Y.dualA x 1))
    (fun x => by simp)]
  exact Finset.sum_congr rfl fun a _ => by
    show c a • Y.balancedFamily x a
      = (if hh : (a : Fin (D + 1)) ≠ 0 then c ⟨a.1, hh⟩ else 0)
        • (Y.dualA x 1 * Y.A a.1 - Y.A a.1 * Y.dualA x 1)
    rw [dif_pos a.2]
    rfl

/-- **Theorem 24.2 (ia) ⇒ (ic)**, with the band vanishing hypothesis discharged from
Lemma 20.3 (ii) (`vanishing_condition`, the item of wave-2 section W-h, now proved
with the `hne`/`hherm`/`hk` hypotheses).  `hrel` (every class nonempty at `x`) is
what 20.3 needs at the fixed vertex.  The main `balanced` takes the vanishing
statement as an explicit hypothesis `hvan`. -/
theorem balanced_of_vanishing_condition (x : X) (hD : 3 ≤ D) (hne : ∀ j, Y.E j ≠ 0)
    (hherm : ∀ j, (Y.E j)ᴴ = Y.E j)
    (hrel : ∀ k : Fin (D + 1), ∃ z, Y.scheme.rel k x z)
    (hE0 : Y.E 0 = (1 / (Fintype.card X : ℂ)) • (allOne : Matrix X X ℂ))
    (hY : Y.IsQPolynomial) :
    Y.IsBalanced x :=
  Y.balanced x hD hne hE0 hY
    (fun i k => (Y.vanishing_condition hne hherm x i 1 k (hrel k)).2)

/-- **Definition 27.3.**  `Γ` has classical parameters `(q, α, σ)` if
`cᵢ = [i/1](1 + α[i-1/1])` and `bᵢ = ([D/1] - [i/1])(σ - α[i/1])`. -/
def HasClassicalParameters (c b : ℕ → ℝ) (q α σ : ℝ) : Prop :=
  (∀ i, c i = gaussBinom q i * (1 + α * gaussBinom q (i - 1))) ∧
    (∀ i, b i = (gaussBinom q D - gaussBinom q i) * (σ - α * gaussBinom q i))


/- **Lemma 27.4.**  DRAFT STATEMENT REMOVED (R2g audit).

The draft quantified `c b q α σ` with only `HasClassicalParameters c b q α σ` as a
hypothesis.  Nothing in that hypothesis refers to the scheme `Y`, so the statement
is false: `classical_parameters_q_polynomial_draft_false` below exhibits a
`SchemeData` (the degenerate one-point scheme, `D = 3`) for which the claimed
identity at `i = 0` reads `0 = 1`.  The corrected statement (same name, with the
hypotheses actually used in the proof, in particular the three-term recurrence for
the dual eigenvalues) and its proof are at the end of the file. -/

end SchemeData

end Terwilliger

/-! ## Lemma 27.4 (R2g): the gaussian-binomial recursion and the
classical-parameters closed form

`classical_parameters_closed_form` proves the computational content of Lemma
27.4 (ii): any ratio sequence `θ*_i/θ*_0` of dual eigenvalues satisfying the
three-term recurrence with classical parameters `(q, α, σ)` is given by
`1 + (θ/k - 1)[i/1]q^{1-i}`.  `classical_parameters_q_polynomial` is the
corrected form of the lemma in the `SchemeData` language, and
`classical_parameters_q_polynomial_draft_false` records that the draft statement
(as it stood in this file) is refutable. -/

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem gaussBinom_zero (q : ℝ) : gaussBinom q 0 = 0 := by simp [gaussBinom]
theorem gaussBinom_one (q : ℝ) : gaussBinom q 1 = 1 := by simp [gaussBinom]
theorem gaussBinom_succ (q : ℝ) (i : ℕ) :
    gaussBinom q (i + 1) = gaussBinom q i + q ^ i := by
  simp [gaussBinom, Finset.sum_range_succ]
theorem gaussBinom_mul_sub_one (q : ℝ) (i : ℕ) :
    gaussBinom q i * (q - 1) = q ^ i - 1 := by
  simpa [gaussBinom] using geom_sum_mul q i
theorem gaussBinom_mul_eq (q : ℝ) (i : ℕ) :
    q * gaussBinom q i = gaussBinom q (i + 1) - 1 := by
  have h1 := gaussBinom_mul_sub_one q i
  have h2 := gaussBinom_succ q i
  linarith
theorem gaussBinom_succ_sub_mul (q : ℝ) (i : ℕ) :
    gaussBinom q (i + 1) - q * gaussBinom q i = 1 := by
  have h := gaussBinom_mul_eq q i
  linarith
theorem gaussBinom_sub_mul_pred (q : ℝ) {i : ℕ} (h : 1 ≤ i) :
    gaussBinom q i - q * gaussBinom q (i - 1) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [hk, Nat.add_sub_cancel]
  exact gaussBinom_succ_sub_mul q k
theorem pow_eq_one_add (q : ℝ) (i : ℕ) : q ^ i = 1 + gaussBinom q i * (q - 1) := by
  have h := gaussBinom_mul_sub_one q i
  linarith

/-- The closed form of Lemma 27.4 (ii): `θ*ᵢ/θ*₀ = 1 + (θ/k - 1)[i/1]q^{1-i}`. -/
def classicalClosedForm (q : ℝ) (θ k : ℝ) (i : ℕ) : ℝ :=
  1 + (θ / k - 1) * gaussBinom q i * q ^ (1 - (i : ℤ))

theorem classical_core {D : ℕ} {c b : ℕ → ℝ} {q α σ : ℝ} (hq : q ≠ 0)
    (hc : SchemeData.HasClassicalParameters (D := D) c b q α σ) {i : ℕ} (h1 : 1 ≤ i) :
    b i - q * c i = b 0 * q ^ i + (b 1 / q - 1 - b 0) * gaussBinom q i * q := by
  have hci : c i = gaussBinom q i * (1 + α * gaussBinom q (i - 1)) := hc.1 i
  have hbi : b i = (gaussBinom q D - gaussBinom q i) * (σ - α * gaussBinom q i) := hc.2 i
  have hb0 : b 0 = gaussBinom q D * σ := by
    rw [hc.2 0]; simp [gaussBinom_zero]
  have hb1 : b 1 = (gaussBinom q D - 1) * (σ - α) := by
    rw [hc.2 1]; simp [gaussBinom_one]
  have hrel : q * gaussBinom q (i - 1) = gaussBinom q i - 1 := by
    have := gaussBinom_sub_mul_pred q h1
    linarith
  have hP : q ^ i = 1 + gaussBinom q i * (q - 1) := pow_eq_one_add q i
  rw [hci, hbi, hb0, hb1, hP]
  have hkey : q * (gaussBinom q i * (1 + α * gaussBinom q (i - 1)))
      = q * gaussBinom q i + α * gaussBinom q i * (q * gaussBinom q (i - 1)) := by ring
  rw [hkey, hrel]
  field_simp
  ring

/-! ### zpow bookkeeping -/

theorem zpow_one_sub_eq_mul (q : ℝ) (hq : q ≠ 0) (m : ℤ) :
    q ^ (1 - m) = q * q ^ (-m) := by
  have h : (1 - m) = 1 + (-m) := by ring
  rw [h, zpow_one_add₀ hq]

theorem zpow_neg_mul_pow (q : ℝ) (hq : q ≠ 0) (i : ℕ) :
    q ^ (-(i : ℤ)) * q ^ i = 1 := by
  rw [_root_.zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero i hq)]

theorem cast_pred (i : ℕ) (h : 1 ≤ i) : ((i - 1 : ℕ) : ℤ) = (i : ℤ) - 1 := by
  rw [Nat.cast_sub h]; norm_num

theorem cast_succ (i : ℕ) : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring

theorem classicalClosedForm_zero (q θ k : ℝ) : classicalClosedForm q θ k 0 = 1 := by
  simp [classicalClosedForm, gaussBinom_zero]

theorem classicalClosedForm_one (q θ k : ℝ) :
    classicalClosedForm q θ k 1 = θ / k := by
  simp [classicalClosedForm, gaussBinom_one]

/-- Step of the recurrence: `ρ_{i-1} - ρ_i = -(θ/k-1) q^{1-i}`. -/
theorem classicalClosedForm_pred_sub (q θ k : ℝ) (hq : q ≠ 0) {i : ℕ} (h1 : 1 ≤ i) :
    classicalClosedForm q θ k (i - 1) - classicalClosedForm q θ k i
      = -(θ / k - 1) * q ^ (1 - (i : ℤ)) := by
  have hz : q ^ (1 - ((i - 1 : ℕ) : ℤ)) = q * q ^ (1 - (i : ℤ)) := by
    rw [cast_pred i h1]
    have h : 1 - ((i : ℤ) - 1) = 1 + (1 - (i : ℤ)) := by ring
    rw [h, zpow_one_add₀ hq]
  have hrel : q * gaussBinom q (i - 1) = gaussBinom q i - 1 := by
    have := gaussBinom_sub_mul_pred q h1
    linarith
  simp only [classicalClosedForm]
  rw [hz]
  linear_combination (θ / k - 1) * q ^ (1 - (i : ℤ)) * hrel

/-- Step of the recurrence: `ρ_{i+1} - ρ_i = (θ/k-1) q^{-i}`. -/
theorem classicalClosedForm_succ_sub (q θ k : ℝ) (hq : q ≠ 0) (i : ℕ) :
    classicalClosedForm q θ k (i + 1) - classicalClosedForm q θ k i
      = (θ / k - 1) * q ^ (-(i : ℤ)) := by
  have hz : q ^ (1 - ((i + 1 : ℕ) : ℤ)) = q ^ (-(i : ℤ)) := by
    rw [cast_succ]
    congr 1
    ring
  have hsh : q ^ (1 - (i : ℤ)) = q * q ^ (-(i : ℤ)) := zpow_one_sub_eq_mul q hq (i : ℤ)
  have hrel : gaussBinom q (i + 1) - q * gaussBinom q i = 1 := gaussBinom_succ_sub_mul q i
  simp only [classicalClosedForm]
  rw [hz, hsh]
  linear_combination (θ / k - 1) * q ^ (-(i : ℤ)) * hrel


theorem classical_parameters_closed_form {D : ℕ} {c b : ℕ → ℝ} {q α σ : ℝ} (hq : q ≠ 0)
    (hc : SchemeData.HasClassicalParameters (D := D) c b q α σ)
    (hk : b 0 ≠ 0) (hb : ∀ i, i < D → b i ≠ 0)
    {r : ℕ → ℝ} (hr0 : r 0 = 1)
    (hrec : ∀ i, i ≤ D →
      c i * r (i - 1) + (b 0 - c i - b i) * r i + b i * r (i + 1) = (b 1 / q - 1) * r i) :
    ∀ i, i ≤ D → r i = classicalClosedForm q (b 1 / q - 1) (b 0) i := by
  have hc0 : c 0 = 0 := by rw [hc.1 0]; simp [gaussBinom_zero]
  set θ := b 1 / q - 1 with hθ
  set k := b 0 with hkk
  obtain ⟨hca, hcb⟩ := hc
  have hρrec : ∀ i, i ≤ D → c i * classicalClosedForm q θ k (i - 1)
      + (k - c i - b i) * classicalClosedForm q θ k i
      + b i * classicalClosedForm q θ k (i + 1) = θ * classicalClosedForm q θ k i := by
    intro i hi
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have hb0 : b 0 = k := hkk.symm
      have hρ1 : classicalClosedForm q θ k 1 = θ / k := classicalClosedForm_one q θ k
      have hρ0 : classicalClosedForm q θ k (0 - 1) = 1 := classicalClosedForm_zero q θ k
      have hρ0' : classicalClosedForm q θ k 0 = 1 := classicalClosedForm_zero q θ k
      simp only [hρ0, hρ1, hc0, hb0]
      have hkm : k * (θ / k) = θ := by rw [mul_comm]; exact div_mul_cancel₀ θ hk
      linarith
    · have hpred := classicalClosedForm_pred_sub q θ k hq hpos
      have hsucc := classicalClosedForm_succ_sub q θ k hq i
      have hcore := classical_core (D := D) hq ⟨hca, hcb⟩ hpos
      have hz1 : q ^ (1 - (i : ℤ)) = q * q ^ (-(i : ℤ)) := zpow_one_sub_eq_mul q hq (i : ℤ)
      have hz2 : q ^ (-(i : ℤ)) * q ^ i = 1 := zpow_neg_mul_pow q hq i
      have hz1' : q ^ (1 - (i : ℤ)) - q * q ^ (-(i : ℤ)) = 0 := by rw [hz1]; ring
      have hz2' : q ^ (-(i : ℤ)) * q ^ i - 1 = 0 := by rw [hz2]; ring
      have hβk : (θ / k - 1) * k = θ - k := by
        rw [sub_mul, one_mul, div_mul_cancel₀ θ hk]
      have hβk' : (θ / k - 1) * k - (θ - k) = 0 := by rw [hβk]; ring
      have hbi : b i = q * c i + (k * q ^ i + (θ - k) * gaussBinom q i * q) := by
        have h := hcore
        rw [← hkk, ← hθ] at h
        linarith
      have step : c i * classicalClosedForm q θ k (i - 1)
            + (k - c i - b i) * classicalClosedForm q θ k i
            + b i * classicalClosedForm q θ k (i + 1)
          = c i * (classicalClosedForm q θ k (i - 1) - classicalClosedForm q θ k i)
            + b i * (classicalClosedForm q θ k (i + 1) - classicalClosedForm q θ k i)
            + k * classicalClosedForm q θ k i := by ring
      rw [step, hpred, hsucc, hbi]
      simp only [classicalClosedForm]
      linear_combination
        (-(c i * (θ / k - 1)) - (θ - k) * (θ / k - 1) * gaussBinom q i) * hz1'
        + (k * (θ / k - 1)) * hz2' + (1 : ℝ) * hβk'
  set d : ℕ → ℝ := fun i => r i - classicalClosedForm q θ k i with hd
  have hd0 : d 0 = 0 := by simp [hd, hr0, classicalClosedForm_zero]
  have hdrec : ∀ i, i ≤ D →
      b i * d (i + 1) = (θ - (k - c i - b i)) * d i - c i * d (i - 1) := by
    intro i hi
    have h1 := hrec i hi
    have h2 := hρrec i hi
    simp only [hd]
    linarith
  have hd1 : d 1 = 0 := by
    have hb0ne : b 0 ≠ 0 := by rw [← hkk]; exact hk
    have h := hdrec 0 (by omega)
    rw [hc0, hd0] at h
    simp only [mul_zero, sub_zero] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hb0ne
    · exact h'
  have hall : ∀ j, j ≤ D → d j = 0 := by
    intro j
    induction j using Nat.twoStepInduction with
    | zero => intro _; exact hd0
    | one => intro _; exact hd1
    | more n ih1 ih2 =>
      intro hn
      have hn1 : n + 1 ≤ D := by omega
      have hbn : b (n + 1) ≠ 0 := hb (n + 1) (by omega)
      have h := hdrec (n + 1) hn1
      have e1 : d ((n + 1) - 1) = 0 := by rw [Nat.add_sub_cancel]; exact ih1 (by omega)
      rw [e1, ih2 hn1] at h
      simp only [mul_zero, sub_zero] at h
      exact (mul_eq_zero.mp h).resolve_left hbn
  intro i hi
  have h := hall i hi
  simp only [hd] at h
  exact sub_eq_zero.mp h

/-- The closed form of Lemma 27.4 (ii) in the complex form of the draft statement. -/
theorem ofReal_classicalClosedForm (q θ k : ℝ) (i : ℕ) :
    ((classicalClosedForm q θ k i : ℝ) : ℂ)
      = 1 + (↑(θ / k) - 1) * ↑(gaussBinom q i) * ↑q ^ (1 - (i : ℤ)) := by
  simp only [classicalClosedForm]
  push_cast
  ring

/-! ## Corrected form of Lemma 27.4 in the `SchemeData` language -/

namespace SchemeData

variable {D : ℕ} (Y : SchemeData X D)

/-- **Lemma 27.4 (ii), corrected.**  `θ*_i/θ*_0 = 1 + (θ/k - 1)[i/1]q^{1-i}`.

The draft statement quantified `c, b, q, α, σ` with only `HasClassicalParameters`
as a hypothesis, which does not refer to the scheme at all; the conclusion (about
`Y.qcoef`) is then false — see `classical_parameters_q_polynomial_draft_false`.
The additional hypotheses are what the notes' proof of Lemma 27.4 uses:
`hq : q ≠ 0`; `hk : b 0 ≠ 0` (`b 0 = k` is the valency); `hb : ∀ i < D, b i ≠ 0`;
`hr`, `hr0` say that `r` is the ratio sequence `θ*_i/θ*_0` of the dual eigenvalues
and `hrec` is their three-term recurrence
`c_i r_{i-1} + (k - c_i - b_i) r_i + b_i r_{i+1} = θ r_i`. -/
theorem classical_parameters_q_polynomial (c b : ℕ → ℝ) (q α σ : ℝ)
    (hc : HasClassicalParameters (D := D) c b q α σ) (hD : 3 ≤ D) (j : Fin (D + 1))
    (hq : q ≠ 0) (hk : b 0 ≠ 0) (hb : ∀ i, i < D → b i ≠ 0)
    {r : ℕ → ℝ}
    (hr : ∀ (i : ℕ) (hi : i ≤ D), (r i : ℂ) = Y.qcoef j ⟨i, Nat.lt_succ_of_le hi⟩ / Y.qcoef j 0)
    (hr0 : r 0 = 1)
    (hrec : ∀ i, i ≤ D →
      c i * r (i - 1) + (b 0 - c i - b i) * r i + b i * r (i + 1) = (b 1 / q - 1) * r i) :
    ∃ θ : ℝ, ∀ (i : ℕ) (hi : i ≤ D),
      Y.qcoef j ⟨i, Nat.lt_succ_of_le hi⟩ / Y.qcoef j 0
        = 1 + (↑θ - 1) * ↑(gaussBinom q i) * ↑q ^ (1 - (i : ℤ)) := by
  refine ⟨(b 1 / q - 1) / b 0, ?_⟩
  intro i hi
  rw [← hr i hi, classical_parameters_closed_form hq hc hk hb hr0 hrec i hi,
    ofReal_classicalClosedForm]

end SchemeData

/-! ## The draft statement of Lemma 27.4 is false

The degenerate association scheme on a one-point set (four classes: `R₀` the
diagonal, all other relations empty) carries `SchemeData`, but its `qcoef j`
vanishes identically for `j ≠ 0`.  The draft statement has no hypothesis
preventing this (nothing ties `c, b, q, α, σ` to the scheme), and its claimed
identity at `i = 0` reads `0/0 = 1 + (θ-1)[0/1]q = 1`. -/

/-- The degenerate one-point association scheme with four classes. -/
def unitScheme : AssociationScheme (Fin 1) 3 where
  rel i _ _ := (i = 0)
  rel_zero := by
    intro x y
    exact ⟨fun _ => Subsingleton.elim x y, fun _ => rfl⟩
  rel_total := by
    intro x y
    exact ⟨0, rfl, fun j hj => hj⟩
  rel_symm := by
    intro i
    exact ⟨i, fun x y => Iff.rfl⟩
  p _ i j := if i = 0 ∧ j = 0 then 1 else 0
  p_spec := by
    intro h i j x y _
    rw [Finset.card_filter, Fin.sum_univ_one]
    by_cases hp : i = 0 ∧ j = 0 <;> simp [hp]
  p_comm := by
    intro h i j
    by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj, and_comm]

/-- The association matrices of `unitScheme` are `1` on `R₀` and `0` elsewhere. -/
theorem unitScheme_assocMatrix (i : Fin (3 + 1)) :
    unitScheme.assocMatrix i = if i = 0 then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0 := by
  ext x y
  have hxy : x = y := Subsingleton.elim x y
  subst hxy
  by_cases hi : i = 0 <;> simp [hi, AssociationScheme.assocMatrix_apply, unitScheme]

/-- The degenerate `SchemeData` used to refute the draft statement. -/
def unitSchemeData : SchemeData (Fin 1) 3 where
  scheme := unitScheme
  symm := fun i x y => Iff.rfl
  E i := if i = 0 then 1 else 0
  E_idem := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  E_orth := by
    intro i j hij
    rcases eq_or_ne i 0 with hi | hi
    · rcases eq_or_ne j 0 with hj | hj
      · exact absurd (hi.trans hj.symm) hij
      · simp [hi, hj]
    · simp [hi]
  E_sum := by
    rw [Finset.sum_eq_single (0 : Fin 4) (fun b _ hb => by
      simp [show ¬ ((b : Fin 4) = 0) from hb]) (fun h => absurd (Finset.mem_univ (0 : Fin 4)) h)]
    rw [if_pos rfl]
  E_mem := by
    intro i
    by_cases hi : i = 0
    · have hEq : (if i = 0 then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0)
          = unitScheme.assocMatrix 0 := by
        rw [unitScheme_assocMatrix]
        simp [hi]
      rw [hEq]
      exact Submodule.subset_span ⟨0, rfl⟩
    · have hEq : (if i = 0 then (1 : Matrix (Fin 1) (Fin 1) ℂ) else 0) = 0 := by simp [hi]
      rw [hEq]
      exact Submodule.zero_mem _
  pcoef i j := if i = j then 1 else 0
  A_eq := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by
      simp [show ¬ ((i : Fin 4) = b) from fun h => hb h.symm])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, one_smul, unitScheme_assocMatrix]
  qcoef i j := if i = j then 1 else 0
  E_eq := by
    intro i
    rw [Finset.sum_eq_single i (fun b _ hb => by
      simp [show ¬ ((i : Fin 4) = b) from fun h => hb h.symm])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [if_pos rfl, one_smul, unitScheme_assocMatrix]
    have hX : (1 / (Fintype.card (Fin 1) : ℂ)) = 1 := by simp
    rw [hX, one_smul]
  krein i j h := if i = 0 ∧ j = 0 ∧ h = 0 then 1 else 0
  hadamard := by
    intro i j
    have hX : (1 / (Fintype.card (Fin 1) : ℂ)) = 1 := by simp
    rw [hX, one_smul]
    rw [Finset.sum_eq_single (0 : Fin 4) (fun b _ hb => by
      simp [show ¬ ((b : Fin 4) = 0) from hb])
      (fun h => absurd (Finset.mem_univ (0 : Fin 4)) h)]
    simp only [if_pos rfl, one_smul]
    funext x y
    rcases eq_or_ne i 0 with hi | hi <;> rcases eq_or_ne j 0 with hj | hj <;>
      simp [hi, hj, Matrix.one_apply, Subsingleton.elim x y]

/-- **The draft statement of Lemma 27.4 is false.**  For the degenerate one-point
scheme `unitSchemeData` (`D = 3`) and `j = 1` the claimed identity at `i = 0`
reads `0/0 = 1`. -/
theorem classical_parameters_q_polynomial_draft_false :
    ¬ (∀ (c b : ℕ → ℝ) (q α σ : ℝ),
        SchemeData.HasClassicalParameters (D := 3) c b q α σ →
        ∀ j : Fin (3 + 1), ∃ θ : ℝ, ∀ (i : ℕ) (hi : i ≤ 3),
          unitSchemeData.qcoef j ⟨i, Nat.lt_succ_of_le hi⟩ / unitSchemeData.qcoef j 0
            = 1 + (↑θ - 1) * ↑(gaussBinom q i) * ↑q ^ (1 - (i : ℤ))) := by
  intro H
  obtain ⟨θ, hθ⟩ := H (fun i => gaussBinom 1 i * (1 + 0 * gaussBinom 1 (i - 1)))
    (fun i => (gaussBinom 1 3 - gaussBinom 1 i) * (1 - 0 * gaussBinom 1 i)) 1 0 1
    ⟨fun i => rfl, fun i => rfl⟩ 1
  have h1 : unitSchemeData.qcoef (1 : Fin 4) ((0 : Fin 4)) = 0 := by
    simp [unitSchemeData]
  have h2 : gaussBinom (1 : ℝ) 0 = 0 := by simp [gaussBinom]
  have h := hθ 0 (by omega)
  rw [h1, h2] at h
  simp at h

end Terwilliger

