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
# The matrices `Eᵢ*(x) A Eⱼ*(x)`, and commutativity of `M` and `M*(x)`

Chapter 4 of Terwilliger's notes begins with the observation that `A` moves the
subconstituents by at most one step: `Eᵢ* A Eⱼ* = 0` whenever `|i - j| > 1`
(Lemma 4.3 (i)).  This is the combinatorial heart of the endpoint theory.

We also record that `M` commutes with `A` (trivially, since `M = ⟨A⟩`) and that
`M*(x)` is commutative — the notes' observation following the definition of the
dual Bose–Mesner algebra.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [Fintype X] [DecidableEq X]


/-! ### Two bookkeeping lemmas for diagonal matrices -/

theorem diagonal_mul_apply (d : X → 𝕜) (M : Matrix X X 𝕜) (y z : X) :
    (diagonal d * M) y z = d y * M y z := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single y]
  · rw [diagonal_apply_eq]
  · intro b _ hb; rw [diagonal_apply_ne _ (Ne.symm hb)]; simp
  · intro h; simp at h

theorem mul_diagonal_apply (M : Matrix X X 𝕜) (d : X → 𝕜) (y z : X) :
    (M * diagonal d) y z = M y z * d z := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single z]
  · rw [diagonal_apply_eq]
  · intro b _ hb; rw [diagonal_apply_ne _ hb]; simp
  · intro h; simp at h

/-! ## Entries of `Eᵢ* A Eⱼ*` -/

/-- Left multiplication by `Eᵢ*(x)`. -/
theorem subconst_mul_apply (G : SimpleGraph X) (x : X) (i : ℕ) (M : Matrix X X 𝕜) (y z : X) :
    (subconst (𝕜 := 𝕜) G x i * M) y z = (if G.dist x y = i then 1 else 0) * M y z := by
  rw [subconst, diagonal_mul_apply]

/-- Right multiplication by `Eⱼ*(x)`. -/
theorem mul_subconst_apply (G : SimpleGraph X) (x : X) (j : ℕ) (M : Matrix X X 𝕜) (y z : X) :
    (M * subconst (𝕜 := 𝕜) G x j) y z = M y z * (if G.dist x z = j then 1 else 0) := by
  rw [subconst, mul_diagonal_apply]

/-- The `(y,z)`-entry of `Eᵢ*(x) A Eⱼ*(x)`: it is `1` when `y ∼ z`,
`∂(x,y) = i` and `∂(x,z) = j`, and `0` otherwise. -/
theorem subconst_mul_adj_mul_subconst_apply {G : SimpleGraph X} {x y z : X} {i j : ℕ} :
    (subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G * subconst (𝕜 := 𝕜) G x j) y z
      = if G.Adj y z then (if G.dist x y = i then 1 else 0) * (if G.dist x z = j then 1 else 0)
        else 0 := by
  rw [mul_subconst_apply, subconst_mul_apply, adj_apply, mul_ite, mul_one, mul_zero]
  by_cases h : G.Adj y z <;> simp [h]

/-- **Lemma 4.3 (i).** `Eᵢ*(x) A Eⱼ*(x) = 0` whenever `|i - j| > 1`. -/
theorem subconst_mul_adj_mul_subconst_eq_zero {G : SimpleGraph X} {x : X} {i j : ℕ}
    (h : j + 1 < i ∨ i + 1 < j) :
    subconst (𝕜 := 𝕜) G x i * adj (𝕜 := 𝕜) G * subconst (𝕜 := 𝕜) G x j = 0 := by
  ext y z
  rw [subconst_mul_adj_mul_subconst_apply, Matrix.zero_apply]
  by_cases hadj : G.Adj y z
  · rw [if_pos hadj]
    by_cases h1 : G.dist x y = i
    · by_cases h2 : G.dist x z = j
      · exfalso
        have h3 := hadj.diff_dist_adj (u := x)
        omega
      · simp [h1, h2]
    · simp [h1]
  · simp [hadj]

/-! ## Two commutative subalgebras of `Mat_X(𝕜)` -/

/-- The subalgebra of diagonal matrices. -/
def diagonalSubalgebra : Subalgebra 𝕜 (Matrix X X 𝕜) where
  carrier := {m | ∃ d : X → 𝕜, m = diagonal d}
  mul_mem' := by
    rintro a b ⟨da, rfl⟩ ⟨db, rfl⟩
    exact ⟨_, diagonal_mul_diagonal _ _⟩
  one_mem' := ⟨1, (diagonal_one).symm⟩
  add_mem' := by
    rintro a b ⟨da, rfl⟩ ⟨db, rfl⟩
    exact ⟨_, diagonal_add _ _⟩
  zero_mem' := ⟨0, diagonal_zero.symm⟩
  algebraMap_mem' := by
    intro r
    exact ⟨fun _ => r, by rw [Matrix.algebraMap_eq_diagonal]; rfl⟩

/-- The centraliser of a single matrix. -/
def centralizerSubalgebra (a : Matrix X X 𝕜) : Subalgebra 𝕜 (Matrix X X 𝕜) where
  carrier := {m | Commute m a}
  mul_mem' := by
    intro x y hx hy
    exact Commute.mul_left hx hy
  one_mem' := Commute.one_left a
  add_mem' := by
    intro x y hx hy
    exact Commute.add_left hx hy
  zero_mem' := Commute.zero_left a
  algebraMap_mem' := fun r => Algebra.commute_algebraMap_left r a

/-- The dual Bose–Mesner algebra consists of diagonal matrices. -/
theorem dualBoseMesner_le_diagonal (G : SimpleGraph X) (x : X) :
    dualBoseMesner (𝕜 := 𝕜) G x ≤ diagonalSubalgebra (𝕜 := 𝕜) (X := X) := by
  rw [dualBoseMesner, Algebra.adjoin_le_iff]
  rintro m ⟨i, rfl⟩
  exact ⟨_, rfl⟩

/-- **`M*(x)` is commutative.** -/
theorem commute_of_mem_dualBoseMesner {G : SimpleGraph X} {x : X} {m n : Matrix X X 𝕜}
    (hm : m ∈ dualBoseMesner (𝕜 := 𝕜) G x) (hn : n ∈ dualBoseMesner G x) : Commute m n := by
  obtain ⟨dm, rfl⟩ := dualBoseMesner_le_diagonal (𝕜 := 𝕜) G x hm
  obtain ⟨dn, rfl⟩ := dualBoseMesner_le_diagonal (𝕜 := 𝕜) G x hn
  rw [Commute, SemiconjBy, diagonal_mul_diagonal, diagonal_mul_diagonal]
  simp [mul_comm]

/-- Every element of the Bose–Mesner algebra commutes with `A`. -/
theorem commute_of_mem_boseMesner {G : SimpleGraph X} {m : Matrix X X 𝕜}
    (hm : m ∈ boseMesner (𝕜 := 𝕜) G) : Commute m (adj G) := by
  have h : boseMesner (𝕜 := 𝕜) G ≤ centralizerSubalgebra (adj (𝕜 := 𝕜) G) := by
    rw [boseMesner, Algebra.adjoin_le_iff]
    exact Set.singleton_subset_iff.mpr (Commute.refl _)
  exact h hm

end Terwilliger
