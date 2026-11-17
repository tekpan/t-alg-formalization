/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib

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
# The subconstituent algebra of a finite graph

This file sets up the objects of Chapter 1 of P. Terwilliger's
*Lecture Note on Terwilliger Algebra* (ed. H. Suzuki):
<https://icu-hsuzuki.github.io/t-algebra/>.

For a finite simple graph `Γ = (X, E)` and a field `𝕜` (here `ℝ` or `ℂ`, which is
what `RCLike` covers) we define

* the adjacency matrix `A` (`Terwilliger.adj`),
* the Bose–Mesner algebra `M = ⟨A⟩` (`Terwilliger.boseMesner`),
* the subconstituent projections `Eᵢ*` (`Terwilliger.subconst`),
* the dual Bose–Mesner algebra `M*(x) = ⟨E₀*, E₁*, …⟩` (`Terwilliger.dualBoseMesner`),
* the subconstituent algebra `T(x) = ⟨M, M*(x)⟩` (`Terwilliger.subconstituentAlgebra`).

`T(x)` is defined as a `StarSubalgebra`, so that closure under the adjoint is
built into the definition — this is exactly Lemma 1.8 (i) of the notes.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {𝕜 : Type*} [RCLike 𝕜]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The adjacency matrix -/

/-- The adjacency matrix of a simple graph, over the field `𝕜`. -/
def adj (G : SimpleGraph X) : Matrix X X 𝕜 := Matrix.of fun x y => if G.Adj x y then 1 else 0

@[simp]
theorem adj_apply (G : SimpleGraph X) (x y : X) :
    adj (𝕜 := 𝕜) G x y = if G.Adj x y then 1 else 0 := rfl

/-- The adjacency matrix of a simple graph is symmetric. -/
theorem adj_transpose (G : SimpleGraph X) : (adj (𝕜 := 𝕜) G)ᵀ = adj G := by
  ext x y; simp [SimpleGraph.adj_comm]

/-- The adjacency matrix of a simple graph is self-adjoint. -/
theorem star_adj (G : SimpleGraph X) : star (adj (𝕜 := 𝕜) G) = adj G := by
  ext x y
  simp only [Matrix.star_apply, adj_apply]
  by_cases h : G.Adj x y <;> simp [h, SimpleGraph.adj_comm]

/-- `A x̂ = ∑_{y ∼ x} ŷ`, where `x̂` is the indicator vector of the vertex `x`. -/
theorem adj_mulVec_single (G : SimpleGraph X) (x : X) :
    adj (𝕜 := 𝕜) G *ᵥ Pi.single x 1 = ∑ y ∈ G.neighborFinset x, Pi.single y (1 : 𝕜) := by
  ext z
  simp only [mulVec, dotProduct, Finset.sum_apply, adj_apply, Pi.single_apply]
  rw [Finset.sum_eq_single x]
  · simp [SimpleGraph.adj_comm]
  · intro b _ hb; simp [hb]
  · intro h; simp at h

/-! ## Valency and spheres -/

/-- The valency `k(x)` of a vertex. -/
def valency (G : SimpleGraph X) (x : X) : ℕ := (G.neighborFinset x).card

/-- The `i`-th sphere around `x`: the set of vertices at distance exactly `i`. -/
def sphere (G : SimpleGraph X) (x : X) (i : ℕ) : Finset X :=
  Finset.univ.filter fun y => G.dist x y = i

@[simp]
theorem mem_sphere_iff (G : SimpleGraph X) (x y : X) (i : ℕ) :
    y ∈ sphere G x i ↔ G.dist x y = i := by
  simp [sphere]

/-- The sphere around `x` of radius `0` is the singleton `{x}`. -/
theorem sphere_zero (G : SimpleGraph X) (hG : G.Connected) (x : X) :
    sphere G x 0 = {x} := by
  ext y
  simp only [mem_sphere_iff, Finset.mem_singleton]
  constructor
  · intro h
    rcases (G.dist_eq_zero_iff_eq_or_not_reachable).mp h with h' | h'
    · exact h'.symm
    · exact absurd (hG x y) h'
  · rintro rfl; simp

/-! ## The subconstituent projections `Eᵢ*(x)` -/

/-- `Eᵢ*(x)`: the orthogonal projection onto the `i`-th subconstituent
`Vᵢ*(x) = Span{ŷ | ∂(x,y) = i}`.  It is the diagonal matrix with `(y,y)`-entry
`1` if `∂(x,y) = i` and `0` otherwise. -/
def subconst (G : SimpleGraph X) (x : X) (i : ℕ) : Matrix X X 𝕜 :=
  diagonal fun y => if G.dist x y = i then 1 else 0

theorem subconst_apply (G : SimpleGraph X) (x y z : X) (i : ℕ) :
    subconst (𝕜 := 𝕜) G x i y z = if y = z then (if G.dist x y = i then 1 else 0) else 0 := by
  rw [subconst, diagonal_apply]

/-- The subconstituent projection is self-adjoint. -/
theorem star_subconst (G : SimpleGraph X) (x : X) (i : ℕ) :
    star (subconst (𝕜 := 𝕜) G x i) = subconst G x i := by
  ext y z
  simp only [Matrix.star_apply, subconst_apply]
  by_cases h : y = z <;> simp [h, eq_comm]

theorem subconst_transpose (G : SimpleGraph X) (x : X) (i : ℕ) :
    (subconst (𝕜 := 𝕜) G x i)ᵀ = subconst G x i := by
  ext y z
  simp only [Matrix.transpose_apply, subconst_apply]
  by_cases h : y = z <;> simp [h, eq_comm]

theorem subconst_mul_subconst (G : SimpleGraph X) (x : X) (i j : ℕ) :
    subconst (𝕜 := 𝕜) G x i * subconst G x j
      = if i = j then subconst G x i else 0 := by
  have key : (fun y : X =>
      (if G.dist x y = i then (1 : 𝕜) else 0) * (if G.dist x y = j then 1 else 0))
        = fun y => if i = j then (if G.dist x y = i then 1 else 0) else 0 := by
    funext y
    by_cases hi : G.dist x y = i
    · by_cases hj : G.dist x y = j
      · have hij : i = j := by rw [← hi, hj]
        simp [hi, hij]
      · have hij : i ≠ j := fun h => hj (hi.trans h)
        simp [hi, hij]
    · simp [hi]
  rw [subconst, subconst, diagonal_mul_diagonal, key]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem subconst_mul_self (G : SimpleGraph X) (x : X) (i : ℕ) :
    subconst (𝕜 := 𝕜) G x i * subconst G x i = subconst G x i := by
  simpa using subconst_mul_subconst (𝕜 := 𝕜) G x i i

/-- The `Eᵢ*` are pairwise orthogonal idempotents summing to the identity,
provided `D` is at least the eccentricity of `x`. -/
theorem sum_subconst_eq_one (G : SimpleGraph X) (x : X) (D : ℕ)
    (hD : ∀ y, G.dist x y ≤ D) :
    ∑ i ∈ Finset.range (D + 1), subconst (𝕜 := 𝕜) G x i = 1 := by
  ext y z
  rw [Matrix.sum_apply]
  by_cases hyz : y = z
  · subst hyz
    simp only [subconst_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (G.dist x y)]
    · simp
    · intro b _ hne
      simp [Ne.symm hne]
    · intro h
      simp only [Finset.mem_range, not_lt] at h
      exact absurd (hD y) (not_le.mpr h)
  · simp only [subconst_apply, if_neg hyz, Matrix.one_apply]
    simp

/-! ## The three algebras `M`, `M*(x)` and `T(x)` -/

/-- The Bose–Mesner algebra `M = ⟨A⟩` of `Γ`. -/
def boseMesner (G : SimpleGraph X) : Subalgebra 𝕜 (Matrix X X 𝕜) :=
  Algebra.adjoin 𝕜 {adj (𝕜 := 𝕜) G}

/-- The dual Bose–Mesner algebra `M*(x) = ⟨E₀*(x), E₁*(x), …⟩`. -/
def dualBoseMesner (G : SimpleGraph X) (x : X) : Subalgebra 𝕜 (Matrix X X 𝕜) :=
  Algebra.adjoin 𝕜 (Set.range (subconst (𝕜 := 𝕜) G x))

/-- The subconstituent algebra `T(x) = ⟨M, M*(x)⟩`.

It is defined as a `StarSubalgebra`, generated by the self-adjoint matrices `A`
and `Eᵢ*(x)`; by construction it is closed under the adjoint, which is
Lemma 1.8 (i) of the notes. -/
def subconstituentAlgebra (G : SimpleGraph X) (x : X) : StarSubalgebra 𝕜 (Matrix X X 𝕜) :=
  StarAlgebra.adjoin 𝕜 ({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x))

theorem adj_mem_subconstituentAlgebra (G : SimpleGraph X) (x : X) :
    adj (𝕜 := 𝕜) G ∈ subconstituentAlgebra G x :=
  StarAlgebra.subset_adjoin 𝕜 ({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x))
    (Set.mem_union_left _ rfl)

theorem subconst_mem_subconstituentAlgebra (G : SimpleGraph X) (x : X) (i : ℕ) :
    subconst (𝕜 := 𝕜) G x i ∈ subconstituentAlgebra G x :=
  StarAlgebra.subset_adjoin 𝕜 ({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x))
    (Set.mem_union_right _ ⟨i, rfl⟩)

theorem subconstituentAlgebra_le {G : SimpleGraph X} {x : X}
    {S : StarSubalgebra 𝕜 (Matrix X X 𝕜)}
    (hA : adj (𝕜 := 𝕜) G ∈ S) (hE : ∀ i, subconst (𝕜 := 𝕜) G x i ∈ S) :
    subconstituentAlgebra G x ≤ S := by
  apply StarAlgebra.adjoin_le
  rintro m (rfl | ⟨i, rfl⟩)
  · exact hA
  · exact hE i

/-- `M ⊆ T(x)`. -/
theorem boseMesner_le_subconstituentAlgebra (G : SimpleGraph X) (x : X) :
    boseMesner (𝕜 := 𝕜) G ≤ (subconstituentAlgebra G x).toSubalgebra := by
  rw [boseMesner, Algebra.adjoin_le_iff]
  exact Set.singleton_subset_iff.mpr (adj_mem_subconstituentAlgebra G x)

/-- `M*(x) ⊆ T(x)`. -/
theorem dualBoseMesner_le_subconstituentAlgebra (G : SimpleGraph X) (x : X) :
    dualBoseMesner (𝕜 := 𝕜) G x ≤ (subconstituentAlgebra G x).toSubalgebra := by
  rw [dualBoseMesner, Algebra.adjoin_le_iff]
  rintro m ⟨i, rfl⟩
  exact subconst_mem_subconstituentAlgebra G x i


/-! ## `T`-modules and orthogonal complements

Definition 1.7 and Lemma 1.8 of the notes. -/

/-- A subspace `W` of the standard module is stable under a subalgebra `T` of the
full matrix algebra. -/
def IsStable (T : Subalgebra 𝕜 (Matrix X X 𝕜)) (W : Submodule 𝕜 (X → 𝕜)) : Prop :=
  ∀ a ∈ T, ∀ w ∈ W, a *ᵥ w ∈ W

theorem isStable_bot (T : Subalgebra 𝕜 (Matrix X X 𝕜)) : IsStable T ⊥ := by
  intro a _ w hw
  simp only [Submodule.mem_bot] at hw ⊢
  rw [hw, mulVec_zero]

theorem isStable_top (T : Subalgebra 𝕜 (Matrix X X 𝕜)) : IsStable T ⊤ := by
  intro a _ w _
  simp

theorem isStable_sup {T : Subalgebra 𝕜 (Matrix X X 𝕜)} {W W' : Submodule 𝕜 (X → 𝕜)}
    (hW : IsStable T W) (hW' : IsStable T W') : IsStable T (W ⊔ W') := by
  intro a ha w hw
  rw [Submodule.mem_sup] at hw ⊢
  obtain ⟨u, hu, v, hv, rfl⟩ := hw
  exact ⟨a *ᵥ u, hW a ha u hu, a *ᵥ v, hW' a ha v hv, (mulVec_add a u v).symm⟩

/-- An irreducible `T`-module: a nonzero `T`-stable subspace with no proper nonzero
`T`-stable subspace (Definition 1.7). -/
def IsIrreducible (T : Subalgebra 𝕜 (Matrix X X 𝕜)) (W : Submodule 𝕜 (X → 𝕜)) : Prop :=
  W ≠ ⊥ ∧ ∀ U : Submodule 𝕜 (X → 𝕜), U ≤ W → IsStable T U → U ≠ ⊥ → U = W

/-- The orthogonal complement of a subspace of the standard module, with respect
to the Hermitian form `⟨w, v⟩ = ∑ w̄ᵢ vᵢ`. -/
def orthCompl (W : Submodule 𝕜 (X → 𝕜)) : Submodule 𝕜 (X → 𝕜) where
  carrier := {v | ∀ w ∈ W, star w ⬝ᵥ v = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb w hw
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [dotProduct_add, ha w hw, hb w hw, add_zero]
  smul_mem' := by
    intro c a ha w hw
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [dotProduct_smul, ha w hw, smul_zero]

@[simp]
theorem mem_orthCompl {W : Submodule 𝕜 (X → 𝕜)} {v : X → 𝕜} :
    v ∈ orthCompl W ↔ ∀ w ∈ W, star w ⬝ᵥ v = 0 := Iff.rfl

/-- **Lemma 1.8 (ii).** If `T` is closed under the adjoint then the orthogonal
complement of a `T`-module is a `T`-module. -/
theorem isStable_orthCompl {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    (hstar : ∀ a ∈ T, star a ∈ T) {W : Submodule 𝕜 (X → 𝕜)} (hW : IsStable T W) :
    IsStable T (orthCompl W) := by
  intro a ha v hv w hw
  rw [mem_orthCompl] at hv
  have h1 : star w ⬝ᵥ (a *ᵥ v) = (star w ᵥ* a) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
  have h2 : star w ᵥ* a = star ((star a) *ᵥ w) := by
    have h3 : (star a)ᴴ = a := by rw [← Matrix.star_eq_conjTranspose, star_star]
    simpa [h3] using (Matrix.star_mulVec (M := star a) (v := w)).symm
  rw [h1, h2]
  exact hv _ (hW (star a) (hstar a ha) w hw)

/-- Lemma 1.8 (ii) for the subconstituent algebra `T(x)`. -/
theorem isStable_orthCompl_subconstituent {G : SimpleGraph X} {x : X}
    {W : Submodule 𝕜 (X → 𝕜)} (hW : IsStable (subconstituentAlgebra G x).toSubalgebra W) :
    IsStable (subconstituentAlgebra G x).toSubalgebra (orthCompl W) := by
  intro a ha v hv w hw
  rw [mem_orthCompl] at hv
  have h1 : star w ⬝ᵥ (a *ᵥ v) = (star w ᵥ* a) ⬝ᵥ v := Matrix.dotProduct_mulVec _ _ _
  have h2 : star w ᵥ* a = star ((star a) *ᵥ w) := by
    have h3 : (star a)ᴴ = a := by rw [← Matrix.star_eq_conjTranspose, star_star]
    simpa [h3] using (Matrix.star_mulVec (M := star a) (v := w)).symm
  rw [h1, h2]
  exact hv _ (hW (star a) (StarMemClass.star_mem (s := subconstituentAlgebra G x) ha) w hw)

/-- The image of a subspace under a matrix. -/
def matImage (M : Matrix X X 𝕜) (W : Submodule 𝕜 (X → 𝕜)) : Submodule 𝕜 (X → 𝕜) :=
  W.map M.mulVecLin

@[simp]
theorem mem_matImage {M : Matrix X X 𝕜} {W : Submodule 𝕜 (X → 𝕜)} {v : X → 𝕜} :
    v ∈ matImage M W ↔ ∃ w ∈ W, M *ᵥ w = v :=
  Iff.rfl

/-- The `i`-th subconstituent of a `T(x)`-module. -/
def subconstImage (G : SimpleGraph X) (x : X) (i : ℕ) (W : Submodule 𝕜 (X → 𝕜)) :
    Submodule 𝕜 (X → 𝕜) :=
  matImage (subconst (𝕜 := 𝕜) G x i) W

/-! ## Lemma 1.8 (iii): complete reducibility of the standard module -/

/-- The real part of `⟨z, z⟩ = z̄ z` is the squared norm of `z`. -/
theorem cr_re_star_mul_self (z : 𝕜) : RCLike.re (star z * z) = RCLike.normSq z := by
  simp only [RCLike.star_def, RCLike.conj_eq_re_sub_im, RCLike.normSq_apply, RCLike.mul_re,
    map_sub, RCLike.ofReal_re, RCLike.ofReal_im, RCLike.im_ofReal_mul, RCLike.I_re, RCLike.I_im]
  ring

/-- Over a `RCLike` field the Hermitian form `⟨u, v⟩ = ∑ uᵢ vᵢ` is non-degenerate:
`⟨u, u⟩ = 0` forces `u = 0`. -/
theorem cr_star_dotProduct_self_eq_zero {u : X → 𝕜} (h : star u ⬝ᵥ u = 0) : u = 0 := by
  have h1 : RCLike.re (star u ⬝ᵥ u) = ∑ x, RCLike.normSq (u x) := by
    rw [dotProduct, map_sum]
    exact Finset.sum_congr rfl fun x _ => by
      simpa only [Pi.star_apply] using cr_re_star_mul_self (u x)
  rw [h, map_zero] at h1
  have h2 : ∀ x ∈ (Finset.univ : Finset X), RCLike.normSq (u x) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => RCLike.normSq_nonneg (u x))).mp h1.symm
  funext x
  exact RCLike.normSq_eq_zero.mp (h2 x (Finset.mem_univ x))

/-- Conjugate symmetry of the Hermitian form. -/
theorem cr_star_dotProduct_symm (u v : X → 𝕜) : star (star u ⬝ᵥ v) = star v ⬝ᵥ u :=
  (Matrix.star_dotProduct v u).symm

/-- **Lemma 1.8 (ii)**, general form: the intersection of two stable subspaces is stable. -/
theorem cr_isStable_inf {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    {W W' : Submodule 𝕜 (X → 𝕜)} (hW : IsStable T W) (hW' : IsStable T W') :
    IsStable T (W ⊓ W') := by
  intro a ha w hw
  rw [Submodule.mem_inf] at hw ⊢
  exact ⟨hW a ha w hw.1, hW' a ha w hw.2⟩

/-- `U` and its orthogonal complement intersect trivially. -/
theorem cr_inf_orthCompl_eq_bot (U : Submodule 𝕜 (X → 𝕜)) : U ⊓ orthCompl U = ⊥ := by
  refine le_bot_iff.mp fun v hv => ?_
  rw [Submodule.mem_inf] at hv
  exact cr_star_dotProduct_self_eq_zero (hv.2 v hv.1)

/-- Gram–Schmidt: `V = U ⊕ U^⊥` for any subspace `U`. -/
theorem cr_exists_orthogonal_decomp_aux (n : ℕ) (U : Submodule 𝕜 (X → 𝕜))
    (hU : Module.finrank 𝕜 ↥U ≤ n) (v : X → 𝕜) :
    ∃ h ∈ U, ∀ u ∈ U, star u ⬝ᵥ (v - h) = 0 := by
  induction n generalizing U with
  | zero =>
    have hbot : U = ⊥ := by
      by_contra hne
      obtain ⟨b, hbU, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hle : Submodule.span 𝕜 ({b} : Set (X → 𝕜)) ≤ U :=
        Submodule.span_le.mpr (by simpa using hbU)
      have h1 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜))) = 1 :=
        finrank_span_singleton (K := 𝕜) (V := X → 𝕜) hb0
      have h2 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜)))
          ≤ Module.finrank 𝕜 ↥U := Submodule.finrank_mono (R := 𝕜) hle
      omega
    refine ⟨0, by simp [hbot], ?_⟩
    intro u hu
    have hu0 : u = 0 := by simpa [hbot] using hu
    simp [hu0]
  | succ n ih =>
    by_cases hbot : U = ⊥
    · refine ⟨0, by simp [hbot], ?_⟩
      intro u hu
      have hu0 : u = 0 := by simpa [hbot] using hu
      simp [hu0]
    obtain ⟨b, hbU, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hbs : star b ⬝ᵥ b ≠ 0 := fun h => hb0 (cr_star_dotProduct_self_eq_zero h)
    set U₁ : Submodule 𝕜 (X → 𝕜) :=
      U ⊓ orthCompl (Submodule.span 𝕜 ({b} : Set (X → 𝕜))) with hU₁def
    have hU₁le : U₁ ≤ U := hU₁def ▸ inf_le_left
    have hbP : b ∈ Submodule.span 𝕜 ({b} : Set (X → 𝕜)) :=
      Submodule.mem_span_singleton.mpr ⟨1, one_smul _ _⟩
    have hbU₁ : b ∉ U₁ := by
      intro hb
      exact hbs (mem_orthCompl.mp (Submodule.mem_inf.mp (hU₁def ▸ hb)).2 b hbP)
    have hU₁lt : U₁ < U := lt_of_le_of_ne hU₁le (fun h => hbU₁ (h ▸ hbU))
    have hfr : Module.finrank 𝕜 ↥U₁ ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hU₁lt
      omega
    obtain ⟨h₁, hh₁, horth₁⟩ := ih U₁ hfr
    have hh₁inf : h₁ ∈ U ⊓ orthCompl (Submodule.span 𝕜 ({b} : Set (X → 𝕜))) :=
      hU₁def ▸ hh₁
    have hh₁U : h₁ ∈ U := (Submodule.mem_inf.mp hh₁inf).1
    refine ⟨h₁ + (star b ⬝ᵥ (v - h₁) / (star b ⬝ᵥ b)) • b, ?_, ?_⟩
    · exact Submodule.add_mem _ hh₁U (Submodule.smul_mem _ _ hbU)
    · intro u hu
      set d : 𝕜 := star b ⬝ᵥ u / (star b ⬝ᵥ b) with hd
      have hu₁inf : u - d • b ∈ U ⊓ orthCompl (Submodule.span 𝕜 ({b} : Set (X → 𝕜))) := by
        refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ hu (Submodule.smul_mem _ _ hbU), ?_⟩
        intro x hx
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
        rw [star_smul, smul_dotProduct, hd, dotProduct_sub, dotProduct_smul, smul_eq_mul]
        have hzero : star b ⬝ᵥ u - (star b ⬝ᵥ u / (star b ⬝ᵥ b)) • (star b ⬝ᵥ b) = 0 := by
          rw [smul_eq_mul, div_mul_cancel₀ _ hbs, sub_self]
        rw [hzero, mul_zero]
      have hu₁U₁ : u - d • b ∈ U₁ := hU₁def.symm ▸ hu₁inf
      have hu₁orth : star b ⬝ᵥ (u - d • b) = 0 :=
        mem_orthCompl.mp (Submodule.mem_inf.mp hu₁inf).2 b hbP
      have horth_u₁ : star (u - d • b) ⬝ᵥ (v - h₁) = 0 := horth₁ _ hu₁U₁
      have horth_u₁' : star (u - d • b) ⬝ᵥ b = 0 := by
        rw [← cr_star_dotProduct_symm, hu₁orth, star_zero]
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

/-- Gram–Schmidt decomposition `V = U + U^⊥`. -/
theorem cr_exists_orthogonal_decomp {U : Submodule 𝕜 (X → 𝕜)} (v : X → 𝕜) :
    ∃ h ∈ U, ∀ u ∈ U, star u ⬝ᵥ (v - h) = 0 :=
  cr_exists_orthogonal_decomp_aux (Module.finrank 𝕜 ↥U) U le_rfl v

/-- `V = U ⊔ U^⊥`. -/
theorem cr_sup_orthCompl_eq_top (U : Submodule 𝕜 (X → 𝕜)) : U ⊔ orthCompl U = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  obtain ⟨h, hhU, horth⟩ := cr_exists_orthogonal_decomp (U := U) v
  have hv : v = h + (v - h) := by abel
  rw [hv]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hhU)
    (Submodule.mem_sup_right (mem_orthCompl.mpr horth))

/-- Every nonzero stable subspace contains a nonzero irreducible stable subspace. -/
theorem cr_exists_irreducible_submodule {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    {W : Submodule 𝕜 (X → 𝕜)} (hW : IsStable T W) (hne : W ≠ ⊥) :
    ∃ U : Submodule 𝕜 (X → 𝕜), U ≤ W ∧ IsStable T U ∧ IsIrreducible T U := by
  suffices H : ∀ k, ∀ Z : Submodule 𝕜 (X → 𝕜), Z ≤ W → IsStable T Z → Z ≠ ⊥ →
      Module.finrank 𝕜 ↥Z ≤ k → ∃ U : Submodule 𝕜 (X → 𝕜), U ≤ Z ∧ IsStable T U ∧
        IsIrreducible T U from H _ W le_rfl hW hne le_rfl
  intro k
  induction k with
  | zero =>
    intro Z _ _ hZne hfr
    obtain ⟨b, hbZ, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZne
    have hle : Submodule.span 𝕜 ({b} : Set (X → 𝕜)) ≤ Z :=
      Submodule.span_le.mpr (by simpa using hbZ)
    have h1 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜))) = 1 :=
      finrank_span_singleton (K := 𝕜) (V := X → 𝕜) hb0
    have h2 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜)))
        ≤ Module.finrank 𝕜 ↥Z := Submodule.finrank_mono (R := 𝕜) hle
    omega
  | succ k ih =>
    intro Z hZW hZstab hZne hfr
    by_cases hirr : IsIrreducible T Z
    · exact ⟨Z, le_rfl, hZstab, hirr⟩
    · have hno : ∃ U : Submodule 𝕜 (X → 𝕜), U ≤ Z ∧ IsStable T U ∧ U ≠ ⊥ ∧ U ≠ Z := by
        by_contra hcon
        push Not at hcon
        exact hirr ⟨hZne, fun U hU hUstab hUne => hcon U hU hUstab hUne⟩
      obtain ⟨U, hUZ, hUstab, hUne, hUZne⟩ := hno
      have hUlt : U < Z := lt_of_le_of_ne hUZ hUZne
      have hlt : Module.finrank 𝕜 ↥U < Module.finrank 𝕜 ↥Z :=
        Submodule.finrank_lt_finrank_of_lt hUlt
      obtain ⟨U', hU'U, hU'stab, hU'irr⟩ := ih U (hUZ.trans hZW) hUstab hUne (by omega)
      exact ⟨U', hU'U.trans hUZ, hU'stab, hU'irr⟩

/-- `⨆` over the empty index type is `⊥`. -/
theorem cr_iSup_empty (f : Empty → Submodule 𝕜 (X → 𝕜)) : (⨆ i, f i) = ⊥ :=
  le_antisymm (iSup_le fun i => i.elim) bot_le

/-- Splitting an `iSup` indexed by `Option ι`. -/
theorem cr_iSup_option {ι : Type*} (f : Option ι → Submodule 𝕜 (X → 𝕜)) :
    (⨆ i, f i) = f none ⊔ ⨆ i, f (some i) := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => ?_
    cases i with
    | none => exact le_sup_left
    | some i => exact le_trans (le_iSup (fun i => f (some i)) i) le_sup_right
  · refine sup_le (le_iSup f none) ?_
    exact iSup_le fun i => le_iSup f (some i)

/-- The orthogonal irreducible decomposition, by induction on `dim W`. -/
theorem cr_orth_decomp_aux {T : Subalgebra 𝕜 (Matrix X X 𝕜)} (hstar : ∀ a ∈ T, star a ∈ T) :
    ∀ (n : ℕ) (W : Submodule 𝕜 (X → 𝕜)), IsStable T W → Module.finrank 𝕜 ↥W ≤ n →
      ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule 𝕜 (X → 𝕜)),
        (∀ i, IsStable T (U i)) ∧ (∀ i, IsIrreducible T (U i)) ∧
        (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
        (W = ⨆ i, U i) := by
  intro n
  induction n with
  | zero =>
    intro W hW hfr
    have hbot : W = ⊥ := by
      by_contra hne
      obtain ⟨b, hbW, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      have hle : Submodule.span 𝕜 ({b} : Set (X → 𝕜)) ≤ W :=
        Submodule.span_le.mpr (by simpa using hbW)
      have h1 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜))) = 1 :=
        finrank_span_singleton (K := 𝕜) (V := X → 𝕜) hb0
      have h2 : Module.finrank 𝕜 ↥(Submodule.span 𝕜 ({b} : Set (X → 𝕜)))
          ≤ Module.finrank 𝕜 ↥W := Submodule.finrank_mono (R := 𝕜) hle
      omega
    refine ⟨Empty, inferInstance, fun e => e.elim, ?_, ?_, ?_, ?_⟩
    · intro i; exact i.elim
    · intro i; exact i.elim
    · intro i; exact i.elim
    · rw [hbot, cr_iSup_empty]
  | succ n ih =>
    intro W hW hfr
    by_cases hbot : W = ⊥
    · refine ⟨Empty, inferInstance, fun e => e.elim, ?_, ?_, ?_, ?_⟩
      · intro i; exact i.elim
      · intro i; exact i.elim
      · intro i; exact i.elim
      · rw [hbot, cr_iSup_empty]
    obtain ⟨U₀, hU₀W, hU₀stab, hU₀irr⟩ := cr_exists_irreducible_submodule hW hbot
    set Z : Submodule 𝕜 (X → 𝕜) := W ⊓ orthCompl U₀ with hZdef
    have hZstab : IsStable T Z := cr_isStable_inf hW (isStable_orthCompl hstar hU₀stab)
    have hZle : Z ≤ W := inf_le_left
    have hZne : Z ≠ W := by
      intro hZW
      have hle : U₀ ≤ orthCompl U₀ := by
        intro u hu
        exact (Submodule.mem_inf.mp (hZW ▸ hU₀W hu)).2
      have hle2 : U₀ ≤ U₀ ⊓ orthCompl U₀ := fun u hu => Submodule.mem_inf.mpr ⟨hu, hle hu⟩
      rw [cr_inf_orthCompl_eq_bot] at hle2
      exact hU₀irr.1 (le_bot_iff.mp hle2)
    have hZfr : Module.finrank 𝕜 ↥Z ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hZle hZne)
      omega
    obtain ⟨ι₁, inst₁, U₁, hstab₁, hirr₁, horth₁, hsup₁⟩ := ih Z hZstab hZfr
    have hWsplit : W = U₀ ⊔ Z := by
      refine le_antisymm ?_ (sup_le hU₀W hZle)
      intro w hw
      obtain ⟨h, hhU₀, horth⟩ := cr_exists_orthogonal_decomp (U := U₀) w
      have hz : w - h ∈ Z :=
        Submodule.mem_inf.mpr
          ⟨Submodule.sub_mem W hw (hU₀W hhU₀), mem_orthCompl.mpr horth⟩
      have hwv : w = h + (w - h) := by abel
      rw [hwv]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hhU₀) (Submodule.mem_sup_right hz)
    refine ⟨Option ι₁, inferInstance, fun o => o.elim U₀ U₁, ?_, ?_, ?_, ?_⟩
    · intro i
      cases i with
      | none => exact hU₀stab
      | some i => exact hstab₁ i
    · intro i
      cases i with
      | none => exact hU₀irr
      | some i => exact hirr₁ i
    · intro i j hij u hu v hv
      cases i with
      | none =>
        cases j with
        | none => exact absurd rfl hij
        | some j =>
          have hvZ : v ∈ Z := hsup₁ ▸ Submodule.mem_iSup_of_mem j hv
          exact (Submodule.mem_inf.mp hvZ).2 u hu
      | some i =>
        cases j with
        | none =>
          have huZ : u ∈ Z := hsup₁ ▸ Submodule.mem_iSup_of_mem i hu
          have huO : star v ⬝ᵥ u = 0 := (Submodule.mem_inf.mp huZ).2 v hv
          rw [← cr_star_dotProduct_symm, huO, star_zero]
        | some j =>
          have hne : i ≠ j := fun h => hij (by rw [h])
          exact horth₁ i j hne u hu v hv
    · rw [cr_iSup_option]
      show W = U₀ ⊔ ⨆ i, U₁ i
      rw [← hsup₁, ← hWsplit]

/-- **Lemma 1.8 (iii)**: a `T`-stable subspace of the standard module is an orthogonal
direct sum of irreducible `T`-submodules. -/
theorem exists_orthogonal_irreducible_decomposition {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    (hstar : ∀ a ∈ T, star a ∈ T) (W : Submodule 𝕜 (X → 𝕜)) (hW : IsStable T W) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule 𝕜 (X → 𝕜)),
      (∀ i, IsStable T (U i)) ∧ (∀ i, IsIrreducible T (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
      (W = ⨆ i, U i) :=
  cr_orth_decomp_aux hstar (Module.finrank 𝕜 ↥W) W hW le_rfl

/-- A vector of a finite supremum of submodules is a finite sum of vectors taken from
the summands. -/
theorem cr_exists_sum_of_mem_finset_sup {ι : Type*} (s : Finset ι)
    (U : ι → Submodule 𝕜 (X → 𝕜)) :
    ∀ v : X → 𝕜, v ∈ s.sup U →
      ∃ w : ι → (X → 𝕜), (∀ i ∈ s, w i ∈ U i) ∧ (∀ i ∉ s, w i = 0) ∧
        v = ∑ i ∈ s, w i := by
  induction s using Finset.induction with
  | empty =>
    intro v hv
    simp only [Finset.sup_empty, Submodule.mem_bot] at hv
    refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro i hi
      exact absurd hi (by simp)
    · intro i _
      rfl
    · rw [hv]
      simp
  | insert a s ha ih =>
    intro v hv
    rw [Finset.sup_insert, Submodule.mem_sup] at hv
    obtain ⟨x, hx, y, hy, hxy⟩ := hv
    obtain ⟨w, hw, hw0, hvw⟩ := ih y hy
    refine ⟨fun i => if i = a then x else w i, ?_, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_insert] at hi
      by_cases hia : i = a
      · simp [hia, hx]
      · simp only [hia, if_false]
        exact hw i (hi.resolve_left hia)
    · intro i hi
      have hia : i ≠ a := fun h => hi (Finset.mem_insert.mpr (Or.inl h))
      have his : i ∉ s := fun h => hi (Finset.mem_insert.mpr (Or.inr h))
      simp only [hia, if_false]
      exact hw0 i his
    · rw [← hxy, Finset.sum_insert ha]
      have hcongr : ∑ i ∈ s, (fun i => if i = a then x else w i) i = ∑ i ∈ s, w i :=
        Finset.sum_congr rfl fun i hi => by
          have hia : i ≠ a := fun h => ha (h ▸ hi)
          simp only [hia, if_false]
      rw [hcongr, ← hvw]
      simp

/-- A vector of `⨆ i, U i` over a finite index type is a finite sum of vectors taken from
the summands. -/
theorem cr_exists_sum_of_mem_iSup {ι : Type*} [Fintype ι] {U : ι → Submodule 𝕜 (X → 𝕜)}
    {v : X → 𝕜} (hv : v ∈ ⨆ i, U i) :
    ∃ w : ι → (X → 𝕜), (∀ i, w i ∈ U i) ∧ v = ∑ i, w i := by
  have hv' : v ∈ Finset.univ.sup U := by
    rw [Finset.sup_eq_iSup]
    simpa using hv
  obtain ⟨w, hw, _, hvw⟩ := cr_exists_sum_of_mem_finset_sup Finset.univ U v hv'
  exact ⟨w, fun i => hw i (Finset.mem_univ i), by simpa using hvw⟩

/-- **Lemma 1.8 (iii)**, top-module form: `V` is an orthogonal direct sum of irreducible
`T`-modules. -/
theorem exists_orthogonal_irreducible_decomposition_top {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    (hstar : ∀ a ∈ T, star a ∈ T) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule 𝕜 (X → 𝕜)),
      (∀ i, IsStable T (U i)) ∧ (∀ i, IsIrreducible T (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
      ((⊤ : Submodule 𝕜 (X → 𝕜)) = ⨆ i, U i) :=
  exists_orthogonal_irreducible_decomposition hstar ⊤ (isStable_top T)

/-- **Lemma 1.8 (iii)** for the subconstituent algebra `T(x)` of a graph: the standard
module `V = ℂ^X` is an orthogonal direct sum of irreducible `T(x)`-modules. -/
theorem exists_orthogonal_irreducible_decomposition_subconstituent_top
    {G : SimpleGraph X} {x : X} :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule ℂ (X → ℂ)),
      (∀ i, IsStable (subconstituentAlgebra G x).toSubalgebra (U i)) ∧
      (∀ i, IsIrreducible (subconstituentAlgebra G x).toSubalgebra (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
      ((⊤ : Submodule ℂ (X → ℂ)) = ⨆ i, U i) :=
  exists_orthogonal_irreducible_decomposition_top
    (fun _a ha => StarMemClass.star_mem (s := subconstituentAlgebra G x) ha)

/-- Every nonzero `T(x)`-module contains an irreducible `T(x)`-submodule. -/
theorem exists_irreducible_submodule_of_isStable_subconstituent {G : SimpleGraph X} {x : X}
    {W : Submodule ℂ (X → ℂ)}
    (hW : IsStable (subconstituentAlgebra G x).toSubalgebra W) (hne : W ≠ ⊥) :
    ∃ U : Submodule ℂ (X → ℂ), U ≤ W ∧
      IsStable (subconstituentAlgebra G x).toSubalgebra U ∧
      IsIrreducible (subconstituentAlgebra G x).toSubalgebra U :=
  cr_exists_irreducible_submodule hW hne

/-- **Lemma 1.8 (iii)** for the subconstituent algebra `T(x)`, relative form. -/
theorem exists_orthogonal_irreducible_decomposition_subconstituent
    {G : SimpleGraph X} {x : X} (W : Submodule ℂ (X → ℂ))
    (hW : IsStable (subconstituentAlgebra G x).toSubalgebra W) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule ℂ (X → ℂ)),
      (∀ i, IsStable (subconstituentAlgebra G x).toSubalgebra (U i)) ∧
      (∀ i, IsIrreducible (subconstituentAlgebra G x).toSubalgebra (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
      (W = ⨆ i, U i) :=
  exists_orthogonal_irreducible_decomposition
    (fun _a ha => StarMemClass.star_mem (s := subconstituentAlgebra G x) ha) W hW

/-- **Lemma 1.8 (iii)**, full form with the coefficient expansion: a stable subspace `W` is
an orthogonal direct sum of finitely many irreducible stable subspaces and every vector of
`W` is a finite sum of vectors taken from the summands. -/
theorem exists_orthogonal_irreducible_decomposition_full {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    (hstar : ∀ a ∈ T, star a ∈ T) (W : Submodule 𝕜 (X → 𝕜)) (hW : IsStable T W) :
    ∃ (ι : Type) (_ : Fintype ι) (U : ι → Submodule 𝕜 (X → 𝕜)),
      (∀ i, IsStable T (U i)) ∧ (∀ i, IsIrreducible T (U i)) ∧
      (∀ i j, i ≠ j → ∀ u ∈ U i, ∀ v ∈ U j, star u ⬝ᵥ v = 0) ∧
      (W = ⨆ i, U i) ∧
      (∀ v ∈ W, ∃ w : ι → (X → 𝕜), (∀ i, w i ∈ U i) ∧ v = ∑ i, w i) := by
  obtain ⟨ι, inst, U, hstab, hirr, horth, hsup⟩ :=
    exists_orthogonal_irreducible_decomposition hstar W hW
  refine ⟨ι, inst, U, hstab, hirr, horth, hsup, ?_⟩
  intro v hv
  exact @cr_exists_sum_of_mem_iSup 𝕜 _ X _ _ ι inst U v (hsup ▸ hv)

end Terwilliger
