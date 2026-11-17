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
# Cayley graphs (Chapter 3)

The Cayley graph `Γ(G, Δ)` of a finite group `G` and a symmetric generating set
`Δ ∌ 1` (Definition 3.4), its automorphism group, and characters.

The concrete results proved here are: left multiplication is an automorphism
(Theorem 3.5 (i)), `G` acts regularly on the vertex set, and the characters of an
abelian group give eigenvectors of the adjacency matrix (Theorem 4.1).
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- **Definition 3.4.** The Cayley graph `Γ(G, Δ)`: two distinct vertices `u`, `v`
are adjacent when `u⁻¹v ∈ Δ`.  (The notes assume `1 ∉ Δ` and `Δ = Δ⁻¹`, which is
what makes this relation symmetric; see `cayley_adj`.) -/
def cayleyGraph (Δ : Set G) : SimpleGraph G := SimpleGraph.mulCayley Δ

/-- Adjacency in a Cayley graph, for a symmetric generating set not containing
`1`. -/
theorem cayley_adj {Δ : Set G} (h1 : (1 : G) ∉ Δ) (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ) (u v : G) :
    (cayleyGraph Δ).Adj u v ↔ u⁻¹ * v ∈ Δ := by
  rw [cayleyGraph, SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · have h' := hsym _ h
      have h2 : (v⁻¹ * u)⁻¹ = u⁻¹ * v := by group
      rwa [h2] at h'
  · refine fun h => ⟨?_, Or.inl h⟩
    rintro rfl
    exact h1 (by simpa using h)

/-- **Theorem 3.5 (i).** Left multiplication by `g` is an automorphism of
`Γ(G, Δ)`. -/
theorem cayley_left_mul_adj {Δ : Set G} (h1 : (1 : G) ∉ Δ)
    (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ) (g u v : G) :
    (cayleyGraph Δ).Adj (g * u) (g * v) ↔ (cayleyGraph Δ).Adj u v := by
  rw [cayley_adj h1 hsym, cayley_adj h1 hsym]
  have h : (g * u)⁻¹ * (g * v) = u⁻¹ * v := by group
  rw [h]

/-- The action of `G` on itself by left multiplication is transitive: `Γ(G, Δ)`
is vertex-transitive. -/
theorem cayley_vertexTransitive (_Δ : Set G) (x y : G) : ∃ g : G, g * x = y :=
  ⟨y * x⁻¹, by group⟩

/-- The image of `G` in `Aut Γ(G, Δ)` acts with trivial vertex stabilisers, i.e.
regularly: `g x = x` forces `g = 1`. -/
theorem cayley_stabilizer_trivial (x : G) {g : G} (h : g * x = x) : g = 1 := by
  have := congrArg (· * x⁻¹) h
  simpa using this

/-- The map `g ↦ (x ↦ g x)` from `G` to the permutation group of the vertex set
is injective (Theorem 3.5 (i)). -/
theorem cayley_leftRegular_injective (g₁ g₂ : G)
    (h : (fun x : G => g₁ * x) = fun x : G => g₂ * x) : g₁ = g₂ := by
  have := congrFun h 1
  simpa using this

/-! ## Characters -/

/-- The vector `θ̂` attached to a character: `x ↦ θ(x⁻¹)`. -/
def charVec (θ : G →* ℂˣ) : G → ℂ := fun x => ((θ x⁻¹ : ℂˣ) : ℂ)

/-- **Lemma 3.7.** For a finite abelian group the character group is isomorphic
to `G`.

This is `CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity` with `M = ℂ`:
`ℂ` is separably closed, hence has enough `n`-th roots of unity for every
`n ≠ 0`, in particular for `n = Monoid.exponent G`.  The two ingredients of the
Mathlib proof are exactly the notes' proof of 3.7: the structure theorem
`CommGroup.equiv_prod_multiplicative_zmod_of_finite` (`G` is a product of
cyclic groups) and the cyclic case `IsCyclic.monoidHom_equiv_self`. -/
theorem charactergroup_isIso {G : Type*} [CommGroup G] [Fintype G] :
    Nonempty (G ≃* (G →* ℂˣ)) := by
  obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ
  exact ⟨e.symm⟩

/-- Consequence of Lemma 3.7: the character group has the same cardinality
as `G` (the notes' count `|Ĝ| = |G|`). -/
theorem card_charactergroup {G : Type*} [CommGroup G] [Fintype G] :
    Nat.card (G →* ℂˣ) = Nat.card G :=
  CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ

/-- Consequence of Lemma 3.7: characters separate points of a finite abelian
group (the notes' `∩_θ ker θ = 1`). -/
theorem exists_charactergroup_apply_ne_one {G : Type*} [CommGroup G] [Fintype G]
    {a : G} (ha : a ≠ 1) : ∃ φ : G →* ℂˣ, φ a ≠ 1 :=
  CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ ha

/-- Adjacency in a Cayley graph, for a symmetric generating `Finset` not
containing `1`: `u` and `v` are adjacent exactly when `u⁻¹v ∈ Δ`.  (The `Finset`
version of `cayley_adj`.) -/
theorem cayley_adj_finset {Δ : Finset G} (h1 : (1 : G) ∉ Δ) (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ)
    (u v : G) : (cayleyGraph (Δ : Set G)).Adj u v ↔ u⁻¹ * v ∈ Δ := by
  rw [cayley_adj (Δ := (Δ : Set G)) (by simpa using h1)
    (fun g hg => by simpa using hsym g (by simpa using hg)) u v]
  exact Finset.mem_coe

/-- Adjacency in a Cayley graph: `1 ∈ Δ` is invisible, because the Cayley graph
has no loops.  So for a symmetric `Δ` the graph only depends on `Δ.erase 1`. -/
theorem cayley_adj_finset_erase {Δ : Finset G} (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ) (u v : G) :
    (cayleyGraph (Δ : Set G)).Adj u v ↔ u⁻¹ * v ∈ Δ.erase 1 := by
  show (SimpleGraph.mulCayley (Δ : Set G)).Adj u v ↔ u⁻¹ * v ∈ Δ.erase 1
  rw [SimpleGraph.mulCayley_adj]
  constructor
  · rintro ⟨hne, hmem | hmem⟩
    · have hmem' : u⁻¹ * v ∈ Δ := by simpa using hmem
      refine Finset.mem_erase.mpr ⟨?_, hmem'⟩
      intro h1
      apply hne
      have := congrArg (fun x => u * x) h1
      simpa using this.symm
    · have hmem' : v⁻¹ * u ∈ Δ := by simpa using hmem
      have hmem'' : u⁻¹ * v ∈ Δ := by
        have h2 : (v⁻¹ * u)⁻¹ = u⁻¹ * v := by group
        rw [← h2]
        exact hsym _ hmem'
      refine Finset.mem_erase.mpr ⟨?_, hmem''⟩
      intro h1
      apply hne
      have := congrArg (fun x => u * x) h1
      simpa using this.symm
  · intro hmem
    refine ⟨?_, Or.inl (by simpa using (Finset.mem_of_mem_erase hmem))⟩
    intro huv
    subst huv
    exact Finset.ne_of_mem_erase hmem (inv_mul_cancel u)

/-- **Theorem 4.1 (ii)**, general form.  For an abelian group and a symmetric
`Δ`, the vector `θ̂` is an eigenvector of the adjacency matrix with eigenvalue
`∑_{g ∈ Δ, g ≠ 1} θ(g)`; the neutral element plays no role since the Cayley
graph has no loops. -/
theorem cayley_charVec_eigen_general {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {Δ : Finset G} (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ) (θ : G →* ℂˣ) :
    adj (𝕜 := ℂ) (cayleyGraph (Δ : Set G)) *ᵥ charVec θ
      = (∑ g ∈ Δ.erase 1, ((θ g : ℂˣ) : ℂ)) • charVec θ := by
  funext h
  have key : ∀ g : G, adj (𝕜 := ℂ) (cayleyGraph (Δ : Set G)) h g * charVec θ g
      = if h⁻¹ * g ∈ Δ.erase 1 then charVec θ g else 0 := by
    intro g
    by_cases hg : h⁻¹ * g ∈ Δ.erase 1
    · rw [adj_apply, if_pos ((cayley_adj_finset_erase hsym h g).mpr hg), if_pos hg, one_mul]
    · rw [adj_apply, if_neg (fun hc => hg ((cayley_adj_finset_erase hsym h g).mp hc)),
        if_neg hg, zero_mul]
  have reindex : ∀ f : G → ℂ, (∑ g, f g) = ∑ k, f (h * k) := by
    intro f
    exact (Equiv.sum_comp (Equiv.mulLeft h) f).symm
  have hstep : ∀ k : G, h⁻¹ * (h * k) = k := fun k => by group
  have hchr : ∀ k : G,
      charVec θ (h * k) = ((θ k⁻¹ : ℂˣ) : ℂ) * ((θ h⁻¹ : ℂˣ) : ℂ) := by
    intro k
    simp only [charVec]
    rw [_root_.mul_inv_rev, map_mul, Units.val_mul]
  have hfilter : ∀ f : G → ℂ,
      (∑ k, (if k ∈ Δ.erase 1 then f k else 0)) = ∑ k ∈ Δ.erase 1, f k := by
    intro f
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have hsym' : ∀ k ∈ Δ.erase 1, k⁻¹ ∈ Δ.erase 1 := by
    intro k hk
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hk
    exact Finset.mem_erase.mpr ⟨by simpa using hne, hsym k hmem⟩
  have hsum : (∑ k ∈ Δ.erase 1, ((θ k⁻¹ : ℂˣ) : ℂ))
      = ∑ k ∈ Δ.erase 1, ((θ k : ℂˣ) : ℂ) := by
    refine Finset.sum_bij' (fun k _ => k⁻¹) (fun k _ => k⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro a ha; exact hsym' a ha
    · intro a ha; exact hsym' a ha
    · intro a ha; simp
    · intro a ha; simp
    · intro a ha; simp
  rw [Pi.smul_apply, smul_eq_mul]
  calc (adj (𝕜 := ℂ) (cayleyGraph (Δ : Set G)) *ᵥ charVec θ) h
      = ∑ g, adj (𝕜 := ℂ) (cayleyGraph (Δ : Set G)) h g * charVec θ g := rfl
    _ = ∑ g, (if h⁻¹ * g ∈ Δ.erase 1 then charVec θ g else 0) :=
          Finset.sum_congr rfl fun g _ => key g
    _ = ∑ k, (if h⁻¹ * (h * k) ∈ Δ.erase 1 then charVec θ (h * k) else 0) :=
          reindex (fun g => if h⁻¹ * g ∈ Δ.erase 1 then charVec θ g else 0)
    _ = ∑ k, (if k ∈ Δ.erase 1 then charVec θ (h * k) else 0) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hstep k]
    _ = ∑ k ∈ Δ.erase 1, charVec θ (h * k) := hfilter _
    _ = ∑ k ∈ Δ.erase 1, ((θ k⁻¹ : ℂˣ) : ℂ) * ((θ h⁻¹ : ℂˣ) : ℂ) :=
          Finset.sum_congr rfl fun k _ => hchr k
    _ = (∑ k ∈ Δ.erase 1, ((θ k⁻¹ : ℂˣ) : ℂ)) * ((θ h⁻¹ : ℂˣ) : ℂ) :=
          (Finset.sum_mul (Δ.erase 1) (fun k => ((θ k⁻¹ : ℂˣ) : ℂ)) _).symm
    _ = (∑ k ∈ Δ.erase 1, ((θ k : ℂˣ) : ℂ)) * ((θ h⁻¹ : ℂˣ) : ℂ) := by rw [hsum]

/-- **Theorem 4.1 (ii).** For an abelian group and a symmetric `Δ` with `1 ∉ Δ`,
the vector `θ̂` is an eigenvector of the adjacency matrix with eigenvalue
`Δ_θ = ∑_{g ∈ Δ} θ(g)`.

The hypothesis `h1 : 1 ∉ Δ` is needed as stated (see
`cayley_charVec_eigen_false_without_h1`); with it, this is
`cayley_charVec_eigen_general` plus `Δ.erase 1 = Δ`. -/
theorem cayley_charVec_eigen {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G]
    {Δ : Finset G} (h1 : (1 : G) ∉ Δ) (hsym : ∀ g ∈ Δ, g⁻¹ ∈ Δ) (θ : G →* ℂˣ) :
    adj (𝕜 := ℂ) (cayleyGraph (Δ : Set G)) *ᵥ charVec θ
      = (∑ g ∈ Δ, ((θ g : ℂˣ) : ℂ)) • charVec θ := by
  rw [cayley_charVec_eigen_general hsym θ, Finset.erase_eq_of_notMem h1]

/-- The hypothesis `1 ∉ Δ` in `cayley_charVec_eigen` cannot be dropped: the
Finset `Δ = {1}` satisfies `Δ = Δ⁻¹`, yet the conclusion fails for every
character, because `{1}` spans no edges of the Cayley graph (there are no loops)
while it contributes `θ 1 = 1` to the claimed eigenvalue. -/
theorem cayley_charVec_eigen_false_without_h1 {G : Type*} [CommGroup G] [Fintype G]
    [DecidableEq G] (θ : G →* ℂˣ) :
    adj (𝕜 := ℂ) (cayleyGraph ({(1 : G)} : Set G)) *ᵥ charVec θ
      ≠ (∑ g ∈ ({(1 : G)} : Finset G), ((θ g : ℂˣ) : ℂ)) • charVec θ := by
  intro hcon
  have hgraph : adj (𝕜 := ℂ) (cayleyGraph ({(1 : G)} : Set G)) = 0 := by
    ext u v
    rw [adj_apply]
    have hnot : ¬ (cayleyGraph ({(1 : G)} : Set G)).Adj u v := by
      intro hadj
      obtain ⟨hne, hmem | hmem⟩ :=
        (SimpleGraph.mulCayley_adj ({(1 : G)} : Set G) u v).mp hadj
      · have huv : u⁻¹ * v = 1 := by simpa using hmem
        have hvu : v = u := by
          have := congrArg (fun x => u * x) huv
          simpa using this
        exact hne hvu.symm
      · have hvu : v⁻¹ * u = 1 := by simpa using hmem
        have huv : u = v := by
          have := congrArg (fun x => v * x) hvu
          simpa using this
        exact hne huv
    rw [if_neg hnot]
    simp
  rw [hgraph, zero_mulVec] at hcon
  have hone : (∑ g ∈ ({(1 : G)} : Finset G), ((θ g : ℂˣ) : ℂ)) = 1 := by simp
  rw [hone, one_smul] at hcon
  have h2 := congrFun hcon 1
  simp [charVec] at h2

end Terwilliger
