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
# The Hamming and Johnson graphs, and the thin condition (Chapters 5–8)

* `Terwilliger.hammingGraph D` is the `D`-cube `H(D,2)` on `Fin D → Bool`.
* `Terwilliger.johnsonGraph D N` is the Johnson graph `J(D,N)` on the `D`-element
  subsets of `Fin N`.
* `Terwilliger.IsThinAt`, `IsCommutativeSubconstituent`, `IsSymmetricSubconstituent`,
  `HasPropertyG` are the four conditions (TH), (C), (S), (G) of Theorem 7.4.

The substance of this file is Theorem 7.4:

  `(TH) ⇔ (C) ⇐ (S) ⇐ (G)`

and the implication `(S) ⇒ (C)` is proved: if every element of `E*_iTE*_i` is
self-adjoint then `E*_iTE*_i` is commutative, because
`ab = (ab)* = b*a* = ba`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The Hamming graph `H(D,2)` -/

/-- The `D`-cube `H(D,2)`: vertices are the `0`-`1` strings of length `D`, and two
strings are adjacent when they differ in exactly one coordinate. -/
def hammingGraph (D : ℕ) : SimpleGraph (Fin D → Bool) :=
  SimpleGraph.fromRel fun u v => ∃ i, u i ≠ v i ∧ ∀ j, j ≠ i → u j = v j

/-- The Hamming distance on `H(D,2)`: the number of coordinates in which the two
strings differ. -/
def hammingDist {D : ℕ} (u v : Fin D → Bool) : ℕ := (Finset.univ.filter fun i => u i ≠ v i).card

/-! ### Auxiliary facts: `hammingDist` and the adjacency relation of `H(D,2)` -/

/-- The set of coordinates in which two binary strings differ. -/
def hammingDiff {D : ℕ} (u v : Fin D → Bool) : Finset (Fin D) :=
  Finset.univ.filter fun i => u i ≠ v i

theorem mem_hammingDiff {D : ℕ} {u v : Fin D → Bool} {i : Fin D} :
    i ∈ hammingDiff u v ↔ u i ≠ v i := by
  simp [hammingDiff]

theorem hammingDist_eq_card_hammingDiff {D : ℕ} (u v : Fin D → Bool) :
    hammingDist u v = (hammingDiff u v).card := rfl

theorem eq_of_hammingDiff_eq_empty {D : ℕ} {u v : Fin D → Bool} (h : hammingDiff u v = ∅) :
    u = v := by
  funext i
  by_contra hne
  have h1 : i ∈ hammingDiff u v := mem_hammingDiff.2 hne
  rw [h] at h1
  exact absurd h1 (Finset.notMem_empty i)

theorem hammingDist_self {D : ℕ} (u : Fin D → Bool) : hammingDist u u = 0 := by
  simp [hammingDist]

/-- Two strings are adjacent in `H(D,2)` exactly when they differ in precisely one
coordinate. -/
theorem hammingGraph_adj_iff {D : ℕ} {u v : Fin D → Bool} :
    (hammingGraph D).Adj u v ↔ ∃ i, u i ≠ v i ∧ ∀ j, j ≠ i → u j = v j := by
  simp only [hammingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, ⟨i, hi, hag⟩ | ⟨i, hi, hag⟩⟩
    · exact ⟨i, hi, hag⟩
    · exact ⟨i, fun hc => hi hc.symm, fun j hj => (hag j hj).symm⟩
  · rintro ⟨i, hi, hag⟩
    refine ⟨?_, Or.inl ⟨i, hi, hag⟩⟩
    rintro rfl
    exact hi rfl

/-- The set of coordinates on which `u` and `w` differ is contained in the union of
the (single) coordinate on which `w` and `w'` differ with the difference set of
`u` and `w'`. -/
theorem hammingDiff_subset_insert {D : ℕ} {u w w' : Fin D → Bool} {i : Fin D}
    (h : ∀ j, j ≠ i → w j = w' j) :
    hammingDiff u w ⊆ insert i (hammingDiff u w') := by
  intro z hz
  have hz' : u z ≠ w z := mem_hammingDiff.1 hz
  by_cases hzi : z = i
  · simp [hzi]
  · rw [Finset.mem_insert]
    right
    exact mem_hammingDiff.2 (by rw [h z hzi] at hz'; exact hz')

/-- Adjacent vertices have Hamming distance differing by at most one. -/
theorem hammingDist_le_succ_of_adj {D : ℕ} {u w w' : Fin D → Bool}
    (h : (hammingGraph D).Adj w w') :
    hammingDist u w ≤ hammingDist u w' + 1 := by
  obtain ⟨i, -, hag⟩ := hammingGraph_adj_iff.1 h
  calc hammingDist u w = (hammingDiff u w).card := hammingDist_eq_card_hammingDiff u w
    _ ≤ (insert i (hammingDiff u w')).card := Finset.card_le_card (hammingDiff_subset_insert hag)
    _ ≤ (hammingDiff u w').card + 1 := Finset.card_insert_le i (hammingDiff u w')
    _ = hammingDist u w' + 1 := by rw [hammingDist_eq_card_hammingDiff]

/-- Along a walk of length `n` starting at `a`, the Hamming distance to a fixed
string `z` changes by at most `n`. -/
theorem hammingDist_le_length_add {D : ℕ} (z : Fin D → Bool) {a b : Fin D → Bool}
    (p : (hammingGraph D).Walk a b) :
    hammingDist z b ≤ hammingDist z a + p.length := by
  induction p with
  | nil => simp
  | cons h q ih =>
      have hstep : hammingDist z _ ≤ hammingDist z _ + 1 :=
        hammingDist_le_succ_of_adj (u := z) h.symm
      rw [SimpleGraph.Walk.length_cons]
      omega

/-- If `s` is exactly the set of coordinates on which `u` and `v` differ, then there
is a walk in `H(D,2)` from `u` to `v` whose length is `s.card`: flip the differing
coordinates one at a time. -/
theorem exists_hammingGraph_walk {D : ℕ} :
    ∀ (s : Finset (Fin D)) (u v : Fin D → Bool), (∀ j, j ∈ s ↔ u j ≠ v j) →
      ∃ p : (hammingGraph D).Walk u v, p.length = s.card := by
  intro s
  induction s using Finset.induction with
  | empty =>
      intro u v h
      have huv : u = v := by
        funext j
        by_contra hne
        have h1 : j ∈ (∅ : Finset (Fin D)) := (h j).2 hne
        exact absurd h1 (Finset.notMem_empty j)
      rw [huv]
      exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | insert a t ha ih =>
      intro u v h
      have hau : u a ≠ v a := (h a).1 (Finset.mem_insert_self a t)
      have hsub : ∀ j, j ∈ t ↔ (Function.update u a (v a)) j ≠ v j := by
        intro j
        by_cases hja : j = a
        · subst hja
          simp [ha]
        · rw [Function.update_of_ne hja]
          have hmem : j ∈ insert a t ↔ j ∈ t := by
            rw [Finset.mem_insert]
            simp [hja]
          exact hmem.symm.trans (h j)
      obtain ⟨p, hp⟩ := ih (Function.update u a (v a)) v hsub
      refine ⟨SimpleGraph.Walk.cons ?_ p, ?_⟩
      · rw [hammingGraph_adj_iff]
        exact ⟨a, by simpa [Function.update_self] using hau,
          fun j hj => by simp [Function.update_of_ne hj]⟩
      · rw [SimpleGraph.Walk.length_cons, hp, Finset.card_insert_of_notMem ha]

/-- **Chapter 5.**  The Hamming distance is the graph distance of `H(D,2)`. -/
theorem hammingGraph_dist {D : ℕ} (u v : Fin D → Bool) :
    (hammingGraph D).dist u v = hammingDist u v := by
  obtain ⟨p₀, hp₀⟩ := exists_hammingGraph_walk (hammingDiff u v) u v
    (fun j => mem_hammingDiff)
  have hr : (hammingGraph D).Reachable u v := ⟨p₀⟩
  obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
  refine le_antisymm ?_ ?_
  · calc (hammingGraph D).dist u v ≤ p₀.length := SimpleGraph.dist_le p₀
      _ = hammingDist u v := hp₀
  · have hle : hammingDist u v ≤ hammingDist u u + p.length := hammingDist_le_length_add u p
    rw [hammingDist_self, hp, Nat.zero_add] at hle
    exact hle

/-- The Hamming distance is symmetric. -/
theorem hammingDist_comm {D : ℕ} (u v : Fin D → Bool) : hammingDist u v = hammingDist v u := by
  have h : hammingDiff u v = hammingDiff v u := by
    ext i
    simp only [mem_hammingDiff, ne_comm]
  rw [hammingDist_eq_card_hammingDiff, hammingDist_eq_card_hammingDiff, h]

/-- The Hamming distance vanishes exactly on equal strings. -/
theorem hammingDist_eq_zero_iff {D : ℕ} {u v : Fin D → Bool} :
    hammingDist u v = 0 ↔ u = v := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [hammingDist_eq_card_hammingDiff] at h
    exact eq_of_hammingDiff_eq_empty (Finset.card_eq_zero.1 h)
  · rintro rfl
    exact hammingDist_self u

/-- The triangle inequality for the Hamming distance. -/
theorem hammingDist_triangle {D : ℕ} (u v w : Fin D → Bool) :
    hammingDist u w ≤ hammingDist u v + hammingDist v w := by
  have hsub : hammingDiff u w ⊆ hammingDiff u v ∪ hammingDiff v w := by
    intro j hj
    have hjuw : u j ≠ w j := mem_hammingDiff.1 hj
    rw [Finset.mem_union]
    by_cases huv : u j = v j
    · right
      exact mem_hammingDiff.2 (by rw [← huv]; exact hjuw)
    · left
      exact mem_hammingDiff.2 huv
  calc hammingDist u w = (hammingDiff u w).card := hammingDist_eq_card_hammingDiff u w
    _ ≤ (hammingDiff u v ∪ hammingDiff v w).card := Finset.card_le_card hsub
    _ ≤ (hammingDiff u v).card + (hammingDiff v w).card := Finset.card_union_le _ _
    _ = hammingDist u v + hammingDist v w := by
        rw [hammingDist_eq_card_hammingDiff u v, hammingDist_eq_card_hammingDiff v w]

/-- `H(D,2)` is preconnected: any two strings are joined by a walk. -/
theorem hammingGraph_preconnected (D : ℕ) : (hammingGraph D).Preconnected := by
  intro u v
  obtain ⟨p, -⟩ := exists_hammingGraph_walk (hammingDiff u v) u v (fun j => mem_hammingDiff)
  exact ⟨p⟩

/-- `H(D,2)` is connected. -/
theorem hammingGraph_connected (D : ℕ) : (hammingGraph D).Connected where
  preconnected := hammingGraph_preconnected D
  nonempty := ⟨fun _ => false⟩

/-- Two strings are adjacent in `H(D,2)` exactly when their Hamming distance is `1`. -/
theorem adj_iff_hammingDist_eq_one {D : ℕ} {u v : Fin D → Bool} :
    (hammingGraph D).Adj u v ↔ hammingDist u v = 1 := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨i, hi, hag⟩ := hammingGraph_adj_iff.1 h
    have hsingle : hammingDiff u v = {i} := by
      ext j
      rw [mem_hammingDiff, Finset.mem_singleton]
      refine ⟨?_, ?_⟩
      · intro hj
        by_contra hji
        exact hj (hag j hji)
      · rintro rfl
        exact hi
    rw [hammingDist_eq_card_hammingDiff, hsingle]
    simp
  · intro h
    obtain ⟨i, hi⟩ := Finset.card_eq_one.1 (show (hammingDiff u v).card = 1 by
      rw [← hammingDist_eq_card_hammingDiff]; exact h)
    refine hammingGraph_adj_iff.2 ⟨i, ?_, ?_⟩
    · rw [← mem_hammingDiff, hi]
      simp
    · intro j hj
      by_contra hne
      have hjd : j ∈ hammingDiff u v := mem_hammingDiff.2 hne
      rw [hi, Finset.mem_singleton] at hjd
      exact hj hjd

namespace HD2

variable {D : ℕ}

/-! ## Flipping a coordinate of a binary string -/

/-- Flip the `i`-th coordinate. -/
def flipAt (u : Fin D → Bool) (i : Fin D) : Fin D → Bool := Function.update u i (!u i)

@[simp]
theorem flipAt_same (u : Fin D → Bool) (i : Fin D) : flipAt u i i = !(u i) := by
  simp [flipAt]

theorem flipAt_of_ne {u : Fin D → Bool} {i j : Fin D} (h : j ≠ i) : flipAt u i j = u j := by
  simp [flipAt, Function.update_of_ne h]

theorem bool_not_ne_self (b : Bool) : (!b) ≠ b := by
  cases b <;> simp

theorem bool_ne_not_self (b : Bool) : b ≠ (!b) := fun h => bool_not_ne_self b h.symm

theorem eq_not_of_ne {a b : Bool} (h : a ≠ b) : b = !a := by
  cases a <;> cases b <;> simp_all

theorem flipAt_involutive (u : Fin D → Bool) (i : Fin D) : flipAt (flipAt u i) i = u := by
  funext j
  by_cases hj : j = i
  · subst hj
    rw [flipAt_same, flipAt_same, Bool.not_not]
  · rw [flipAt_of_ne hj, flipAt_of_ne hj]

theorem flipAt_comm (u : Fin D → Bool) {i j : Fin D} (h : i ≠ j) :
    flipAt (flipAt u i) j = flipAt (flipAt u j) i := by
  have h1 : Function.update u i (!u i) j = u j := Function.update_of_ne (Ne.symm h) _ _
  have h2 : Function.update u j (!u j) i = u i := Function.update_of_ne h _ _
  simp only [flipAt, h1, h2]
  exact Function.update_comm h _ _ _

theorem flipAt_ne (u : Fin D → Bool) (i : Fin D) : flipAt u i ≠ u := by
  intro h
  have h1 : flipAt u i i = u i := by rw [h]
  rw [flipAt_same] at h1
  exact bool_not_ne_self (u i) h1

theorem flipAt_inj {u : Fin D → Bool} {i j : Fin D} (h : flipAt u i = flipAt u j) : i = j := by
  by_contra hij
  have h1 : flipAt u i j = u j := flipAt_of_ne (Ne.symm hij)
  have h2 : flipAt u j j = !(u j) := flipAt_same u j
  rw [h, h2] at h1
  exact bool_not_ne_self (u j) h1

/-! ## The up- and down-sets of a vertex -/

/-- Coordinates on which `u` agrees with the base point `x`: the ones that can be
raised. -/
def upSet (x u : Fin D → Bool) : Finset (Fin D) := Finset.univ.filter fun i => u i = x i

/-- Coordinates on which `u` differs from the base point `x`: the ones that can be
lowered. -/
def dnSet (x u : Fin D → Bool) : Finset (Fin D) := hammingDiff u x

@[simp]
theorem mem_upSet {x u : Fin D → Bool} {i : Fin D} : i ∈ upSet x u ↔ u i = x i := by
  simp [upSet]

theorem mem_dnSet {x u : Fin D → Bool} {i : Fin D} : i ∈ dnSet x u ↔ u i ≠ x i :=
  mem_hammingDiff

/-- The level of `u` (its distance from the base point) is the size of the down-set. -/
theorem card_dnSet (x u : Fin D → Bool) : (dnSet x u).card = hammingDist x u := by
  rw [hammingDist_comm, hammingDist_eq_card_hammingDiff]
  rfl

theorem disjoint_upSet_dnSet (x u : Fin D → Bool) : Disjoint (upSet x u) (dnSet x u) := by
  refine Finset.disjoint_left.2 ?_
  intro i hi hi'
  rw [mem_upSet] at hi
  rw [mem_dnSet] at hi'
  exact hi' hi

theorem upSet_union_dnSet (x u : Fin D → Bool) : upSet x u ∪ dnSet x u = Finset.univ := by
  ext i
  rw [Finset.mem_union, mem_upSet, mem_dnSet]
  by_cases hu : u i <;> by_cases hx : x i <;> simp_all

theorem card_upSet_add_card_dnSet (x u : Fin D → Bool) :
    (upSet x u).card + (dnSet x u).card = D := by
  have h := Finset.card_union_of_disjoint (disjoint_upSet_dnSet x u)
  rw [upSet_union_dnSet, Finset.card_univ, Fintype.card_fin] at h
  omega

theorem hammingDist_le_card (x u : Fin D → Bool) : hammingDist x u ≤ D := by
  have h := card_upSet_add_card_dnSet x u
  have h2 := card_dnSet x u
  omega

theorem upSet_flip_dnSet {x u : Fin D → Bool} {i : Fin D} (h : i ∈ dnSet x u) :
    upSet x (flipAt u i) = insert i (upSet x u) := by
  have hx : u i ≠ x i := mem_dnSet.1 h
  ext k
  simp only [mem_upSet, Finset.mem_insert]
  by_cases hk : k = i
  · subst hk
    rw [flipAt_same]
    cases hu : u k <;> cases hxx : x k <;> simp_all
  · rw [flipAt_of_ne hk]
    cases hu : u k <;> cases hxx : x k <;> simp_all

theorem dnSet_flip_upSet {x u : Fin D → Bool} {i : Fin D} (h : i ∈ upSet x u) :
    dnSet x (flipAt u i) = insert i (dnSet x u) := by
  have hx : u i = x i := mem_upSet.1 h
  ext k
  simp only [mem_dnSet, Finset.mem_insert]
  by_cases hk : k = i
  · subst hk
    rw [flipAt_same]
    cases hu : u k <;> cases hxx : x k <;> simp_all
  · rw [flipAt_of_ne hk]
    cases hu : u k <;> cases hxx : x k <;> simp_all

theorem dnSet_flip_dnSet {x u : Fin D → Bool} {i : Fin D} (h : i ∈ dnSet x u) :
    dnSet x (flipAt u i) = (dnSet x u).erase i := by
  have hx : u i ≠ x i := mem_dnSet.1 h
  ext k
  simp only [mem_dnSet, Finset.mem_erase]
  by_cases hk : k = i
  · subst hk
    rw [flipAt_same]
    cases hu : u k <;> cases hxx : x k <;> simp_all
  · rw [flipAt_of_ne hk]
    cases hu : u k <;> cases hxx : x k <;> simp_all

theorem upSet_flip_upSet {x u : Fin D → Bool} {i : Fin D} (h : i ∈ upSet x u) :
    upSet x (flipAt u i) = (upSet x u).erase i := by
  have hx : u i = x i := mem_upSet.1 h
  ext k
  simp only [mem_upSet, Finset.mem_erase]
  by_cases hk : k = i
  · subst hk
    rw [flipAt_same]
    cases hu : u k <;> cases hxx : x k <;> simp_all
  · rw [flipAt_of_ne hk]
    cases hu : u k <;> by_cases hxx : x k <;> simp_all

theorem hammingDist_flip_up {x u : Fin D → Bool} {i : Fin D} (h : i ∈ upSet x u) :
    hammingDist x (flipAt u i) = hammingDist x u + 1 := by
  have hx : u i = x i := mem_upSet.1 h
  have hnot : i ∉ dnSet x u := by
    rw [mem_dnSet]; exact fun hc => hc hx
  rw [← card_dnSet x (flipAt u i), dnSet_flip_upSet h,
    Finset.card_insert_of_notMem hnot, card_dnSet]

theorem hammingDist_flip_dn {x u : Fin D → Bool} {i : Fin D} (h : i ∈ dnSet x u) :
    hammingDist x (flipAt u i) = hammingDist x u - 1 := by
  rw [← card_dnSet x (flipAt u i), dnSet_flip_dnSet h, Finset.card_erase_of_mem h, card_dnSet]

/-! ## Adjacency in the cube -/

theorem adj_iff_flipAt {u v : Fin D → Bool} :
    (hammingGraph D).Adj u v ↔ ∃ i, v = flipAt u i := by
  rw [hammingGraph_adj_iff]
  constructor
  · rintro ⟨i, hi, hag⟩
    refine ⟨i, ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      rw [flipAt_same, eq_not_of_ne hi]
    · rw [flipAt_of_ne hj]
      exact (hag j hj).symm
  · rintro ⟨i, rfl⟩
    refine ⟨i, ?_, ?_⟩
    · rw [flipAt_same]
      exact bool_ne_not_self (u i)
    · intro j hj
      rw [flipAt_of_ne hj]

theorem adj_flipAt (u : Fin D → Bool) (i : Fin D) : (hammingGraph D).Adj u (flipAt u i) :=
  adj_iff_flipAt.2 ⟨i, rfl⟩

/-- Neighbours of a vertex are obtained by flipping one coordinate, and the
coordinate is unique. -/
theorem existsUnique_flipAt_of_adj {u v : Fin D → Bool} (h : (hammingGraph D).Adj u v) :
    ∃! i : Fin D, v = flipAt u i := by
  obtain ⟨i, hi⟩ := adj_iff_flipAt.1 h
  exact ⟨i, hi, fun j hj => flipAt_inj (hj.symm.trans hi)⟩

theorem dist_flip_up {x u : Fin D → Bool} {i : Fin D} (h : i ∈ upSet x u) :
    (hammingGraph D).dist x (flipAt u i) = hammingDist x u + 1 := by
  rw [hammingGraph_dist, hammingDist_flip_up h]

theorem dist_flip_dn {x u : Fin D → Bool} {i : Fin D} (h : i ∈ dnSet x u) :
    (hammingGraph D).dist x (flipAt u i) = hammingDist x u - 1 := by
  rw [hammingGraph_dist, hammingDist_flip_dn h]

/-- Adjacent vertices are at levels differing by exactly one. -/
theorem hammingDist_adj {x u v : Fin D → Bool} (h : (hammingGraph D).Adj u v) :
    hammingDist x v = hammingDist x u + 1 ∨ hammingDist x u = hammingDist x v + 1 := by
  obtain ⟨i, rfl⟩ := adj_iff_flipAt.1 h
  by_cases hi : i ∈ upSet x u
  · left; rw [hammingDist_flip_up hi]
  · right
    have hd : i ∈ dnSet x u := by
      rw [mem_dnSet]; rw [mem_upSet] at hi; simpa using hi
    rw [hammingDist_flip_dn hd]
    have : 1 ≤ hammingDist x u := by
      rw [← card_dnSet x u]
      exact Finset.card_pos.2 ⟨i, hd⟩
    omega

/-! ## The raising, lowering and level operators of the cube -/

/-- The raising matrix `R = ∑ᵢ E*_{i+1} A E*ᵢ` of `H(D,2)` with base point `x`. -/
def hdR (D : ℕ) (x : Fin D → Bool) : Matrix (Fin D → Bool) (Fin D → Bool) ℂ :=
  ∑ i ∈ Finset.range D, subconst (𝕜 := ℂ) (hammingGraph D) x (i + 1)
    * adj (𝕜 := ℂ) (hammingGraph D) * subconst (𝕜 := ℂ) (hammingGraph D) x i

/-- The lowering matrix `L = ∑ᵢ E*_{i-1} A E*ᵢ` of `H(D,2)` with base point `x`. -/
def hdL (D : ℕ) (x : Fin D → Bool) : Matrix (Fin D → Bool) (Fin D → Bool) ℂ :=
  ∑ i ∈ Finset.Icc 1 D, subconst (𝕜 := ℂ) (hammingGraph D) x (i - 1)
    * adj (𝕜 := ℂ) (hammingGraph D) * subconst (𝕜 := ℂ) (hammingGraph D) x i

/-- The "dual" operator `A* = ∑ᵢ (D - 2i) Eᵢ*` of `H(D,2)` with base point `x`. -/
def hdAst (D : ℕ) (x : Fin D → Bool) : Matrix (Fin D → Bool) (Fin D → Bool) ℂ :=
  ∑ i ∈ Finset.range (D + 1), ((D : ℂ) - 2 * (i : ℂ))
    • subconst (𝕜 := ℂ) (hammingGraph D) x i

/-! ## The cube as a level system -/

theorem hdR_mem (D : ℕ) (x : Fin D → Bool) :
    hdR D x ∈ subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x := by
  rw [hdR]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  exact mul_mem (mul_mem (subconst_mem_subconstituentAlgebra _ x _)
    (adj_mem_subconstituentAlgebra _ x)) (subconst_mem_subconstituentAlgebra _ x _)

theorem hdL_mem (D : ℕ) (x : Fin D → Bool) :
    hdL D x ∈ subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x := by
  rw [hdL]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  exact mul_mem (mul_mem (subconst_mem_subconstituentAlgebra _ x _)
    (adj_mem_subconstituentAlgebra _ x)) (subconst_mem_subconstituentAlgebra _ x _)

theorem hdAst_mem (D : ℕ) (x : Fin D → Bool) :
    hdAst D x ∈ subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x := by
  rw [hdAst]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  exact Subalgebra.smul_mem _ (subconst_mem_subconstituentAlgebra _ x _) _

/-! ### Vector formulas -/

/-- A sum over the neighbours of `u` is a sum over the coordinates of `u`. -/
theorem sum_adj_eq_sum_flipAt (u : Fin D → Bool) (g : (Fin D → Bool) → ℂ) :
    ∑ v, (if (hammingGraph D).Adj u v then (1 : ℂ) else 0) * g v = ∑ k : Fin D, g (flipAt u k) := by
  have himg : (Finset.univ.filter fun v => (hammingGraph D).Adj u v)
      = Finset.univ.image (flipAt u) := by
    ext v
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, h⟩
      obtain ⟨i, rfl⟩ := adj_iff_flipAt.1 h
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · rintro ⟨k, -, rfl⟩
      exact ⟨Finset.mem_univ _, adj_flipAt u k⟩
  have h1 : ∀ v : Fin D → Bool,
      (if (hammingGraph D).Adj u v then (1 : ℂ) else 0) * g v
        = (if (hammingGraph D).Adj u v then g v else 0) := by
    intro v
    by_cases h : (hammingGraph D).Adj u v <;> simp [h]
  rw [Finset.sum_congr rfl fun v _ => h1 v]
  rw [← Finset.sum_filter, himg]
  exact Finset.sum_image (fun a _ b _ h => flipAt_inj h)

theorem subconst_mulVec_apply (x : Fin D → Bool) (i : ℕ) (f : (Fin D → Bool) → ℂ)
    (u : Fin D → Bool) :
    (subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ f) u
      = (if (hammingGraph D).dist x u = i then 1 else 0) * f u := by
  simp only [Matrix.mulVec, dotProduct]
  simp only [subconst_apply]
  rw [Finset.sum_eq_single u]
  · rw [if_pos rfl]
  · intro b _ hb
    rw [if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ u) h

/-- The action of a block `E*_j A E*_i` on a vector. -/
theorem block_mulVec_apply (x : Fin D → Bool) (i j : ℕ) (f : (Fin D → Bool) → ℂ)
    (u : Fin D → Bool) :
    ((subconst (𝕜 := ℂ) (hammingGraph D) x j * adj (𝕜 := ℂ) (hammingGraph D)
        * subconst (𝕜 := ℂ) (hammingGraph D) x i) *ᵥ f) u
      = (if (hammingGraph D).dist x u = j then 1 else 0)
        * ∑ k : Fin D, (if (hammingGraph D).dist x (flipAt u k) = i then 1 else 0)
            * f (flipAt u k) := by
  conv_lhs => rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [subconst_mulVec_apply]
  congr 1
  rw [Matrix.mulVec, dotProduct]
  simp only [adj_apply, subconst_mulVec_apply]
  rw [sum_adj_eq_sum_flipAt]

/-- The level-`i` part of the down-set sum, as a sum over `k ∈ dnSet x u`. -/
theorem sum_flip_level_eq (x u : Fin D → Bool) {i : ℕ}
    (hi : i = hammingDist x u - 1) (f : (Fin D → Bool) → ℂ) :
    ∑ k : Fin D, (if hammingDist x (flipAt u k) = i then 1 else 0) * f (flipAt u k)
      = ∑ k ∈ dnSet x u, f (flipAt u k) := by
  have hfil : (Finset.univ.filter fun k => hammingDist x (flipAt u k) = i) = dnSet x u := by
    refine Finset.filter_congr ?_
    intro k _
    rw [hi]
    by_cases hk : u k = x k
    · rw [hammingDist_flip_up (mem_upSet.2 hk)]
      constructor
      · intro hc; omega
      · intro hc; exact absurd hk hc
    · rw [hammingDist_flip_dn (mem_dnSet.2 hk)]
      exact ⟨fun _ => hk, fun _ => rfl⟩
  have h1 : ∀ k : Fin D,
      (if hammingDist x (flipAt u k) = i then (1 : ℂ) else 0) * f (flipAt u k)
        = (if hammingDist x (flipAt u k) = i then f (flipAt u k) else 0) := by
    intro k
    by_cases h : hammingDist x (flipAt u k) = i <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_filter, hfil]

/-- The level-`i` part in the raising direction. -/
theorem sum_flip_level_eq_up (x u : Fin D → Bool) (i : ℕ)
    (hi : i = hammingDist x u + 1) (f : (Fin D → Bool) → ℂ) :
    ∑ k : Fin D, (if hammingDist x (flipAt u k) = i then 1 else 0) * f (flipAt u k)
      = ∑ k ∈ upSet x u, f (flipAt u k) := by
  have hfil : (Finset.univ.filter fun k => hammingDist x (flipAt u k) = i) = upSet x u := by
    refine Finset.filter_congr ?_
    intro k _
    rw [hi]
    by_cases hk : u k = x k
    · rw [hammingDist_flip_up (mem_upSet.2 hk)]
      exact ⟨fun _ => hk, fun _ => rfl⟩
    · rw [hammingDist_flip_dn (mem_dnSet.2 hk)]
      have hlt : hammingDist x u - 1 < hammingDist x u + 1 := by omega
      exact ⟨fun hc => absurd hc hlt.ne, fun hc => absurd hc hk⟩
  have h1 : ∀ k : Fin D,
      (if hammingDist x (flipAt u k) = i then (1 : ℂ) else 0) * f (flipAt u k)
        = (if hammingDist x (flipAt u k) = i then f (flipAt u k) else 0) := by
    intro k
    by_cases h : hammingDist x (flipAt u k) = i <;> simp [h]
  rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_filter, hfil]

theorem hdR_mulVec (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) (u : Fin D → Bool) :
    (hdR D x *ᵥ f) u = ∑ k ∈ dnSet x u, f (flipAt u k) := by
  have hdist : ∀ v : Fin D → Bool, (hammingGraph D).dist x v = hammingDist x v :=
    fun v => hammingGraph_dist x v
  have hAle : hammingDist x u ≤ D := hammingDist_le_card x u
  rw [hdR, Matrix.sum_mulVec, Finset.sum_apply]
  simp only [block_mulVec_apply, hdist]
  by_cases hA : hammingDist x u = 0
  · have hempty : dnSet x u = ∅ := by
      rw [← Finset.card_eq_zero, card_dnSet]
      exact hA
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [if_neg (by omega), zero_mul]
  · have hApos : 1 ≤ hammingDist x u := Nat.pos_of_ne_zero hA
    rw [Finset.sum_eq_single (hammingDist x u - 1)]
    · rw [Nat.sub_add_cancel hApos, if_pos rfl, one_mul]
      exact sum_flip_level_eq x u rfl f
    · intro b _ hb
      rw [if_neg (by omega), zero_mul]
    · intro hb
      exact absurd (Finset.mem_range.2 (by omega)) hb

theorem hdL_mulVec (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) (u : Fin D → Bool) :
    (hdL D x *ᵥ f) u = ∑ k ∈ upSet x u, f (flipAt u k) := by
  have hdist : ∀ v : Fin D → Bool, (hammingGraph D).dist x v = hammingDist x v :=
    fun v => hammingGraph_dist x v
  have hAle : hammingDist x u ≤ D := hammingDist_le_card x u
  rw [hdL, Matrix.sum_mulVec, Finset.sum_apply]
  simp only [block_mulVec_apply, hdist]
  by_cases hA : hammingDist x u = D
  · have hempty : upSet x u = ∅ := by
      rw [← Finset.card_eq_zero]
      have h := card_upSet_add_card_dnSet x u
      rw [card_dnSet, hA] at h
      omega
    rw [hempty, Finset.sum_empty]
    refine Finset.sum_eq_zero fun i hi => ?_
    obtain ⟨hi1, hi2⟩ := Finset.mem_Icc.1 hi
    rw [if_neg (by omega), zero_mul]
  · have hlt : hammingDist x u + 1 ≤ D := by omega
    rw [Finset.sum_eq_single (hammingDist x u + 1)]
    · rw [if_pos (by omega), one_mul]
      exact sum_flip_level_eq_up x u (hammingDist x u + 1) rfl f
    · intro b hb hne
      obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.1 hb
      rw [if_neg (by omega), zero_mul]
    · intro hb
      exact absurd (Finset.mem_Icc.2 ⟨by omega, hlt⟩) hb

theorem hdAst_mulVec (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) (u : Fin D → Bool) :
    (hdAst D x *ᵥ f) u = ((D : ℂ) - 2 * (hammingDist x u : ℂ)) * f u := by
  have hdist : ∀ v : Fin D → Bool, (hammingGraph D).dist x v = hammingDist x v :=
    fun v => hammingGraph_dist x v
  have hAle : hammingDist x u ≤ D := hammingDist_le_card x u
  rw [hdAst, Matrix.sum_mulVec, Finset.sum_apply]
  have hterm : ∀ i : ℕ, (((D : ℂ) - 2 * (i : ℂ))
      • subconst (𝕜 := ℂ) (hammingGraph D) x i) *ᵥ f
      = fun v => ((D : ℂ) - 2 * (i : ℂ))
          * ((if (hammingGraph D).dist x v = i then 1 else 0) * f v) := by
    intro i
    funext v
    rw [Matrix.smul_mulVec, Pi.smul_apply, subconst_mulVec_apply, smul_eq_mul]
  simp only [hterm, hdist]
  rw [Finset.sum_eq_single (hammingDist x u)]
  · rw [if_pos rfl, one_mul]
  · intro b _ hb
    rw [if_neg (fun h => hb h.symm), zero_mul, mul_zero]
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem adj_mulVec (D : ℕ) (f : (Fin D → Bool) → ℂ) (u : Fin D → Bool) :
    (adj (𝕜 := ℂ) (hammingGraph D) *ᵥ f) u = ∑ k : Fin D, f (flipAt u k) := by
  rw [Matrix.mulVec, dotProduct]
  simp only [adj_apply]
  rw [sum_adj_eq_sum_flipAt]

/-- `A = R + L` for the cube, as operators on vectors. -/
theorem adj_mulVec_eq (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) :
    adj (𝕜 := ℂ) (hammingGraph D) *ᵥ f = hdR D x *ᵥ f + hdL D x *ᵥ f := by
  funext u
  rw [Pi.add_apply, hdR_mulVec, hdL_mulVec, adj_mulVec D]
  have h1 : ∑ k ∈ upSet x u, f (flipAt u k)
      = ∑ k : Fin D, if u k = x k then f (flipAt u k) else 0 :=
    Finset.sum_filter (fun k => u k = x k) _
  have h2 : ∑ k ∈ dnSet x u, f (flipAt u k)
      = ∑ k : Fin D, if u k ≠ x k then f (flipAt u k) else 0 :=
    Finset.sum_filter (fun k => u k ≠ x k) _
  rw [h1, h2, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hk : u k = x k <;> simp [hk]

/-! ### The `sl₂` relations -/

theorem hdLR_sum_apply (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ)
    (u : Fin D → Bool) :
    (hdL D x *ᵥ (hdR D x *ᵥ f)) u
      = ∑ k ∈ upSet x u, (f u + ∑ j ∈ dnSet x u, f (flipAt (flipAt u k) j)) := by
  rw [hdL_mulVec]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkup : u k = x k := mem_upSet.1 hk
  have hknot : k ∉ dnSet x u := by
    rw [mem_dnSet]; exact fun hc => hc hkup
  rw [hdR_mulVec, dnSet_flip_upSet hk, Finset.sum_insert hknot, flipAt_involutive]

theorem hdRL_sum_apply (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ)
    (u : Fin D → Bool) :
    (hdR D x *ᵥ (hdL D x *ᵥ f)) u
      = ∑ k ∈ dnSet x u, (f u + ∑ j ∈ upSet x u, f (flipAt (flipAt u k) j)) := by
  rw [hdR_mulVec]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkdn : u k ≠ x k := mem_dnSet.1 hk
  have hknot : k ∉ upSet x u := by
    rw [mem_upSet]; exact hkdn
  rw [hdL_mulVec, upSet_flip_dnSet hk, Finset.sum_insert hknot, flipAt_involutive]

/-- `L R - R L = A*` on vectors. -/
theorem hdLR_sub_hdRL (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) :
    hdL D x *ᵥ (hdR D x *ᵥ f) - hdR D x *ᵥ (hdL D x *ᵥ f) = hdAst D x *ᵥ f := by
  have hdouble : ∀ u : Fin D → Bool,
      ∑ k ∈ upSet x u, ∑ j ∈ dnSet x u, f (flipAt (flipAt u k) j)
        = ∑ k ∈ dnSet x u, ∑ j ∈ upSet x u, f (flipAt (flipAt u k) j) := by
    intro u
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j hj => ?_
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := by
      rw [mem_upSet] at hk
      rw [mem_dnSet] at hj
      intro h
      exact hj (h ▸ hk)
    rw [flipAt_comm u hkj]
  funext u
  rw [Pi.sub_apply, hdAst_mulVec, hdLR_sum_apply, hdRL_sum_apply,
    Finset.sum_add_distrib, Finset.sum_add_distrib, hdouble u,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
  have hcard := card_upSet_add_card_dnSet x u
  have hlev : ((dnSet x u).card : ℂ) = (hammingDist x u : ℂ) := by
    exact_mod_cast card_dnSet x u
  have hc1 : ((upSet x u).card : ℂ) = (D : ℂ) - (hammingDist x u : ℂ) := by
    have h : ((upSet x u).card : ℂ) + ((dnSet x u).card : ℂ) = (D : ℂ) := by
      exact_mod_cast hcard
    rw [hlev] at h
    linear_combination h
  rw [hc1, hlev]
  ring

/-- `L R = A* + R L` as operators on vectors. -/
theorem hdLRapply (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) :
    hdL D x *ᵥ (hdR D x *ᵥ f) = hdAst D x *ᵥ f + hdR D x *ᵥ (hdL D x *ᵥ f) := by
  have h := hdLR_sub_hdRL D x f
  rw [sub_eq_iff_eq_add] at h
  exact h

/-- `A* L - L A* = 2 L` on vectors. -/
theorem hdAstL_sub (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) :
    hdAst D x *ᵥ (hdL D x *ᵥ f) - hdL D x *ᵥ (hdAst D x *ᵥ f)
      = (2 : ℂ) • (hdL D x *ᵥ f) := by
  funext u
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hdAst_mulVec, hdL_mulVec, hdL_mulVec]
  have hstep : ∀ k ∈ upSet x u,
      (hdAst D x *ᵥ f) (flipAt u k)
        = (((D : ℂ) - 2 * (hammingDist x u : ℂ)) - 2) * f (flipAt u k) := by
    intro k hk
    rw [hdAst_mulVec, hammingDist_flip_up hk]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  ring

/-- `A* R - R A* = -2 R` on vectors. -/
theorem hdAstR_sub (D : ℕ) (x : Fin D → Bool) (f : (Fin D → Bool) → ℂ) :
    hdAst D x *ᵥ (hdR D x *ᵥ f) - hdR D x *ᵥ (hdAst D x *ᵥ f)
      = -((2 : ℂ) • (hdR D x *ᵥ f)) := by
  funext u
  rw [Pi.sub_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul, hdAst_mulVec, hdR_mulVec,
    hdR_mulVec]
  have hpos : ∀ k ∈ dnSet x u, 1 ≤ hammingDist x u := by
    intro k hk
    rw [← card_dnSet x u]
    exact Finset.card_pos.2 ⟨k, hk⟩
  have hstep : ∀ k ∈ dnSet x u,
      (hdAst D x *ᵥ f) (flipAt u k)
        = (((D : ℂ) - 2 * (hammingDist x u : ℂ)) + 2) * f (flipAt u k) := by
    intro k hk
    rw [hdAst_mulVec, hammingDist_flip_dn hk, Nat.cast_sub (hpos k hk)]
    push_cast
    ring
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum]
  ring

/-! ### Support of a vector -/

/-- A vector is supported on the `i`-th sphere around `x`. -/
def SupportsAt (x : Fin D → Bool) (i : ℕ) (f : (Fin D → Bool) → ℂ) : Prop :=
  subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ f = f

theorem supportsAt_apply {x : Fin D → Bool} {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x i f) {u : Fin D → Bool} (hu : (hammingGraph D).dist x u ≠ i) : f u = 0 := by
  have h2 := congrFun h u
  rw [subconst_mulVec_apply, if_neg hu, zero_mul] at h2
  exact h2.symm

theorem supportsAt_of_forall {x : Fin D → Bool} {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : ∀ u, f u ≠ 0 → (hammingGraph D).dist x u = i) : SupportsAt x i f := by
  funext u
  rw [subconst_mulVec_apply]
  by_cases hu : (hammingGraph D).dist x u = i
  · rw [if_pos hu, one_mul]
  · rw [if_neg hu, zero_mul]
    have hz : f u = 0 := by
      by_contra hc
      exact hu (h u hc)
    rw [hz]

theorem SupportsAt.zero (x : Fin D → Bool) (i : ℕ) :
    SupportsAt x i (0 : (Fin D → Bool) → ℂ) := by
  rw [SupportsAt, mulVec_zero]

theorem SupportsAt.add {x : Fin D → Bool} {i : ℕ} {f g : (Fin D → Bool) → ℂ}
    (hf : SupportsAt x i f) (hg : SupportsAt x i g) : SupportsAt x i (f + g) := by
  rw [SupportsAt, mulVec_add, hf, hg]

theorem SupportsAt.smul {x : Fin D → Bool} {i : ℕ} {f : (Fin D → Bool) → ℂ} (c : ℂ)
    (hf : SupportsAt x i f) : SupportsAt x i (c • f) := by
  rw [SupportsAt, mulVec_smul, hf]

theorem SupportsAt.sub {x : Fin D → Bool} {i : ℕ} {f g : (Fin D → Bool) → ℂ}
    (hf : SupportsAt x i f) (hg : SupportsAt x i g) : SupportsAt x i (f - g) := by
  rw [SupportsAt, mulVec_sub, hf, hg]

theorem SupportsAt.single {x : Fin D → Bool} {i : ℕ} {u : Fin D → Bool}
    (hu : (hammingGraph D).dist x u = i) : SupportsAt x i (Pi.single u 1) := by
  refine supportsAt_of_forall ?_
  intro v hv
  by_contra hne
  have hvu : v ≠ u := by intro h; exact hne (h ▸ hu)
  exact hv (Pi.single_eq_of_ne hvu 1)

theorem supportsAt_kill {x : Fin D → Bool} {i j : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x j f) (hij : i ≠ j) :
    subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ f = 0 := by
  funext u
  rw [subconst_mulVec_apply]
  by_cases hu : (hammingGraph D).dist x u = i
  · rw [if_pos hu, one_mul]
    exact supportsAt_apply h (by rw [hu]; exact hij)
  · rw [if_neg hu, zero_mul]
    rfl

theorem supportsAt_neg {x : Fin D → Bool} {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x i f) : SupportsAt x i (-f) := by
  rw [SupportsAt, mulVec_neg, h]

/-- The raising operator raises the level by one. -/
theorem hdR_supportsAt (D : ℕ) (x : Fin D → Bool) {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x i f) : SupportsAt x (i + 1) (hdR D x *ᵥ f) := by
  refine supportsAt_of_forall ?_
  intro u hu
  by_contra hne
  have hne' : hammingDist x u ≠ i + 1 := by
    intro hc
    exact hne (by rw [hammingGraph_dist]; exact hc)
  apply hu
  rw [hdR_mulVec]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hpos : 1 ≤ hammingDist x u := by
    rw [← card_dnSet x u]
    exact Finset.card_pos.2 ⟨k, hk⟩
  exact supportsAt_apply h (by rw [hammingGraph_dist, hammingDist_flip_dn hk]; omega)

/-- The lowering operator lowers the level by one. -/
theorem hdL_apply_eq_zero (D : ℕ) (x : Fin D → Bool) {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x i f) {u : Fin D → Bool} (hu : hammingDist x u + 1 ≠ i) :
    (hdL D x *ᵥ f) u = 0 := by
  rw [hdL_mulVec]
  refine Finset.sum_eq_zero fun k hk => ?_
  exact supportsAt_apply h (by rw [hammingGraph_dist, hammingDist_flip_up hk]; exact hu)

/-- The lowering operator maps a level-`i` vector into level `i - 1`. -/
theorem hdL_apply_eq_zero' (D : ℕ) (x : Fin D → Bool) {i : ℕ} {f : (Fin D → Bool) → ℂ}
    (h : SupportsAt x i f) {u : Fin D → Bool} (hu : (hammingGraph D).dist x u ≠ i - 1) :
    (hdL D x *ᵥ f) u = 0 := by
  refine hdL_apply_eq_zero D x h (u := u) ?_
  intro hc
  exact hu (by rw [hammingGraph_dist]; omega)

/-- `A*` acts on a level-`i` vector by the scalar `D - 2i`. -/
theorem hdAst_smul_of_supportsAt (D : ℕ) (x : Fin D → Bool) {i : ℕ}
    {f : (Fin D → Bool) → ℂ} (h : SupportsAt x i f) :
    hdAst D x *ᵥ f = ((D : ℂ) - 2 * (i : ℂ)) • f := by
  funext u
  rw [hdAst_mulVec, Pi.smul_apply, smul_eq_mul]
  by_cases hu : (hammingGraph D).dist x u = i
  · rw [← hammingGraph_dist, hu]
  · rw [supportsAt_apply h hu, mul_zero, mul_zero]

/-! ## Stability from the two kinds of generators -/

section Generators

variable {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [Fintype X] [DecidableEq X]

/-- A subspace stable under `A` and under all `E*_i` is a `T(x)`-module. -/
theorem isStable_subconstituentAlgebra_of {G : SimpleGraph X} {x : X}
    {U : Submodule 𝕜 (X → 𝕜)}
    (hA : ∀ u ∈ U, adj (𝕜 := 𝕜) G *ᵥ u ∈ U)
    (hE : ∀ i : ℕ, ∀ u ∈ U, subconst (𝕜 := 𝕜) G x i *ᵥ u ∈ U) :
    IsStable (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra U := by
  intro a ha
  have hEq : (subconstituentAlgebra (𝕜 := 𝕜) G x).toSubalgebra
      = Algebra.adjoin 𝕜 (({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x)) ∪
          star ({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x))) :=
    StarAlgebra.adjoin_toSubalgebra _ _
  rw [hEq] at ha
  induction ha using Algebra.adjoin_induction with
  | mem m hm =>
      rcases hm with hm | hm
      · rcases hm with hm | hm
        · rw [Set.mem_singleton_iff] at hm
          subst hm
          exact hA
        · obtain ⟨i, rfl⟩ := hm
          exact hE i
      · have hm' : star m ∈ ({adj (𝕜 := 𝕜) G} ∪ Set.range (subconst (𝕜 := 𝕜) G x)) :=
          Set.mem_star.mp hm
        rcases hm' with hm' | hm'
        · rw [Set.mem_singleton_iff] at hm'
          have hm'' : m = adj (𝕜 := 𝕜) G := by
            rw [← star_star m, hm']
            exact star_adj (𝕜 := 𝕜) G
          rw [hm'']
          exact hA
        · obtain ⟨i, hi⟩ := hm'
          have hm'' : m = subconst (𝕜 := 𝕜) G x i := by
            rw [← star_star m, ← hi]
            exact star_subconst G x i
          rw [hm'']
          exact hE i
  | algebraMap r =>
      intro w hw
      have h1 : (algebraMap 𝕜 (Matrix X X 𝕜)) r *ᵥ w = r • w := by
        funext i
        rw [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]
        rfl
      rw [h1]
      exact Submodule.smul_mem _ r hw
  | add m n _ _ ihm ihn =>
      intro w hw
      rw [Matrix.add_mulVec]
      exact Submodule.add_mem _ (ihm w hw) (ihn w hw)
  | mul m n _ _ ihm ihn =>
      intro w hw
      rw [← Matrix.mulVec_mulVec]
      exact ihm _ (ihn w hw)

end Generators

/-! ## The `sl₂` module argument (Theorem 5.2 (ii) and thinness) -/

/-- The scalars of the `sl₂` computation. -/
def cc (D r i : ℕ) : ℂ := (D : ℂ) - 2 * (r : ℂ) - (i : ℂ) + 1

/-- The vectors supported on the `i`-th sphere. -/
def levelSub (D : ℕ) (x : Fin D → Bool) (i : ℕ) : Submodule ℂ ((Fin D → Bool) → ℂ) where
  carrier := {f | SupportsAt x i f}
  zero_mem' := SupportsAt.zero x i
  add_mem' := fun hf hg => SupportsAt.add hf hg
  smul_mem' := fun c _ hf => SupportsAt.smul c hf

theorem mem_levelSub {D : ℕ} {x : Fin D → Bool} {i : ℕ} {f : (Fin D → Bool) → ℂ} :
    f ∈ levelSub D x i ↔ SupportsAt x i f := Iff.rfl

/-- The normalised raising orbit `w_i = i!⁻¹ Rⁱ w` of a vector `w`. -/
def wseq (D : ℕ) (x : Fin D → Bool) (w : (Fin D → Bool) → ℂ) :
    ℕ → ((Fin D → Bool) → ℂ)
  | 0 => w
  | (n + 1) => (((n : ℂ) + 1))⁻¹ • (hdR D x *ᵥ wseq D x w n)

theorem wseq_zero (D : ℕ) (x : Fin D → Bool) (w : (Fin D → Bool) → ℂ) :
    wseq D x w 0 = w := rfl

theorem wseq_succ (D : ℕ) (x : Fin D → Bool) (w : (Fin D → Bool) → ℂ) (n : ℕ) :
    wseq D x w (n + 1) = (((n : ℂ) + 1))⁻¹ • (hdR D x *ᵥ wseq D x w n) := rfl

theorem hd2_modules_aux (D : ℕ) (x : Fin D → Bool) {W : Submodule ℂ ((Fin D → Bool) → ℂ)}
    (hWstab : IsStable (subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x).toSubalgebra W)
    (hWirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x).toSubalgebra W)
    {r d : ℕ} (hend : IsEndpoint (hammingGraph D) x W r)
    (hdiam : IsDiameter (hammingGraph D) x W r d) :
    d = D - 2 * r ∧ ThinModule (hammingGraph D) x W := by
  have hDle : ∀ y : Fin D → Bool, (hammingGraph D).dist x y ≤ D := by
    intro y; rw [hammingGraph_dist]; exact hammingDist_le_card x y
  -- (1) `E*_i W = 0` iff the level-`i` part of `W` vanishes
  have hiff : ∀ i, subconstImage (𝕜 := ℂ) (hammingGraph D) x i W = ⊥
      ↔ W ⊓ levelSub D x i = ⊥ := by
    intro i
    constructor
    · intro hbot
      rw [Submodule.eq_bot_iff]
      intro f hf
      obtain ⟨hfW, hfsupp⟩ := Submodule.mem_inf.1 hf
      have hfim : f ∈ subconstImage (𝕜 := ℂ) (hammingGraph D) x i W :=
        mem_matImage.2 ⟨f, hfW, hfsupp⟩
      rw [hbot] at hfim
      simpa using hfim
    · intro hbot
      rw [Submodule.eq_bot_iff]
      intro v hv
      obtain ⟨w, hw, rfl⟩ := mem_matImage.1 hv
      have h1 : subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ w ∈ W :=
        hWstab _ (subconst_mem_subconstituentAlgebra _ x i) w hw
      have h2 : SupportsAt x i (subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ w) := by
        rw [SupportsAt, Matrix.mulVec_mulVec, subconst_mul_self]
      have hmem : subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ w ∈ W ⊓ levelSub D x i :=
        Submodule.mem_inf.2 ⟨h1, h2⟩
      rw [hbot] at hmem
      simpa using hmem
  have hbot_lt : ∀ i, i < r → W ⊓ levelSub D x i = ⊥ := by
    intro i hi
    rw [← hiff i]
    by_contra hne
    exact absurd (hdiam.2 i hne).1 (by omega)
  have hbot_gt : ∀ i, r + d < i → W ⊓ levelSub D x i = ⊥ := by
    intro i hi
    rw [← hiff i]
    by_contra hne
    exact absurd (hdiam.2 i hne).2 (by omega)
  have hne_i : ∀ i, r ≤ i → i ≤ r + d → W ⊓ levelSub D x i ≠ ⊥ := by
    intro i h1 h2 hb
    exact hdiam.1 i h1 h2 ((hiff i).2 hb)
  -- (2) a nonzero vector of `W` in level `r`
  have hex : ∃ w : (Fin D → Bool) → ℂ, w ∈ W ∧ SupportsAt x r w ∧ w ≠ 0 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hne_i r le_rfl (by omega))
    exact ⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hw0⟩
  obtain ⟨w, hwW, hwsupp0, hwne⟩ := hex
  -- (3) the orbit
  have hwmem : ∀ n, wseq D x w n ∈ W := by
    intro n
    induction n with
    | zero => simpa [wseq_zero] using hwW
    | succ n ih =>
        rw [wseq_succ]
        exact Submodule.smul_mem _ _ (hWstab _ (hdR_mem D x) _ ih)
  have hwsupp : ∀ n, SupportsAt x (r + n) (wseq D x w n) := by
    intro n
    induction n with
    | zero => simpa [wseq_zero] using hwsupp0
    | succ n ih =>
        have h' : SupportsAt x (r + n + 1) ((((n : ℂ) + 1))⁻¹ • (hdR D x *ᵥ wseq D x w n)) :=
          SupportsAt.smul _ (hdR_supportsAt D x ih)
        have hidx : r + n + 1 = r + (n + 1) := by omega
        rw [hidx] at h'
        rw [wseq_succ]
        exact h'
  have hwseqR : ∀ n, hdR D x *ᵥ wseq D x w n = ((n : ℂ) + 1) • wseq D x w (n + 1) := by
    intro n
    have hc : ((n : ℂ) + 1) ≠ 0 := by
      have h : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h]
      exact Nat.cast_ne_zero.2 (Nat.succ_ne_zero n)
    rw [wseq_succ, smul_smul, mul_inv_cancel₀ hc, one_smul]
  -- (4) `L w₀ = 0`
  have hL0 : hdL D x *ᵥ wseq D x w 0 = 0 := by
    rw [wseq_zero]
    by_cases hr : r = 0
    · subst hr
      funext u
      exact hdL_apply_eq_zero D x hwsupp0 (by omega)
    · have hmem : hdL D x *ᵥ w ∈ W := hWstab _ (hdL_mem D x) _ hwW
      have hsupp : SupportsAt x (r - 1) (hdL D x *ᵥ w) := by
        refine supportsAt_of_forall ?_
        intro u hu
        by_contra hc
        exact hu (hdL_apply_eq_zero' D x hwsupp0 hc)
      have hmem2 : hdL D x *ᵥ w ∈ W ⊓ levelSub D x (r - 1) :=
        Submodule.mem_inf.2 ⟨hmem, hsupp⟩
      rw [hbot_lt (r - 1) (by omega)] at hmem2
      simpa using hmem2
  -- (5) the recursion `L w_{n+1} = cc (n+1) • w_n`
  have hLrec : ∀ n, hdL D x *ᵥ wseq D x w (n + 1) = cc D r (n + 1) • wseq D x w n := by
    intro n
    induction n with
    | zero =>
        have hv : wseq D x w 1 = ((0 : ℂ) + 1)⁻¹ • (hdR D x *ᵥ wseq D x w 0) := by
          simpa using wseq_succ D x w 0
        rw [hv, mulVec_smul, hdLRapply, hL0, mulVec_zero, add_zero,
          hdAst_smul_of_supportsAt D x (hwsupp 0), smul_smul]
        simp only [cc]
        push_cast
        ring_nf
    | succ n ih =>
        have hv : wseq D x w (n + 2) =
            (((n : ℂ) + 1 + 1))⁻¹ • (hdR D x *ᵥ wseq D x w (n + 1)) := by
          have h := wseq_succ D x w (n + 1)
          simpa [Nat.cast_add, Nat.cast_one] using h
        have hRv : hdR D x *ᵥ (cc D r (n + 1) • wseq D x w n)
            = (cc D r (n + 1) * ((n : ℂ) + 1)) • wseq D x w (n + 1) := by
          rw [mulVec_smul, hwseqR n, smul_smul]
        rw [hv, mulVec_smul, hdLRapply, ih, hdAst_smul_of_supportsAt D x (hwsupp (n + 1)),
          hRv, ← add_smul, smul_smul]
        congr 1
        simp only [cc]
        push_cast
        have hc : ((n : ℂ) + 1 + 1) ≠ 0 := by
          have h : ((n : ℂ) + 1 + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
          rw [h]
          exact Nat.cast_ne_zero.2 (by omega)
        field_simp
        ring
  -- (6) `R w_d = 0`
  have hRwd : hdR D x *ᵥ wseq D x w d = 0 := by
    have hmem : hdR D x *ᵥ wseq D x w d ∈ W := hWstab _ (hdR_mem D x) _ (hwmem d)
    have hsupp : SupportsAt x (r + (d + 1)) (hdR D x *ᵥ wseq D x w d) := by
      have h := hdR_supportsAt D x (hwsupp d)
      have hidx : r + d + 1 = r + (d + 1) := by omega
      rwa [hidx] at h
    have hmem2 : hdR D x *ᵥ wseq D x w d ∈ W ⊓ levelSub D x (r + (d + 1)) :=
      Submodule.mem_inf.2 ⟨hmem, hsupp⟩
    rw [hbot_gt (r + (d + 1)) (by omega)] at hmem2
    simpa using hmem2
  -- (7) the span of the orbit is a `T(x)`-module, hence all of `W`
  set W' : Submodule ℂ ((Fin D → Bool) → ℂ) :=
    Submodule.span ℂ (Set.range fun j : Fin (d + 1) => wseq D x w (j : ℕ)) with hW'def
  have hRinv : ∀ v ∈ W', hdR D x *ᵥ v ∈ W' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        change hdR D x *ᵥ wseq D x w (j : ℕ) ∈ W'
        have hj : (j : ℕ) ≤ d := by have := j.2; omega
        by_cases hjd : (j : ℕ) = d
        · rw [hjd, hRwd]
          exact Submodule.zero_mem _
        · have hlt : (j : ℕ) + 1 ≤ d := by omega
          rw [hwseqR]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          exact ⟨⟨(j : ℕ) + 1, by omega⟩, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hLinv : ∀ v ∈ W', hdL D x *ᵥ v ∈ W' := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        change hdL D x *ᵥ wseq D x w (j : ℕ) ∈ W'
        have hj : (j : ℕ) ≤ d := by have := j.2; omega
        rcases Nat.eq_zero_or_pos ((j : ℕ)) with h0 | hpos
        · rw [h0, hL0]
          exact Submodule.zero_mem _
        · obtain ⟨n, hn⟩ : ∃ n, (j : ℕ) = n + 1 := ⟨(j : ℕ) - 1, by omega⟩
          rw [hn, hLrec n]
          refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
          exact ⟨⟨n, by omega⟩, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hEinv : ∀ i : ℕ, ∀ v ∈ W', subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ v ∈ W' := by
    intro i v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨j, rfl⟩ := hv
        change subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ wseq D x w (j : ℕ) ∈ W'
        by_cases hij : i = r + (j : ℕ)
        · rw [hij]
          have := hwsupp (j : ℕ)
          rw [show subconst (𝕜 := ℂ) (hammingGraph D) x (r + (j:ℕ)) *ᵥ wseq D x w (j:ℕ)
              = wseq D x w (j:ℕ) from this]
          exact Submodule.subset_span ⟨j, rfl⟩
        · rw [supportsAt_kill (hwsupp (j : ℕ)) hij]
          exact Submodule.zero_mem _
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add a b _ _ ha hb => rw [mulVec_add]; exact Submodule.add_mem _ ha hb
    | smul c a _ ha => rw [mulVec_smul]; exact Submodule.smul_mem _ _ ha
  have hAinv : ∀ v ∈ W', adj (𝕜 := ℂ) (hammingGraph D) *ᵥ v ∈ W' := by
    intro v hv
    rw [adj_mulVec_eq]
    exact Submodule.add_mem _ (hRinv v hv) (hLinv v hv)
  have hW'stab : IsStable (subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x).toSubalgebra W' :=
    isStable_subconstituentAlgebra_of hAinv hEinv
  have hW'le : W' ≤ W := by
    rw [hW'def, Submodule.span_le]
    rintro v ⟨j, rfl⟩
    exact hwmem (j : ℕ)
  have hW'ne : W' ≠ ⊥ := by
    intro hbot
    have hmem : wseq D x w 0 ∈ W' := by
      rw [hW'def]
      exact Submodule.subset_span ⟨⟨0, by omega⟩, rfl⟩
    rw [hbot] at hmem
    have h0 : wseq D x w 0 = 0 := by simpa using hmem
    rw [wseq_zero] at h0
    exact hwne h0
  have hW'eq : W' = W := hWirr.2 W' hW'le hW'stab hW'ne
  -- (8) expansion of any element of `W` in the orbit
  have hspan : ∀ v ∈ W, ∃ c : Fin (d + 1) → ℂ,
      v = ∑ j : Fin (d + 1), c j • wseq D x w (j : ℕ) := by
    intro v hv
    have hv' : v ∈ W' := by rw [hW'eq]; exact hv
    rw [hW'def] at hv'
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hv'
    exact ⟨c, hc.symm⟩
  -- (9) the subconstituent of a level is a line
  have hproj : ∀ (i : ℕ), i ≤ d → ∀ v : (Fin D → Bool) → ℂ, v ∈ W →
      SupportsAt x (r + i) v → ∃ c : ℂ, v = c • wseq D x w i := by
    intro i hi v hvW hvsupp
    obtain ⟨c, hc⟩ := hspan v hvW
    have h1 : subconst (𝕜 := ℂ) (hammingGraph D) x (r + i) *ᵥ v
        = ∑ j : Fin (d + 1), c j • (subconst (𝕜 := ℂ) (hammingGraph D) x (r + i)
            *ᵥ wseq D x w (j : ℕ)) := by
      rw [hc, Matrix.mulVec_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [mulVec_smul]
    have h2 : ∑ j : Fin (d + 1), c j • (subconst (𝕜 := ℂ) (hammingGraph D) x (r + i)
        *ᵥ wseq D x w (j : ℕ)) = c ⟨i, by omega⟩ • wseq D x w i := by
      rw [Finset.sum_eq_single ⟨i, by omega⟩]
      · rw [show subconst (𝕜 := ℂ) (hammingGraph D) x (r + i) *ᵥ wseq D x w i
            = wseq D x w i from hwsupp i]
      · intro j _ hj
        have hji : i ≠ (j : ℕ) := by
          intro h
          exact hj (Fin.ext h.symm)
        have hne : (r + i) ≠ (r + (j : ℕ)) := by omega
        rw [supportsAt_kill (hwsupp (j : ℕ)) hne, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    refine ⟨c ⟨i, by omega⟩, ?_⟩
    rw [← h2, ← h1, hvsupp]
  have hwnz : ∀ i, i ≤ d → wseq D x w i ≠ 0 := by
    intro i hi
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (hne_i (r + i) (by omega) (by omega))
    obtain ⟨huW, husupp⟩ := Submodule.mem_inf.1 hu
    obtain ⟨c, hc⟩ := hproj i hi u huW husupp
    intro hz
    exact hu0 (by rw [hc, hz, smul_zero])
  -- (10) the final scalar computation
  have hscal : ((D : ℂ) - 2 * (r : ℂ) - (d : ℂ)) = 0 := by
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · have hrel := hdLRapply D x (wseq D x w d)
      rw [hd0] at hrel
      rw [wseq_zero] at hrel
      have hRw : hdR D x *ᵥ w = 0 := by
        have h := hRwd
        rw [hd0, wseq_zero] at h
        exact h
      have hLw : hdL D x *ᵥ w = 0 := by
        have h := hL0
        rwa [wseq_zero] at h
      rw [hRw, mulVec_zero, hLw, mulVec_zero,
        hdAst_smul_of_supportsAt D x hwsupp0, add_zero] at hrel
      have hs0 : ((D : ℂ) - 2 * (r : ℂ)) = 0 := by
        rcases smul_eq_zero.1 hrel.symm with h | h
        · exact h
        · exact absurd h hwne
      subst hd0
      push_cast
      linear_combination hs0
    · obtain ⟨n, hn⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
      have hLd : hdL D x *ᵥ wseq D x w d = cc D r d • wseq D x w (d - 1) := by
        rw [hn]
        have h := hLrec n
        simpa using h
      have hRd : hdR D x *ᵥ wseq D x w (d - 1) = (d : ℂ) • wseq D x w d := by
        rw [hn]
        have h := hwseqR n
        simpa using h
      have hrel := hdLRapply D x (wseq D x w d)
      rw [hRwd, mulVec_zero, hLd, mulVec_smul, hRd, smul_smul,
        hdAst_smul_of_supportsAt D x (hwsupp d), ← add_smul] at hrel
      have hsc0 : ((D : ℂ) - 2 * ((r + d : ℕ) : ℂ)) + cc D r d * (d : ℂ) = 0 := by
        rcases smul_eq_zero.1 hrel.symm with h | h
        · exact h
        · exact absurd h (hwnz d (by omega))
      have hprod : ((d : ℂ) + 1) * ((D : ℂ) - 2 * (r : ℂ) - (d : ℂ)) = 0 := by
        have hfac : ((D : ℂ) - 2 * ((r + d : ℕ) : ℂ)) + cc D r d * (d : ℂ)
            = ((d : ℂ) + 1) * ((D : ℂ) - 2 * (r : ℂ) - (d : ℂ)) := by
          simp only [cc]
          push_cast
          ring
        rw [← hfac]
        exact hsc0
      have hd1 : ((d : ℂ) + 1) ≠ 0 := by
        have h : ((d : ℂ) + 1) = ((d + 1 : ℕ) : ℂ) := by push_cast; ring
        rw [h]
        exact Nat.cast_ne_zero.2 (by omega)
      exact (mul_eq_zero.1 hprod).resolve_left hd1
  have hd_eq : d = D - 2 * r := by
    have h2 : (D : ℂ) = ((2 * r + d : ℕ) : ℂ) := by
      have h := hscal
      push_cast
      linear_combination h
    have := Nat.cast_inj.1 h2
    omega
  refine ⟨hd_eq, ?_⟩
  -- (11) thinness
  intro i
  by_cases hi : r ≤ i ∧ i ≤ r + d
  · have hle : subconstImage (𝕜 := ℂ) (hammingGraph D) x i W
        ≤ Submodule.span ℂ {wseq D x w (i - r)} := by
      intro v hv
      obtain ⟨u, huW, rfl⟩ := mem_matImage.1 hv
      have hfun : subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ u ∈ W :=
        hWstab _ (subconst_mem_subconstituentAlgebra _ x i) u huW
      have hsupp : SupportsAt x (r + (i - r)) (subconst (𝕜 := ℂ) (hammingGraph D) x i *ᵥ u) := by
        have hidx : r + (i - r) = i := by omega
        rw [hidx]
        rw [SupportsAt, Matrix.mulVec_mulVec, subconst_mul_self]
      obtain ⟨c, hc⟩ := hproj (i - r) (by omega) _ hfun hsupp
      rw [hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
    haveI : Module.Finite ℂ ↥(Submodule.span ℂ {wseq D x w (i - r)}) :=
      Module.Finite.span_of_finite ℂ (Set.finite_singleton _)
    have hle1 : Module.finrank ℂ ↥(Submodule.span ℂ {wseq D x w (i - r)}) ≤ 1 := by
      by_cases hz : wseq D x w (i - r) = 0
      · rw [Submodule.span_singleton_eq_bot.2 hz, finrank_bot]
        exact zero_le_one
      · rw [finrank_span_singleton hz]
    exact le_trans (Submodule.finrank_mono hle) hle1
  · have hbot : subconstImage (𝕜 := ℂ) (hammingGraph D) x i W = ⊥ := by
      by_contra hne
      exact hi (hdiam.2 i hne)
    rw [hbot, finrank_bot]
    exact zero_le_one

end HD2

/-- **Theorem 5.2.**  For `H(D,2)`, an irreducible `T(x)`-module of endpoint `r`
has diameter `D - 2r` and is determined up to isomorphism by `r`; its multiplicity
is `C(D,r) - C(D,r-1)`.

The stability hypothesis is not part of the draft statement, but it is needed:
`IsIrreducible` (`Basic.lean`, Definition 1.7) does not assert that the subspace is
`T(x)`-invariant, and `span{x̂}` for `D ≥ 1` is a counterexample (see
`hd2_modules_needs_stability` in `Terwilliger/HammingHD2.lean`).  With stability, the
lecture-5 `sl₂` argument shows `d + 2r = D` — in particular `2r ≤ D`, so no separate
endpoint bound is needed — and that every `Eᵢ*W` is at most one-dimensional. -/
theorem hd2_modules (D : ℕ) (x : Fin D → Bool) {W : Submodule ℂ ((Fin D → Bool) → ℂ)}
    (hWstab : IsStable (subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x).toSubalgebra W)
    (hW : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) (hammingGraph D) x).toSubalgebra W)
    {r d : ℕ} (hend : IsEndpoint (hammingGraph D) x W r) (hdiam : IsDiameter (hammingGraph D) x W r d) :
    d = D - 2 * r ∧ ThinModule (hammingGraph D) x W :=
  HD2.hd2_modules_aux D x hWstab hW hend hdiam

/-! ## The Johnson graph `J(D,N)` -/

/-- The Johnson graph `J(D,N)`: vertices are the `D`-element subsets of `Fin N`,
adjacent when they meet in `D - 1` points. -/
def johnsonGraph (D N : ℕ) : SimpleGraph {s : Finset (Fin N) // s.card = D} :=
  SimpleGraph.fromRel fun S T => (S.1 ∩ T.1).card = D - 1

/-! ## The up and down incidence matrices between `j`- and `(j+1)`-subsets -/

/-- The vertices of the Johnson graph `J(j,N)`: the `j`-element subsets of `Fin N`. -/
abbrev johnsonVerts (j N : ℕ) : Type := {s : Finset (Fin N) // s.card = j}

/-- The "up" incidence matrix, from functions on `j`-subsets to functions on
`(j+1)`-subsets: `(upMat j N) S T = 1` when `T ⊆ S`. -/
def upMat (j N : ℕ) : Matrix (johnsonVerts (j+1) N) (johnsonVerts j N) ℂ :=
  fun S T => if (T.1 : Finset (Fin N)) ⊆ (S.1 : Finset (Fin N)) then 1 else 0

/-- The "down" incidence matrix, the transpose of `upMat`. -/
def dnMat (j N : ℕ) : Matrix (johnsonVerts j N) (johnsonVerts (j+1) N) ℂ :=
  fun T S => if (T.1 : Finset (Fin N)) ⊆ (S.1 : Finset (Fin N)) then 1 else 0

@[simp] theorem upMat_apply (j N : ℕ) (S : johnsonVerts (j+1) N) (T : johnsonVerts j N) :
    upMat j N S T = if (T.1 : Finset (Fin N)) ⊆ (S.1 : Finset (Fin N)) then 1 else 0 := rfl

@[simp] theorem dnMat_apply (j N : ℕ) (T : johnsonVerts j N) (S : johnsonVerts (j+1) N) :
    dnMat j N T S = if (T.1 : Finset (Fin N)) ⊆ (S.1 : Finset (Fin N)) then 1 else 0 := rfl

/-! ### Counting the `j`-subsets of a set, and the `j`-subsets containing a set -/

/-- The number of `j`-element subsets of `U`. -/
theorem sum_indicator_subset (j N : ℕ) (U : Finset (Fin N)) :
    ∑ T : johnsonVerts j N,
        (if (T.1 : Finset (Fin N)) ⊆ U then (1 : ℂ) else 0)
      = (U.card.choose j : ℂ) := by
  have hcard : (Finset.univ.filter
      fun T : johnsonVerts j N => (T.1 : Finset (Fin N)) ⊆ U).card
        = (U.powersetCard j).card := by
    refine Finset.card_bij (fun (T : johnsonVerts j N) _ => (T.1 : Finset (Fin N))) ?_ ?_ ?_
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      simp only [Finset.mem_powersetCard]
      exact ⟨hT, T.2⟩
    · intro T1 _ T2 _ h
      exact Subtype.ext h
    · intro b hb
      simp only [Finset.mem_powersetCard] at hb
      exact ⟨⟨b, hb.2⟩, by simp [hb.1], rfl⟩
  rw [Finset.sum_boole, hcard, Finset.card_powersetCard]

/-- The number of `j`-element subsets of `Fin N` that contain `U`. -/
theorem sum_indicator_superset (j N : ℕ) (U : Finset (Fin N)) :
    ∑ S : johnsonVerts j N,
        (if U ⊆ (S.1 : Finset (Fin N)) then (1 : ℂ) else 0)
      = if U.card ≤ j then ((N - U.card).choose (j - U.card) : ℂ) else 0 := by
  by_cases hU : U.card ≤ j
  · rw [if_pos hU]
    have hcard : (Finset.univ.filter
        fun S : johnsonVerts j N => U ⊆ (S.1 : Finset (Fin N))).card
          = ((Finset.univ \ U).powersetCard (j - U.card)).card := by
      refine Finset.card_bij
        (fun (S : johnsonVerts j N) _ => (S.1 : Finset (Fin N)) \ U) ?_ ?_ ?_
      · intro S hS
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS
        simp only [Finset.mem_powersetCard]
        refine ⟨?_, ?_⟩
        · intro x hx
          rw [Finset.mem_sdiff] at hx ⊢
          exact ⟨Finset.mem_univ x, hx.2⟩
        have h1 : (S.1 : Finset (Fin N)).card = U.card + ((S.1 : Finset (Fin N)) \ U).card := by
          rw [← Finset.card_sdiff_add_card_eq_card hS, add_comm]
        omega
      · intro S1 hS1 S2 hS2 h
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hS1 hS2
        have h1 : (S1.1 : Finset (Fin N)) = U ∪ (S1.1 \ U) := (Finset.union_sdiff_of_subset hS1).symm
        have h2 : (S2.1 : Finset (Fin N)) = U ∪ (S2.1 \ U) := (Finset.union_sdiff_of_subset hS2).symm
        exact Subtype.ext (by rw [h1, h2, h])
      · intro b hb
        simp only [Finset.mem_powersetCard] at hb
        obtain ⟨hb1, hb2⟩ := hb
        have hdisj : Disjoint U b := (Finset.disjoint_of_subset_left hb1 Finset.sdiff_disjoint).symm
        refine ⟨⟨U ∪ b, ?_⟩, ?_, ?_⟩
        · rw [Finset.card_union_of_disjoint hdisj, hb2]
          omega
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact Finset.subset_union_left
        · rw [Finset.union_sdiff_cancel_left hdisj]
    have hcu : ((Finset.univ \ U : Finset (Fin N))).card = N - U.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    rw [Finset.sum_boole, hcard, Finset.card_powersetCard, hcu]
  · rw [if_neg hU]
    apply Finset.sum_eq_zero
    intro S _
    rw [if_neg]
    intro hsub
    exact hU (le_trans (Finset.card_le_card hsub) (le_of_eq S.2))

/-! ### The adjacency relation of the Johnson graph -/

/-- Two `D`-element subsets are adjacent in `J(D,N)` exactly when they are distinct
and meet in `D - 1` points. -/
theorem johnsonGraph_adj_iff (D N : ℕ) {S T : johnsonVerts D N} :
    (johnsonGraph D N).Adj S T ↔ S ≠ T ∧ (S.1 ∩ T.1).card = D - 1 := by
  have h : johnsonGraph D N
      = SimpleGraph.fromRel (fun S T : johnsonVerts D N => (S.1 ∩ T.1).card = D - 1) := rfl
  rw [h, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, h⟩
    · exact ⟨hne, by rw [Finset.inter_comm]; exact h⟩
  · rintro ⟨hne, h⟩
    exact ⟨hne, Or.inl h⟩

/-! ### The two operator identities -/

/-- `upMat * dnMat` is the adjacency matrix of `J(j+1,N)` plus `(j+1)` times the
identity: two `(j+1)`-sets have a common `j`-subset exactly when they coincide
(`j+1` of them) or are adjacent in `J(j+1,N)` (exactly one of them). -/
theorem upMat_mul_dnMat (j N : ℕ) :
    upMat j N * dnMat j N
      = adj (𝕜 := ℂ) (johnsonGraph (j+1) N)
        + ((j : ℂ) + 1) •
            (1 : Matrix (johnsonVerts (j+1) N) (johnsonVerts (j+1) N) ℂ) := by
  ext S S'
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, adj_apply, Matrix.mul_apply]
  have hterm : ∀ T : johnsonVerts j N,
      upMat j N S T * dnMat j N T S'
        = (if (T.1 : Finset (Fin N)) ⊆ S.1 ∩ S'.1 then (1 : ℂ) else 0) := by
    intro T
    rw [upMat_apply, dnMat_apply]
    by_cases h1 : (T.1 : Finset (Fin N)) ⊆ S.1 <;>
      by_cases h2 : (T.1 : Finset (Fin N)) ⊆ S'.1 <;>
      by_cases h3 : (T.1 : Finset (Fin N)) ⊆ S.1 ∩ S'.1 <;>
      simp_all [Finset.subset_inter_iff]
  rw [Finset.sum_congr rfl (fun T _ => hterm T),
    sum_indicator_subset j N (S.1 ∩ S'.1)]
  by_cases hSS : S = S'
  · subst hSS
    rw [Finset.inter_self, S.2, Nat.choose_succ_self_right,
      if_neg (SimpleGraph.irrefl _), if_pos rfl]
    push_cast
    ring
  · have hcardle : (S.1 ∩ S'.1).card ≤ j := by
      have h1 : (S.1 ∩ S'.1).card ≤ S.1.card :=
        Finset.card_le_card (Finset.inter_subset_left)
      rw [S.2] at h1
      rcases lt_or_eq_of_le h1 with hlt | heq
      · omega
      · exfalso
        apply hSS
        have hinter : S.1 ∩ S'.1 = S.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [S.2, heq])
        have hsub : S.1 ⊆ S'.1 := by
          rw [← hinter]; exact Finset.inter_subset_right
        exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [S.2, S'.2]))
    rcases lt_or_eq_of_le hcardle with hlt | heq
    · have hchoose : ((S.1 ∩ S'.1).card.choose j : ℂ) = 0 := by
        rw [Nat.choose_eq_zero_of_lt hlt]; simp
      rw [hchoose, if_neg hSS, if_neg]
      · ring
      · rw [johnsonGraph_adj_iff]
        rintro ⟨-, hc⟩
        omega
    · have hchoose : ((S.1 ∩ S'.1).card.choose j : ℂ) = 1 := by
        rw [heq, Nat.choose_self]; simp
      rw [hchoose, if_neg hSS, if_pos]
      · ring
      · rw [johnsonGraph_adj_iff]
        exact ⟨hSS, by omega⟩

/-- `dnMat * upMat` is the adjacency matrix of `J(j,N)` plus `(N-j)` times the
identity: the `(j+1)`-sets containing a `j`-set `T` and another `T'` are `N-j` when
`T = T'`, one when `T, T'` are adjacent, and none otherwise. -/
theorem dnMat_mul_upMat (j N : ℕ) :
    dnMat j N * upMat j N
      = adj (𝕜 := ℂ) (johnsonGraph j N)
        + (((N - j : ℕ) : ℂ)) •
            (1 : Matrix (johnsonVerts j N) (johnsonVerts j N) ℂ) := by
  ext T T'
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, adj_apply, Matrix.mul_apply]
  have hterm : ∀ S : johnsonVerts (j+1) N,
      dnMat j N T S * upMat j N S T'
        = (if ((T.1 : Finset (Fin N)) ∪ (T'.1 : Finset (Fin N))) ⊆ S.1 then (1 : ℂ) else 0) := by
    intro S
    rw [dnMat_apply, upMat_apply]
    by_cases h1 : (T.1 : Finset (Fin N)) ⊆ S.1 <;>
      by_cases h2 : (T'.1 : Finset (Fin N)) ⊆ S.1 <;>
      by_cases h3 : ((T.1 : Finset (Fin N)) ∪ (T'.1 : Finset (Fin N))) ⊆ S.1 <;>
      simp_all [Finset.union_subset_iff]
  rw [Finset.sum_congr rfl (fun S _ => hterm S),
    sum_indicator_superset (j+1) N (T.1 ∪ T'.1)]
  by_cases hTT : T = T'
  · subst hTT
    rw [Finset.union_self, T.2, if_pos (Nat.le_succ j), show (j + 1) - j = 1 from by omega,
      Nat.choose_one_right, if_neg (SimpleGraph.irrefl _), if_pos rfl]
    ring
  · have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · exfalso
        have h1 : (T.1 : Finset (Fin N)) = ∅ := Finset.card_eq_zero.mp (by rw [T.2, h])
        have h2 : (T'.1 : Finset (Fin N)) = ∅ := Finset.card_eq_zero.mp (by rw [T'.2, h])
        exact hTT (Subtype.ext (by rw [h1, h2]))
      · exact h
    have hle : (T.1 ∩ T'.1).card ≤ j - 1 := by
      have h1 : (T.1 ∩ T'.1).card ≤ T.1.card :=
        Finset.card_le_card (Finset.inter_subset_left)
      rw [T.2] at h1
      rcases lt_or_eq_of_le h1 with hlt | heq
      · omega
      · exfalso
        apply hTT
        have hinter : T.1 ∩ T'.1 = T.1 :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by rw [T.2, heq])
        have hsub : T.1 ⊆ T'.1 := by
          rw [← hinter]; exact Finset.inter_subset_right
        exact Subtype.ext (Finset.eq_of_subset_of_card_le hsub (by rw [T.2, T'.2]))
    have hcard_union : (T.1 ∪ T'.1).card + (T.1 ∩ T'.1).card = 2 * j := by
      rw [Finset.card_union_add_card_inter, T.2, T'.2]
      ring
    rcases lt_or_eq_of_le hle with hlt | heq
    · rw [if_neg (by omega : ¬ (T.1 ∪ T'.1).card ≤ j + 1), if_neg hTT, if_neg]
      · ring
      · rw [johnsonGraph_adj_iff]
        rintro ⟨-, hc⟩
        omega
    · have hunion : (T.1 ∪ T'.1).card = j + 1 := by omega
      rw [hunion, if_pos (by omega : j + 1 ≤ j + 1),
        show (j + 1) - (j + 1) = 0 from by omega, Nat.choose_zero_right, if_pos, if_neg hTT]
      · ring
      · rw [johnsonGraph_adj_iff]
        exact ⟨hTT, heq⟩

/-! ### Shifting the characteristic polynomial by a scalar matrix -/

theorem charpoly_add_smul_one {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℂ) (c : ℂ) :
    (M + c • (1 : Matrix n n ℂ)).charpoly = M.charpoly.comp (Polynomial.X - Polynomial.C c) := by
  have h : M + c • (1 : Matrix n n ℂ) = M - Matrix.scalar n (-c) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.scalar_apply,
      Matrix.one_apply, Matrix.diagonal_apply]
    by_cases hij : i = j
    · simp [hij]
    · simp [hij]
  rw [h, Matrix.charpoly_sub_scalar, map_neg, sub_eq_add_neg]

/-! ### The recursion for the characteristic polynomial of `J(j,N)` -/

/-- The one-step recursion: `charpoly J(j+1,N)` is `(X + j+1)^{C(N,j+1)-C(N,j)}` times
`charpoly J(j,N)` with `X` shifted by `-(N-2j-1)`. -/
theorem charpoly_johnson_succ (j N : ℕ) (hj : 2 * (j + 1) ≤ N) :
    (adj (𝕜 := ℂ) (johnsonGraph (j+1) N)).charpoly
      = (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) ^ (Nat.choose N (j+1) - Nat.choose N j)
        * (adj (𝕜 := ℂ) (johnsonGraph j N)).charpoly.comp
            (Polynomial.X - Polynomial.C (((N - (2*j+1) : ℕ) : ℂ))) := by
  have hle : Fintype.card (johnsonVerts j N) ≤ Fintype.card (johnsonVerts (j+1) N) := by
    simp only [johnsonVerts, Fintype.card_finset_len, Fintype.card_fin]
    exact Nat.choose_le_succ_of_lt_half_left (by omega)
  have hA : upMat j N * dnMat j N - Matrix.scalar (johnsonVerts (j+1) N) ((j : ℂ) + 1)
      = adj (𝕜 := ℂ) (johnsonGraph (j+1) N) := by
    rw [upMat_mul_dnMat, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal, add_sub_cancel_right]
  have hB : dnMat j N * upMat j N
      = adj (𝕜 := ℂ) (johnsonGraph j N) + (((N - j : ℕ) : ℂ)) •
          (1 : Matrix (johnsonVerts j N) (johnsonVerts j N) ℂ) := dnMat_mul_upMat j N
  have hcard : Fintype.card (johnsonVerts (j+1) N) - Fintype.card (johnsonVerts j N)
      = Nat.choose N (j+1) - Nat.choose N j := by
    simp only [johnsonVerts, Fintype.card_finset_len, Fintype.card_fin]
  have hc' : ((j : ℂ) + 1) - (((N - j : ℕ)) : ℂ) = -((((N - (2*j+1) : ℕ)) : ℂ)) := by
    have h1 : j ≤ N := by omega
    have h2 : 2*j+1 ≤ N := by omega
    rw [Nat.cast_sub h1, Nat.cast_sub h2]
    push_cast
    ring
  have hshift : (Polynomial.X - Polynomial.C (((N - j : ℕ) : ℂ))).comp
        (Polynomial.X + Polynomial.C ((j : ℂ) + 1))
      = Polynomial.X - Polynomial.C (((N - (2*j+1) : ℕ) : ℂ)) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [add_sub_assoc, ← Polynomial.C_sub, hc', Polynomial.C_neg, sub_eq_add_neg]
  have hstep : (dnMat j N * upMat j N).charpoly.comp (Polynomial.X + Polynomial.C ((j : ℂ) + 1))
      = ((adj (𝕜 := ℂ) (johnsonGraph j N)).charpoly.comp
          (Polynomial.X - Polynomial.C (((N - j : ℕ) : ℂ)))).comp
        (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) := by
    rw [hB, charpoly_add_smul_one]
  calc (adj (𝕜 := ℂ) (johnsonGraph (j+1) N)).charpoly
      = (upMat j N * dnMat j N
          - Matrix.scalar (johnsonVerts (j+1) N) ((j : ℂ) + 1)).charpoly := by rw [hA]
    _ = (upMat j N * dnMat j N).charpoly.comp
          (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) := Matrix.charpoly_sub_scalar _ _
    _ = (Polynomial.X ^ (Fintype.card (johnsonVerts (j+1) N)
            - Fintype.card (johnsonVerts j N))
          * (dnMat j N * upMat j N).charpoly).comp
          (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) := by
        rw [Matrix.charpoly_mul_comm_of_le (upMat j N) (dnMat j N) hle]
    _ = (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) ^ (Nat.choose N (j+1) - Nat.choose N j)
          * ((dnMat j N * upMat j N).charpoly.comp
              (Polynomial.X + Polynomial.C ((j : ℂ) + 1))) := by
        rw [Polynomial.mul_comp, Polynomial.pow_comp, Polynomial.X_comp, hcard]
    _ = (Polynomial.X + Polynomial.C ((j : ℂ) + 1)) ^ (Nat.choose N (j+1) - Nat.choose N j)
          * (adj (𝕜 := ℂ) (johnsonGraph j N)).charpoly.comp
              (Polynomial.X - Polynomial.C (((N - (2*j+1) : ℕ) : ℂ))) := by
        rw [hstep, Polynomial.comp_assoc, hshift]

/-! ### The Eberlein eigenvalues, the multiplicities, and the induction -/

/-- The `i`-th Eberlein eigenvalue `(N-j-i)(j-i) - i` of `J(j,N)`, read in `ℂ`. -/
def theta (N j i : ℕ) : ℂ := ((N : ℂ) - j - i) * ((j : ℂ) - i) - i

/-- The multiplicity `C(N,i) - C(N,i-1)` of the `i`-th eigenvalue (`1` for `i = 0`). -/
def jmult (N i : ℕ) : ℕ := Nat.choose N i - (if i = 0 then 0 else Nat.choose N (i - 1))

theorem jmult_zero (N : ℕ) : jmult N 0 = 1 := by
  simp [jmult]

theorem jmult_succ (N j : ℕ) :
    jmult N (j + 1) = Nat.choose N (j + 1) - Nat.choose N j := by
  simp [jmult]

theorem theta_zero (N : ℕ) : theta N 0 0 = 0 := by
  simp [theta]

/-- The last eigenvalue of `J(j,N)` is `-j`. -/
theorem theta_self (N j : ℕ) : theta N j j = -((j : ℂ)) := by
  simp [theta]

/-- The eigenvalues of `J(j,N)` and of `J(j+1,N)` agree up to the shift `-(N-2j-1)`. -/
theorem theta_shift {N j i : ℕ} (hj : 2 * (j + 1) ≤ N) :
    theta N j i + (((N - (2*j+1) : ℕ)) : ℂ) = theta N (j+1) i := by
  unfold theta
  have h : (((N - (2*j+1) : ℕ)) : ℂ) = (N : ℂ) - ((2 * j : ℕ) + 1) := by
    rw [Nat.cast_sub (by omega : 2*j+1 ≤ N)]
    push_cast
    ring
  rw [h]
  push_cast
  ring

/-- `theta` as an integer expression (no truncated subtraction). -/
theorem theta_int {N j i : ℕ} :
    theta N j i = (((((N : ℤ) - j - i) * ((j : ℤ) - i) - i : ℤ)) : ℂ) := by
  unfold theta
  push_cast
  ring

/-- Shifting a product of `(X - C (a i)) ^ (m i)` by `X ↦ X - c`. -/
theorem prod_shift (s : Finset ℕ) (a b : ℕ → ℂ) (c : ℂ) (m : ℕ → ℕ)
    (h : ∀ i ∈ s, a i + c = b i) :
    (∏ i ∈ s, (Polynomial.X - Polynomial.C (a i)) ^ (m i)).comp
        (Polynomial.X - Polynomial.C c)
      = ∏ i ∈ s, (Polynomial.X - Polynomial.C (b i)) ^ (m i) := by
  rw [Polynomial.prod_comp]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  have hbase : (Polynomial.X - Polynomial.C (a i)).comp (Polynomial.X - Polynomial.C c)
      = Polynomial.X - Polynomial.C (b i) := by
    simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]
    rw [sub_sub, ← Polynomial.C_add]
    congr 1
    rw [add_comm, h i hi]
  rw [Polynomial.pow_comp, hbase]

theorem adj_johnsonGraph_zero (N : ℕ) : adj (𝕜 := ℂ) (johnsonGraph 0 N) = 0 := by
  ext S S'
  have hSS : S = S' := Subtype.ext (by
    rw [Finset.card_eq_zero.mp S.2, Finset.card_eq_zero.mp S'.2])
  subst hSS
  rw [adj_apply, Matrix.zero_apply, if_neg]
  exact SimpleGraph.irrefl _

theorem charpoly_johnson_zero (N : ℕ) :
    (adj (𝕜 := ℂ) (johnsonGraph 0 N)).charpoly = Polynomial.X := by
  rw [adj_johnsonGraph_zero, Matrix.charpoly_zero]
  simp only [Fintype.card_finset_len, Fintype.card_fin, Nat.choose_zero_right, pow_one]

/-- The inductive step of Lemma 7.3. -/
theorem charpoly_johnson_step (j N : ℕ) (hj : 2 * (j + 1) ≤ N)
    (ih : (adj (𝕜 := ℂ) (johnsonGraph j N)).charpoly
      = ∏ i ∈ Finset.range (j + 1),
          (Polynomial.X - Polynomial.C (theta N j i)) ^ (jmult N i)) :
    (adj (𝕜 := ℂ) (johnsonGraph (j+1) N)).charpoly
      = ∏ i ∈ Finset.range (j + 2),
          (Polynomial.X - Polynomial.C (theta N (j+1) i)) ^ (jmult N i) := by
  have hshift : ∀ i ∈ Finset.range (j + 1),
      theta N j i + (((N - (2*j+1) : ℕ)) : ℂ) = theta N (j+1) i :=
    fun i _ => theta_shift hj
  have hlast : (Polynomial.X + Polynomial.C ((j : ℂ) + 1))
        ^ (Nat.choose N (j+1) - Nat.choose N j)
      = (Polynomial.X - Polynomial.C (theta N (j+1) (j+1))) ^ (jmult N (j+1)) := by
    rw [theta_self, jmult_succ, map_neg, sub_neg_eq_add]
    push_cast
    ring
  have hsplit : ∏ i ∈ Finset.range (j + 2),
        (Polynomial.X - Polynomial.C (theta N (j+1) i)) ^ (jmult N i)
      = (∏ i ∈ Finset.range (j + 1),
          (Polynomial.X - Polynomial.C (theta N (j+1) i)) ^ (jmult N i))
        * (Polynomial.X - Polynomial.C (theta N (j+1) (j+1))) ^ (jmult N (j+1)) := by
    rw [show j + 2 = (j + 1) + 1 from by ring, Finset.prod_range_succ]
  rw [charpoly_johnson_succ j N hj, ih, prod_shift _ _ _ _ _ hshift, hsplit, ← hlast]
  ring

/-- **Lemma 7.3** (Johnson eigenvalues) in "one parameter" form: the characteristic
polynomial of `J(j,N)` is the product of `(X - θᵢ)^{mᵢ}` over `0 ≤ i ≤ j`. -/
theorem charpoly_johnson_eq (j N : ℕ) (hj : 2 * j ≤ N) :
    (adj (𝕜 := ℂ) (johnsonGraph j N)).charpoly
      = ∏ i ∈ Finset.range (j + 1),
          (Polynomial.X - Polynomial.C (theta N j i)) ^ (jmult N i) := by
  revert hj
  induction j with
  | zero =>
    intro _
    rw [charpoly_johnson_zero, Finset.prod_range_one, theta_zero, jmult_zero]
    simp
  | succ j ih => intro hj; exact charpoly_johnson_step j N hj (ih (by omega))

/-- **Lemma 7.3.**  The characteristic polynomial of the Johnson graph `J(D,N)`
(`1 ≤ D ≤ N/2`) is `∏ᵢ (X - θᵢ)^{mᵢ}` with `θᵢ = (N-D-i)(D-i) - i` and
`mᵢ = C(N,i) - C(N,i-1)` (with `m₀ = 1`). -/
theorem johnson_eigenvalues (D N : ℕ) (hD : 1 ≤ D) (hDN : 2 * D ≤ N) :
    (adj (𝕜 := ℂ) (johnsonGraph D N)).charpoly
      = ∏ i ∈ Finset.range (D + 1),
          (Polynomial.X - Polynomial.C ((((N : ℤ) - D - i) * ((D : ℤ) - i) - i : ℤ) : ℂ))
            ^ (Nat.choose N i - (if i = 0 then 0 else Nat.choose N (i - 1))) := by
  rw [charpoly_johnson_eq D N hDN]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  show (Polynomial.X - Polynomial.C (theta N D i)) ^ (jmult N i)
      = (Polynomial.X - Polynomial.C ((((N : ℤ) - D - i) * ((D : ℤ) - i) - i : ℤ) : ℂ))
          ^ (jmult N i)
  rw [theta_int]

/-! ## The thin condition (Chapter 7) -/

/-- **(TH)**: every irreducible `T(x)`-module is thin.

A `T(x)`-module is by definition stable under `T(x)`, so stability is part of the
quantification: `IsIrreducible` (Definition 1.7) does not itself imply that a subspace
is stable, and the variant quantifying over *all* subspaces having no proper nonzero
stable subspace is false (`K₄` at a vertex satisfies (C) below, while `span{𝟙, e_y}` is
vacuously "irreducible" with a two-dimensional `E₁*`-image; see the report). -/
def IsThinAt (G : SimpleGraph X) (x : X) : Prop :=
  ∀ W : Submodule ℂ (X → ℂ),
    IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W →
      IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W → ThinModule G x W

/-- **(C)**: `E*_iTE*_i` is commutative for every `i`. -/
def IsCommutativeSubconstituent (G : SimpleGraph X) (x : X) : Prop :=
  ∀ i : ℕ, ∀ a ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
    ∀ b ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
      (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)
          * (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
        = (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
          * (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)

/-- **(S)**: `E*_iTE*_i` is symmetric for every `i`. -/
def IsSymmetricSubconstituent (G : SimpleGraph X) (x : X) : Prop :=
  ∀ i : ℕ, ∀ a ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra,
    (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)ᵀ
      = subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i

/-- **(G)**: for all `y`, `z` with `∂(x,y) = ∂(x,z)` there is an automorphism `σ`
of `Γ` with `σx = x` and `σy = z`. -/
def HasPropertyG (G : SimpleGraph X) (x : X) : Prop :=
  ∀ y z : X, G.dist x y = G.dist x z →
    ∃ σ : X ≃ X, (∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) ∧ σ x = x ∧ σ y = z ∧ σ z = y

/-- Scalar times matrix, entrywise. -/
theorem smul_mapMatrix_mul {c : ℂ} (M N : Matrix X X ℝ) :
    (c • (algebraMap ℝ ℂ).mapMatrix M) * (algebraMap ℝ ℂ).mapMatrix N
      = c • (algebraMap ℝ ℂ).mapMatrix (M * N) := by
  ext y z
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, map_mul, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem mapMatrix_mul_smul {c : ℂ} (M N : Matrix X X ℝ) :
    (algebraMap ℝ ℂ).mapMatrix M * (c • (algebraMap ℝ ℂ).mapMatrix N)
      = c • (algebraMap ℝ ℂ).mapMatrix (M * N) := by
  ext y z
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, map_mul, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem smul_mapMatrix_mul_smul {c d : ℂ} (M N : Matrix X X ℝ) :
    (c • (algebraMap ℝ ℂ).mapMatrix M) * (d • (algebraMap ℝ ℂ).mapMatrix N)
      = (c * d) • (algebraMap ℝ ℂ).mapMatrix (M * N) := by
  ext y z
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, map_mul, Matrix.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/- **(S) ⇒ (C)**: a symmetric `E*_iTE*_i` is commutative, because
`ab = (ab)* = b*a* = ba` for self-adjoint `a`, `b`.  (Stated over `ℝ`: the
`ℂ`-version is unsatisfiable, `I • E₀*` being a non-self-adjoint element of
`T(x)`; the `ℂ`-conclusion is derived from the real one by decomposing
`a = u + I • v`.) -/
set_option maxHeartbeats 1600000 in
theorem symmetric_implies_commutative {G : SimpleGraph X} {x : X}
    (hS : IsSymmetricSubconstituent G x) : IsCommutativeSubconstituent G x := by
  intro i a ha b hb
  -- Every element of the complex subconstituent algebra is `u + I • v` with
  -- `u`, `v` real elements (the generators are real and the property is
  -- preserved under the algebra operations).
  have hdecomp : ∀ a ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
      ∃ u v : Matrix X X ℝ,
        u ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra ∧
        v ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra ∧
        a = ((algebraMap ℝ ℂ).mapMatrix u) + Complex.I • ((algebraMap ℝ ℂ).mapMatrix v) := by
    intro a ha
    have hEq : (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra
        = Algebra.adjoin ℂ (({adj (𝕜 := ℂ) G} ∪ Set.range (subconst (𝕜 := ℂ) G x)) ∪
            star ({adj (𝕜 := ℂ) G} ∪ Set.range (subconst (𝕜 := ℂ) G x))) :=
      StarAlgebra.adjoin_toSubalgebra _ _
    rw [hEq] at ha
    induction ha using Algebra.adjoin_induction with
    | mem b hb =>
        rcases hb with hb | hb
        · rcases hb with hb | hb
          · rw [Set.mem_singleton_iff] at hb
            rw [hb]
            refine ⟨adj (𝕜 := ℝ) G, 0, adj_mem_subconstituentAlgebra G x, Subalgebra.zero_mem _, ?_⟩
            ext y z
            by_cases h : G.Adj y z <;> simp [adj_apply, h]
          · obtain ⟨j, hj⟩ := hb
            rw [← hj]
            refine ⟨subconst (𝕜 := ℝ) G x j, 0, subconst_mem_subconstituentAlgebra G x j,
              Subalgebra.zero_mem _, ?_⟩
            ext y z
            by_cases hyz : y = z
            · subst hyz
              by_cases h : G.dist x y = j <;> simp [subconst_apply, h]
            · simp [subconst_apply, hyz]
        · rw [Set.mem_star] at hb
          rcases hb with hb | hb
          · rw [Set.mem_singleton_iff] at hb
            rw [← star_star b, hb, star_adj]
            refine ⟨adj (𝕜 := ℝ) G, 0, adj_mem_subconstituentAlgebra G x,
              Subalgebra.zero_mem _, ?_⟩
            ext y z
            by_cases h : G.Adj y z <;> simp [adj_apply, h]
          · obtain ⟨j, hj⟩ := hb
            rw [← star_star b, ← hj, star_subconst]
            refine ⟨subconst (𝕜 := ℝ) G x j, 0, subconst_mem_subconstituentAlgebra G x j,
              Subalgebra.zero_mem _, ?_⟩
            ext y z
            by_cases hyz : y = z
            · subst hyz
              by_cases h : G.dist x y = j <;> simp [subconst_apply, h]
            · simp [subconst_apply, hyz]
    | algebraMap c =>
        refine ⟨(algebraMap ℝ (Matrix X X ℝ)) c.re, (algebraMap ℝ (Matrix X X ℝ)) c.im,
          Subalgebra.algebraMap_mem _ _, Subalgebra.algebraMap_mem _ _, ?_⟩
        ext y z
        by_cases hyz : y = z
        · subst hyz
          simp only [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
            RingHom.mapMatrix_apply, map_apply, Matrix.smul_apply, Pi.smul_apply,
            smul_eq_mul, Matrix.add_apply, map_add, map_mul, Matrix.one_apply, one_mul,
            mul_one]
          rw [mul_comm]
          exact (Complex.re_add_im c).symm
        · simp [Matrix.algebraMap_eq_diagonal, RingHom.mapMatrix_apply, hyz]
    | add p q _ _ hp hq =>
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := hp
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := hq
        refine ⟨u₁ + u₂, v₁ + v₂, Subalgebra.add_mem _ hu₁ hu₂, Subalgebra.add_mem _ hv₁ hv₂, ?_⟩
        ext y z
        simp only [map_add, Matrix.add_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
        ring
    | mul p q _ _ hp hq =>
        obtain ⟨u₁, v₁, hu₁, hv₁, rfl⟩ := hp
        obtain ⟨u₂, v₂, hu₂, hv₂, rfl⟩ := hq
        have hm₁ : u₁ * u₂ - v₁ * v₂ ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra :=
          Subalgebra.sub_mem _ (Subalgebra.mul_mem _ hu₁ hu₂) (Subalgebra.mul_mem _ hv₁ hv₂)
        have hm₂ : u₁ * v₂ + v₁ * u₂ ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra :=
          Subalgebra.add_mem _ (Subalgebra.mul_mem _ hu₁ hv₂) (Subalgebra.mul_mem _ hv₁ hu₂)
        refine ⟨u₁ * u₂ - v₁ * v₂, u₁ * v₂ + v₁ * u₂, hm₁, hm₂, ?_⟩
        simp only [Matrix.mul_add, Matrix.add_mul]
        rw [smul_mapMatrix_mul, mapMatrix_mul_smul, smul_mapMatrix_mul_smul, ← map_mul,
          show Complex.I * Complex.I = -1 from by simp, neg_one_smul,
          map_sub, map_add, smul_add]
        abel
  -- the complex compression of a real matrix is the mapMatrix of the real one
  have hmapE : (algebraMap ℝ ℂ).mapMatrix (subconst (𝕜 := ℝ) G x i)
      = subconst (𝕜 := ℂ) G x i := by
    ext y z
    by_cases hyz : y = z
    · subst hyz
      by_cases h : G.dist x y = i <;> simp [subconst_apply, h]
    · simp [subconst_apply, hyz]
  have hcomp : ∀ u : Matrix X X ℝ,
      u ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra →
      subconst (𝕜 := ℂ) G x i * ((algebraMap ℝ ℂ).mapMatrix u) * subconst (𝕜 := ℂ) G x i
        = (algebraMap ℝ ℂ).mapMatrix (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i) := by
    intro u _
    rw [← hmapE, ← map_mul ((algebraMap ℝ ℂ).mapMatrix),
      ← map_mul ((algebraMap ℝ ℂ).mapMatrix)]
  have hcompSmul : ∀ (c : ℂ) (u : Matrix X X ℝ),
      u ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra →
      subconst (𝕜 := ℂ) G x i * (c • (algebraMap ℝ ℂ).mapMatrix u)
          * subconst (𝕜 := ℂ) G x i
        = c • (algebraMap ℝ ℂ).mapMatrix
            (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i) := by
    intro c u hu
    rw [← hmapE, mapMatrix_mul_smul, smul_mapMatrix_mul]
  -- real compressions commute pairwise: the compressed matrices are symmetric
  -- by (S), and so is their product (it is again a compression), so the
  -- transpose argument applies to the product itself
  have hpair : ∀ u v : Matrix X X ℝ,
      u ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra →
      v ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra →
      (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
          * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)
        = (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)
            * (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i) := by
    intro u v hu hv
    have hmem : u * subconst (𝕜 := ℝ) G x i * v
        ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra :=
      Subalgebra.mul_mem _
        (Subalgebra.mul_mem _ hu (subconst_mem_subconstituentAlgebra G x i)) hv
    have hsym := hS i _ hmem
    have hE2 : subconst (𝕜 := ℝ) G x i * subconst (𝕜 := ℝ) G x i
        = subconst (𝕜 := ℝ) G x i := subconst_mul_self G x i
    have hEE : ∀ w : Matrix X X ℝ, subconst (𝕜 := ℝ) G x i
          * (subconst (𝕜 := ℝ) G x i * w) = subconst (𝕜 := ℝ) G x i * w := by
      intro w
      rw [← Matrix.mul_assoc, hE2]
    have hl : (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
          * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)
        = subconst (𝕜 := ℝ) G x i * (u * subconst (𝕜 := ℝ) G x i * v)
            * subconst (𝕜 := ℝ) G x i := by
      simp only [Matrix.mul_assoc]
      rw [hEE]
    have hS₁ : (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)ᵀ
        = subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i := hS i u hu
    have hT₁ : (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)ᵀ
        = subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i := hS i v hv
    have hST : ((subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
          * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i))ᵀ
        = (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
            * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i) := by
      rw [hl, hsym, ← hl]
    calc (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
          * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)
        = ((subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)
            * (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i))ᵀ := hST.symm
      _ = (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)ᵀ
            * (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i)ᵀ :=
              Matrix.transpose_mul _ _
      _ = (subconst (𝕜 := ℝ) G x i * v * subconst (𝕜 := ℝ) G x i)
            * (subconst (𝕜 := ℝ) G x i * u * subconst (𝕜 := ℝ) G x i) := by
              rw [hT₁, hS₁]
  obtain ⟨a₁, a₂, ha₁, ha₂, rfl⟩ := hdecomp a ha
  obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := hdecomp b hb
  have hp₁ := hpair a₁ b₁ ha₁ hb₁
  have hp₂ := hpair a₁ b₂ ha₁ hb₂
  have hp₃ := hpair a₂ b₁ ha₂ hb₁
  have hp₄ := hpair a₂ b₂ ha₂ hb₂
  have hcompAdd : ∀ (P Q : Matrix X X ℂ),
      subconst (𝕜 := ℂ) G x i * P * subconst (𝕜 := ℂ) G x i
        + subconst (𝕜 := ℂ) G x i * Q * subconst (𝕜 := ℂ) G x i
      = subconst (𝕜 := ℂ) G x i * (P + Q) * subconst (𝕜 := ℂ) G x i := by
    intro P Q
    rw [Matrix.mul_add, Matrix.add_mul]
  have hsplit : subconst (𝕜 := ℂ) G x i
      * ((algebraMap ℝ ℂ).mapMatrix a₁ + Complex.I • (algebraMap ℝ ℂ).mapMatrix a₂)
      * subconst (𝕜 := ℂ) G x i
    = subconst (𝕜 := ℂ) G x i * (algebraMap ℝ ℂ).mapMatrix a₁ * subconst (𝕜 := ℂ) G x i
      + subconst (𝕜 := ℂ) G x i
          * (Complex.I • (algebraMap ℝ ℂ).mapMatrix a₂) * subconst (𝕜 := ℂ) G x i :=
    (hcompAdd _ _).symm
  have hsplit' : subconst (𝕜 := ℂ) G x i
      * ((algebraMap ℝ ℂ).mapMatrix b₁ + Complex.I • (algebraMap ℝ ℂ).mapMatrix b₂)
      * subconst (𝕜 := ℂ) G x i
    = subconst (𝕜 := ℂ) G x i * (algebraMap ℝ ℂ).mapMatrix b₁ * subconst (𝕜 := ℂ) G x i
      + subconst (𝕜 := ℂ) G x i
          * (Complex.I • (algebraMap ℝ ℂ).mapMatrix b₂) * subconst (𝕜 := ℂ) G x i :=
    (hcompAdd _ _).symm
  rw [hsplit, hsplit']
  rw [hcomp a₁ ha₁, hcomp b₁ hb₁, hcompSmul Complex.I a₂ ha₂, hcompSmul Complex.I b₂ hb₂]
  have expand : ∀ S T U V : Matrix X X ℝ,
      ((algebraMap ℝ ℂ).mapMatrix S + Complex.I • (algebraMap ℝ ℂ).mapMatrix T)
          * ((algebraMap ℝ ℂ).mapMatrix U + Complex.I • (algebraMap ℝ ℂ).mapMatrix V)
        = (algebraMap ℝ ℂ).mapMatrix (S * U - T * V)
          + Complex.I • (algebraMap ℝ ℂ).mapMatrix (S * V + T * U) := by
    intro S T U V
    simp only [Matrix.mul_add, Matrix.add_mul]
    rw [smul_mapMatrix_mul, mapMatrix_mul_smul, smul_mapMatrix_mul_smul, ← map_mul,
      show Complex.I * Complex.I = -1 from by simp, neg_one_smul,
      map_sub, map_add, smul_add]
    abel
  rw [expand, expand]
  rw [hp₁, hp₂, hp₃, hp₄]
  simp only [map_add]
  module

/-- Stability under a subalgebra is preserved by binary intersections. -/
theorem isStable_inf {𝕜 : Type*} [RCLike 𝕜] {T : Subalgebra 𝕜 (Matrix X X 𝕜)}
    {W W' : Submodule 𝕜 (X → 𝕜)} (hW : IsStable T W) (hW' : IsStable T W') :
    IsStable T (W ⊓ W') := by
  intro a ha v hv
  rw [Submodule.mem_inf] at hv ⊢
  exact ⟨hW a ha v hv.1, hW' a ha v hv.2⟩

/-- A subspace meets its orthogonal complement trivially. -/
theorem inf_orthCompl_eq_bot (W : Submodule ℂ (X → ℂ)) : W ⊓ orthCompl W = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf, mem_orthCompl] at hv
  exact star_dotProduct_self_eq_zero (hv.2 v hv.1)

/-- Splitting a vector of `W` along a subspace `U ≤ W` and its orthogonal
complement. -/
theorem exists_add_mem_inf_orthCompl {U W : Submodule ℂ (X → ℂ)} (hUW : U ≤ W) {v : X → ℂ}
    (hv : v ∈ W) : ∃ u ∈ U, ∃ u' ∈ W ⊓ orthCompl U, v = u + u' := by
  obtain ⟨h, hhU, horth⟩ := exists_orthogonal_decomp (W := U) v
  refine ⟨h, hhU, v - h, ?_, by abel⟩
  exact Submodule.mem_inf.mpr
    ⟨Submodule.sub_mem _ hv (hUW hhU), by rw [mem_orthCompl]; exact horth⟩

/-- Passing to the orthogonal complement inside a larger space strictly lowers
the dimension. -/
theorem finrank_inf_orthCompl_lt {U W : Submodule ℂ (X → ℂ)} (hUW : U ≤ W) (hU : U ≠ ⊥) :
    Module.finrank ℂ ↥(W ⊓ orthCompl U) < Module.finrank ℂ ↥W := by
  refine Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left ?_)
  intro hEq
  obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
  have huW' : u ∈ W ⊓ orthCompl U := by rw [hEq]; exact hUW huU
  have huOrth : u ∈ orthCompl U := (Submodule.mem_inf.mp huW').2
  exact hu0 (star_dotProduct_self_eq_zero (mem_orthCompl.mp huOrth u huU))

/-- On a subspace of dimension at most one, an endomorphism fixing it acts by a
scalar. -/
theorem exists_forall_mulVec_eq_smul {U : Submodule ℂ (X → ℂ)}
    (hU : Module.finrank ℂ ↥U ≤ 1) {M : Matrix X X ℂ} (hM : ∀ y ∈ U, M *ᵥ y ∈ U) :
    ∃ c : ℂ, ∀ y ∈ U, M *ᵥ y = c • y := by
  rcases eq_or_ne U ⊥ with hbot | hne
  · refine ⟨0, ?_⟩
    intro y hy
    have hy0 : y = 0 := by simpa [hbot] using hy
    rw [hy0, mulVec_zero, smul_zero]
  · obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    have hspanU : Submodule.span ℂ ({u} : Set (X → ℂ)) ≤ U :=
      Submodule.span_le.mpr (by simpa using huU)
    have hfr : Module.finrank ℂ ↥(Submodule.span ℂ ({u} : Set (X → ℂ))) = 1 :=
      finrank_span_singleton (K := ℂ) (V := X → ℂ) hu0
    have hspanEq : Submodule.span ℂ ({u} : Set (X → ℂ)) = U := by
      refine Submodule.eq_of_le_of_finrank_le hspanU ?_
      rw [hfr]; exact hU
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspanEq ▸ hM u huU)
    refine ⟨c, ?_⟩
    intro y hy
    obtain ⟨e, he⟩ := Submodule.mem_span_singleton.mp (hspanEq ▸ hy)
    rw [← he, mulVec_smul, ← hc, smul_smul, smul_smul, mul_comm]

/-- An endomorphism of a nonzero finite-dimensional complex subspace has an
eigenvector. -/
theorem exists_eigen_smul {U : Submodule ℂ (X → ℂ)} (hne : U ≠ ⊥) {M : Matrix X X ℂ}
    (hM : ∀ y ∈ U, M *ᵥ y ∈ U) :
    ∃ c : ℂ, ∃ w ∈ U, w ≠ 0 ∧ M *ᵥ w = c • w := by
  haveI : Nontrivial ↥U := Submodule.nontrivial_iff_ne_bot.mpr hne
  let g : Module.End ℂ ↥U :=
    { toFun := fun v => ⟨M *ᵥ (v : X → ℂ), hM v v.2⟩
      map_add' := by
        intro v w
        ext x
        simp only [mulVec_add, Pi.add_apply, Submodule.coe_add]
      map_smul' := by
        intro a v
        ext x
        simp only [mulVec_smul, Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply,
          smul_eq_mul] }
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
  rw [Module.End.hasEigenvalue_iff] at hc
  obtain ⟨w, hwE, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  have h2 : (g w : X → ℂ) = c • (w : X → ℂ) := by
    have := Module.End.mem_eigenspace_iff.mp hwE
    rw [this]
    rfl
  exact ⟨c, w, w.2, fun h => hw0 (Subtype.ext h), h2⟩

/-- On the range of `Eᵢ*`, the operator `Eᵢ* t Eᵢ*` acts as `Eᵢ* t`. -/
theorem estar_mulVec_of_mem {G : SimpleGraph X} {x : X} {i : ℕ} (t : Matrix X X ℂ)
    {y : X → ℂ} (hy : subconst (𝕜 := ℂ) G x i *ᵥ y = y) :
    (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ y
      = subconst (𝕜 := ℂ) G x i *ᵥ (t *ᵥ y) := by
  calc (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ y
      = (subconst (𝕜 := ℂ) G x i * t) *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ y) :=
        (Matrix.mulVec_mulVec y (subconst (𝕜 := ℂ) G x i * t)
          (subconst (𝕜 := ℂ) G x i)).symm
    _ = (subconst (𝕜 := ℂ) G x i * t) *ᵥ y := by rw [hy]
    _ = subconst (𝕜 := ℂ) G x i *ᵥ (t *ᵥ y) :=
        (Matrix.mulVec_mulVec y (subconst (𝕜 := ℂ) G x i) t).symm

/-- `Eᵢ* t Eᵢ*` does not see whether its argument has already been projected. -/
theorem estar_mulVec_mulVec_self {G : SimpleGraph X} {x : X} {i : ℕ} (t : Matrix X X ℂ)
    (v : X → ℂ) :
    (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ v
      = (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i)
          *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v) := by
  have h1 : (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ v
      = subconst (𝕜 := ℂ) G x i *ᵥ (t *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v)) := by
    calc (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ v
        = (subconst (𝕜 := ℂ) G x i * t) *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v) :=
          (Matrix.mulVec_mulVec v (subconst (𝕜 := ℂ) G x i * t)
            (subconst (𝕜 := ℂ) G x i)).symm
      _ = subconst (𝕜 := ℂ) G x i *ᵥ (t *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v)) :=
          (Matrix.mulVec_mulVec (subconst (𝕜 := ℂ) G x i *ᵥ v)
            (subconst (𝕜 := ℂ) G x i) t).symm
  have hFF : subconst (𝕜 := ℂ) G x i *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v)
      = subconst (𝕜 := ℂ) G x i *ᵥ v := by
    rw [Matrix.mulVec_mulVec, subconst_mul_self]
  have h2 : (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i)
        *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v)
      = subconst (𝕜 := ℂ) G x i *ᵥ (t *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ v)) :=
    estar_mulVec_of_mem t hFF
  rw [h1, h2]

/-- `U` is stable under all the operators `Eᵢ*(x) t Eᵢ*(x)` with `t ∈ T(x)`: the
notion of a module over the algebra `Eᵢ*T(x)Eᵢ*` used in Theorem 7.4. -/
def IsEstarStable (G : SimpleGraph X) (x : X) (i : ℕ) (U : Submodule ℂ (X → ℂ)) : Prop :=
  ∀ t ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
    ∀ y ∈ U, (subconst (𝕜 := ℂ) G x i * t * subconst (𝕜 := ℂ) G x i) *ᵥ y ∈ U

/-- **Theorem 7.4, Claim 1.** If `W` is an irreducible `T(x)`-module then `Eᵢ*W` is an
irreducible `Eᵢ*T(x)Eᵢ*`-module. -/
theorem subconstImage_le_of_isEstarStable {G : SimpleGraph X} {x : X} {i : ℕ}
    {W : Submodule ℂ (X → ℂ)}
    (hWstab : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hWirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    {U : Submodule ℂ (X → ℂ)} (hUsub : U ≤ subconstImage (𝕜 := ℂ) G x i W)
    (hUstab : IsEstarStable G x i U) (hU0 : U ≠ ⊥) :
    subconstImage (𝕜 := ℂ) G x i W ≤ U := by
  have hFWle : subconstImage (𝕜 := ℂ) G x i W ≤ W := by
    intro y hy
    obtain ⟨w, hw, rfl⟩ := mem_matImage.mp hy
    exact hWstab _ (subconst_mem_subconstituentAlgebra G x i) w hw
  set S₀ : Submodule ℂ (X → ℂ) :=
    Submodule.span ℂ {z : X → ℂ | ∃ t ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
      ∃ u ∈ U, t *ᵥ u = z} with hS₀
  have hS₀le : S₀ ≤ W := by
    rw [hS₀, Submodule.span_le]
    rintro z ⟨t, ht, u, hu, rfl⟩
    exact hWstab t ht u (hFWle (hUsub hu))
  have hS₀stab : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra S₀ := by
    intro t ht z hz
    rw [hS₀] at hz ⊢
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨s, hs, u, hu, rfl⟩ := hz
        rw [Matrix.mulVec_mulVec]
        exact Submodule.subset_span ⟨t * s, mul_mem ht hs, u, hu, rfl⟩
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [mulVec_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c y _ hy => rw [mulVec_smul]; exact Submodule.smul_mem _ c hy
  have hS₀ne : S₀ ≠ ⊥ := by
    obtain ⟨u, huU, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    have hmem : u ∈ S₀ := by
      rw [hS₀]
      exact Submodule.subset_span ⟨1, Subalgebra.one_mem _, u, huU, one_mulVec u⟩
    intro hbot
    rw [hbot] at hmem
    exact hu0 (by simpa using hmem)
  have hS₀eq : S₀ = W := hWirr.2 S₀ hS₀le hS₀stab hS₀ne
  have hkey : ∀ z ∈ S₀, subconst (𝕜 := ℂ) G x i *ᵥ z ∈ U := by
    intro z hz
    rw [hS₀] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
        obtain ⟨t, ht, u, hu, rfl⟩ := hz
        have hFu : subconst (𝕜 := ℂ) G x i *ᵥ u = u := subconst_mulVec_self (hUsub hu)
        have h := hUstab t ht u hu
        rw [estar_mulVec_of_mem t hFu] at h
        exact h
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [mulVec_add]; exact Submodule.add_mem _ h₁ h₂
    | smul c y _ hy => rw [mulVec_smul]; exact Submodule.smul_mem _ c hy
  intro y hy
  obtain ⟨w, hw, rfl⟩ := mem_matImage.mp hy
  exact hkey w (hS₀eq ▸ hw)

/-- **Theorem 7.4, Claim 2.** Over a commutative `Eᵢ*T(x)Eᵢ*`, an irreducible
`Eᵢ*T(x)Eᵢ*`-module is one-dimensional. -/
theorem finrank_le_one_of_isEstarStable {G : SimpleGraph X} {x : X} {i : ℕ}
    (hcomm : ∀ a ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
      ∀ b ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
        (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
          = (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i))
    {U : Submodule ℂ (X → ℂ)} (hUne : U ≠ ⊥) (hUstab : IsEstarStable G x i U)
    (hUirr : ∀ U' : Submodule ℂ (X → ℂ), U' ≤ U → IsEstarStable G x i U' → U' ≠ ⊥ → U' = U) :
    Module.finrank ℂ ↥U ≤ 1 := by
  have hscalar : ∀ a ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra,
      ∃ c : ℂ, ∀ y ∈ U,
        (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i) *ᵥ y = c • y := by
    intro a ha
    obtain ⟨c, w, hwU, hw0, hweig⟩ := exists_eigen_smul hUne (hUstab a ha)
    refine ⟨c, ?_⟩
    set E : Submodule ℂ (X → ℂ) :=
      U ⊓ Module.End.eigenspace
        (Matrix.mulVecLin (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)) c
      with hEdef
    have hwE : w ∈ E := by
      refine Submodule.mem_inf.mpr ⟨hwU, ?_⟩
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      exact hweig
    have hEne : E ≠ ⊥ := by
      intro hbot
      rw [Submodule.eq_bot_iff] at hbot
      exact hw0 (hbot w hwE)
    have hEstab : IsEstarStable G x i E := by
      intro t ht y hy
      obtain ⟨hyU, hyE⟩ := Submodule.mem_inf.mp hy
      have hyMeig :
          (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i) *ᵥ y = c • y := by
        rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hyE
        exact hyE
      refine Submodule.mem_inf.mpr ⟨hUstab t ht y hyU, ?_⟩
      rw [Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply]
      rw [Matrix.mulVec_mulVec, hcomm a ha t ht, ← Matrix.mulVec_mulVec, hyMeig, mulVec_smul]
    have hEeq : E = U := hUirr E inf_le_left hEstab hEne
    intro y hy
    have hyE : y ∈ E := by rw [hEeq]; exact hy
    rw [hEdef, Submodule.mem_inf, Module.End.mem_eigenspace_iff, Matrix.mulVecLin_apply] at hyE
    exact hyE.2
  obtain ⟨w, hwU, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hUne
  have hspanU : Submodule.span ℂ ({w} : Set (X → ℂ)) ≤ U :=
    Submodule.span_le.mpr (by simpa using hwU)
  have hspanStab : IsEstarStable G x i (Submodule.span ℂ ({w} : Set (X → ℂ))) := by
    intro t ht y hy
    obtain ⟨c, hc⟩ := hscalar t ht
    induction hy using Submodule.span_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        rw [hz, hc w hwU]
        exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton w))
    | zero => rw [mulVec_zero]; exact Submodule.zero_mem _
    | add y₁ y₂ _ _ h₁ h₂ => rw [mulVec_add]; exact Submodule.add_mem _ h₁ h₂
    | smul e y _ hy => rw [mulVec_smul]; exact Submodule.smul_mem _ e hy
  have hspanNe : Submodule.span ℂ ({w} : Set (X → ℂ)) ≠ ⊥ := by
    intro hbot
    have hmem : w ∈ (⊥ : Submodule ℂ (X → ℂ)) :=
      hbot ▸ Submodule.subset_span (Set.mem_singleton w)
    exact hw0 (by simpa using hmem)
  have hEq : Submodule.span ℂ ({w} : Set (X → ℂ)) = U := hUirr _ hspanU hspanStab hspanNe
  rw [← hEq, finrank_span_singleton (K := ℂ) (V := X → ℂ) hw0]


/-- **(TH) ⇒ (C)** of Theorem 7.4, in the form in which the proof is carried out: if
every stable irreducible `T(x)`-module is thin then `Eᵢ*T(x)Eᵢ*` is commutative for
every `i`.  (Thinness is used only for stable irreducible modules.) -/
theorem commutativeSubconstituent_of_thin {G : SimpleGraph X} {x : X}
    (hTH : ∀ W : Submodule ℂ (X → ℂ),
      IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W →
      IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W → ThinModule G x W) :
    IsCommutativeSubconstituent G x := by
  intro i a ha b hb
  have key : ∀ (n : ℕ) (W : Submodule ℂ (X → ℂ)), Module.finrank ℂ ↥W = n →
      IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W →
      ∀ v ∈ W,
        ((subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)) *ᵥ v
        = ((subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)) *ᵥ v := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro W hWn hWstab v hv
      by_cases hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W
      · -- `W` irreducible: thinness makes `Eᵢ*W` a line
        have hFW1 : Module.finrank ℂ ↥(subconstImage (𝕜 := ℂ) G x i W) ≤ 1 :=
          (hTH W hWstab hirr) i
        have hFWle : subconstImage (𝕜 := ℂ) G x i W ≤ W := by
          intro y hy
          obtain ⟨w, hw, rfl⟩ := mem_matImage.mp hy
          exact hWstab _ (subconst_mem_subconstituentAlgebra G x i) w hw
        have hMU : ∀ y ∈ subconstImage (𝕜 := ℂ) G x i W,
            (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i) *ᵥ y ∈
              subconstImage (𝕜 := ℂ) G x i W := by
          intro y hy
          rw [estar_mulVec_of_mem a (subconst_mulVec_self hy)]
          exact mem_matImage.mpr ⟨a *ᵥ y, hWstab a ha y (hFWle hy), rfl⟩
        have hNU : ∀ y ∈ subconstImage (𝕜 := ℂ) G x i W,
            (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i) *ᵥ y ∈
              subconstImage (𝕜 := ℂ) G x i W := by
          intro y hy
          rw [estar_mulVec_of_mem b (subconst_mulVec_self hy)]
          exact mem_matImage.mpr ⟨b *ᵥ y, hWstab b hb y (hFWle hy), rfl⟩
        obtain ⟨c, hc⟩ := exists_forall_mulVec_eq_smul hFW1 hMU
        obtain ⟨d, hd⟩ := exists_forall_mulVec_eq_smul hFW1 hNU
        have hFv : subconst (𝕜 := ℂ) G x i *ᵥ v ∈ subconstImage (𝕜 := ℂ) G x i W :=
          mem_matImage.mpr ⟨v, hv, rfl⟩
        have hNv : (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i) *ᵥ v
            = d • (subconst (𝕜 := ℂ) G x i *ᵥ v) := by
          rw [estar_mulVec_mulVec_self b v]
          exact hd _ hFv
        have hMv : (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i) *ᵥ v
            = c • (subconst (𝕜 := ℂ) G x i *ᵥ v) := by
          rw [estar_mulVec_mulVec_self a v]
          exact hc _ hFv
        have hL : ((subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)) *ᵥ v
            = (d * c) • (subconst (𝕜 := ℂ) G x i *ᵥ v) := by
          rw [← Matrix.mulVec_mulVec, hNv, mulVec_smul, hc _ hFv, smul_smul]
        have hR : ((subconst (𝕜 := ℂ) G x i * b * subconst (𝕜 := ℂ) G x i)
            * (subconst (𝕜 := ℂ) G x i * a * subconst (𝕜 := ℂ) G x i)) *ᵥ v
            = (d * c) • (subconst (𝕜 := ℂ) G x i *ᵥ v) := by
          rw [← Matrix.mulVec_mulVec, hMv, mulVec_smul, hd _ hFv, smul_smul, mul_comm c d]
        rw [hL, hR]
      · -- `W` reducible: split `W = U ⊕ (W ⊓ Uᗮ)` along a proper stable submodule
        by_cases hbot : W = ⊥
        · have hv0 : v = 0 := by simpa [hbot] using hv
          rw [hv0, mulVec_zero, mulVec_zero]
        · have h2 : ¬ (∀ U : Submodule ℂ (X → ℂ), U ≤ W →
              IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra U → U ≠ ⊥ →
              U = W) := by
            intro hconj
            exact hirr ⟨hbot, hconj⟩
          push_neg at h2
          obtain ⟨U, hUW, hUstab, hUno, hUneW⟩ := h2
          have hUfr : Module.finrank ℂ ↥U < n := by
            have hlt : U < W := lt_of_le_of_ne hUW hUneW
            have := Submodule.finrank_lt_finrank_of_lt hlt
            rw [hWn] at this
            exact this
          have hW'fr : Module.finrank ℂ ↥(W ⊓ orthCompl U) < n := by
            have := finrank_inf_orthCompl_lt hUW hUno
            rw [hWn] at this
            exact this
          have hW'stab : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra
              (W ⊓ orthCompl U) :=
            isStable_inf hWstab (isStable_orthCompl_subconstituent hUstab)
          obtain ⟨u, huU, u', hu', hvu'⟩ := exists_add_mem_inf_orthCompl hUW hv
          rw [hvu', mulVec_add, mulVec_add,
            ih _ hUfr U rfl hUstab u huU, ih _ hW'fr _ rfl hW'stab u' hu']
  refine Matrix.mulVec_injective (funext fun v => ?_)
  exact key (Module.finrank ℂ ↥(⊤ : Submodule ℂ (X → ℂ))) ⊤ rfl (isStable_top _) v
    (Submodule.mem_top)

/-- **(C) ⇒ (TH)** of Theorem 7.4, for a *stable* (i.e. genuine) irreducible
`T(x)`-module `W`: if `Eᵢ*T(x)Eᵢ*` is commutative for every `i`, then every
subconstituent `Eᵢ*W` of `W` is at most one-dimensional. -/
theorem commutativeSubconstituent_implies_thin {G : SimpleGraph X} {x : X}
    (hC : IsCommutativeSubconstituent G x) {W : Submodule ℂ (X → ℂ)}
    (hWstab : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hWirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W) :
    ThinModule G x W := by
  intro i
  by_cases hFW : subconstImage (𝕜 := ℂ) G x i W = ⊥
  · rw [hFW, finrank_bot]
    exact zero_le_one
  · refine finrank_le_one_of_isEstarStable (i := i) (hC i) hFW ?_ ?_
    · -- `Eᵢ*W` is stable under `Eᵢ*T(x)Eᵢ*`
      intro t ht y hy
      obtain ⟨w, hw, rfl⟩ := mem_matImage.mp hy
      have hFw : subconst (𝕜 := ℂ) G x i *ᵥ w ∈ W :=
        hWstab _ (subconst_mem_subconstituentAlgebra G x i) w hw
      have hFF : subconst (𝕜 := ℂ) G x i *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ w)
          = subconst (𝕜 := ℂ) G x i *ᵥ w := by
        rw [Matrix.mulVec_mulVec, subconst_mul_self]
      rw [estar_mulVec_of_mem t hFF]
      exact mem_matImage.mpr ⟨t *ᵥ (subconst (𝕜 := ℂ) G x i *ᵥ w),
        hWstab t ht _ hFw, rfl⟩
    · -- Claim 1: `Eᵢ*W` is irreducible over `Eᵢ*T(x)Eᵢ*`
      intro U' hU'sub hU'stab hU'ne
      exact le_antisymm hU'sub
        (subconstImage_le_of_isEstarStable hWstab hWirr hU'sub hU'stab hU'ne)

/-- **(C) ⇒ (TH)** and **(TH) ⇒ (C)** (Theorem 7.4, first equivalence). -/
theorem thin_iff_commutative {G : SimpleGraph X} {x : X} :
    IsThinAt G x ↔ IsCommutativeSubconstituent G x :=
  ⟨commutativeSubconstituent_of_thin,
    fun h W hW hI => commutativeSubconstituent_implies_thin h hW hI⟩

/-- `(TH) ⇔ (C)` with `(TH)` written out, without reference to `IsThinAt`.  The
quantification is over genuine `T(x)`-modules, i.e. over *stable* irreducible
subspaces: on subspaces that are not stable the condition would be false
(see the docstring of `IsThinAt`). -/
theorem thin_iff_commutative_explicit {G : SimpleGraph X} {x : X} :
    (∀ W : Submodule ℂ (X → ℂ),
        IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W →
        IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W →
        ThinModule G x W) ↔
      IsCommutativeSubconstituent G x :=
  thin_iff_commutative

/- **(G) ⇒ (S)** (Theorem 7.4), proved below via permutation matrices. -/
/-! ### Permutation matrices and graph automorphisms -/

/-- The permutation matrix of a vertex bijection `σ` (over `ℝ`). -/
def permMatrix (σ : X ≃ X) : Matrix X X ℝ := Matrix.of fun u v => if σ u = v then 1 else 0

theorem permMatrix_apply (σ : X ≃ X) (u v : X) :
    permMatrix σ u v = if σ u = v then 1 else 0 := rfl

theorem permMatrix_mul_apply_left (σ : X ≃ X) (M : Matrix X X ℝ) (y z : X) :
    (permMatrix σ * M) y z = M (σ y) z := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ y)]
  · rw [permMatrix_apply, if_pos rfl, one_mul]
  · intro u _ hu
    rw [permMatrix_apply, if_neg (fun h => hu h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ (σ y)) h

theorem permMatrix_mul_apply_right (σ : X ≃ X) (M : Matrix X X ℝ) (y z : X) :
    (M * permMatrix σ) y z = M y (σ.symm z) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ.symm z)]
  · rw [permMatrix_apply, if_pos (σ.apply_symm_apply z), mul_one]
  · intro v _ hv
    rw [permMatrix_apply, if_neg (fun h => hv (by rw [← Equiv.symm_apply_apply σ v, h])),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ (σ.symm z)) h

theorem permMatrix_mul_cancel (σ : X ≃ X) :
    permMatrix σ * permMatrix σ.symm = 1 := by
  ext a b
  rw [permMatrix_mul_apply_left, permMatrix_apply, Matrix.one_apply,
    Equiv.symm_apply_apply]

theorem permMatrix_mul_cancel' (σ : X ≃ X) :
    permMatrix σ.symm * permMatrix σ = 1 := by
  have h := permMatrix_mul_cancel σ.symm
  rwa [Equiv.symm_symm] at h

/-- Conjugating a matrix by a permutation matrix reindexes the entries. -/
theorem permMatrix_conj (σ : X ≃ X) (M : Matrix X X ℝ) (y z : X) :
    (permMatrix σ * M * permMatrix σ.symm) y z = M (σ y) (σ z) := by
  rw [Matrix.mul_assoc, permMatrix_mul_apply_left, permMatrix_mul_apply_right,
    Equiv.symm_symm]

/-- A bijection preserving adjacency transports walks. -/
def walk_map {G : SimpleGraph X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) {u v : X} (p : G.Walk u v) :
    G.Walk (σ u) (σ v) :=
  match p with
  | .nil => .nil
  | .cons hw p => .cons ((h _ _).1 hw) (walk_map h p)

theorem walk_map_length {G : SimpleGraph X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) {u v : X} (p : G.Walk u v) :
    (walk_map h p).length = p.length := by
  induction p with
  | nil => rfl
  | cons hw p ih => simp only [walk_map, SimpleGraph.Walk.length_cons, ih]

/-- A graph automorphism (as an adjacency-preserving bijection) preserves distances. -/
theorem dist_map {G : SimpleGraph X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) (u v : X) :
    G.dist (σ u) (σ v) = G.dist u v := by
  have hsymm : ∀ a b, G.Adj a b ↔ G.Adj (σ.symm a) (σ.symm b) := by
    intro a b
    have h2 := (h (σ.symm a) (σ.symm b)).symm
    rw [σ.apply_symm_apply a, σ.apply_symm_apply b] at h2
    exact h2
  have hle : ∀ (τ : X ≃ X), (∀ u v, G.Adj u v ↔ G.Adj (τ u) (τ v)) →
      ∀ a b, G.dist (τ a) (τ b) ≤ G.dist a b := by
    intro τ hτ a b
    by_cases hreach : G.Reachable a b
    · obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
      have hle2 := SimpleGraph.dist_le (walk_map hτ p)
      rw [walk_map_length hτ p, hp] at hle2
      exact hle2
    · have hnr : ¬ G.Reachable (τ a) (τ b) := by
        intro hreach2
        obtain ⟨w⟩ := hreach2
        have hτs : ∀ x y, G.Adj x y ↔ G.Adj (τ.symm x) (τ.symm y) := by
          intro x y
          have h4 := (hτ (τ.symm x) (τ.symm y)).symm
          rw [τ.apply_symm_apply x, τ.apply_symm_apply y] at h4
          exact h4
        refine hreach ⟨?_⟩
        rw [← τ.symm_apply_apply a, ← τ.symm_apply_apply b]
        exact walk_map hτs w
      rw [SimpleGraph.dist_eq_zero_of_not_reachable hreach,
        SimpleGraph.dist_eq_zero_of_not_reachable hnr]
  have h1 := hle σ h u v
  have h2 : G.dist u v ≤ G.dist (σ u) (σ v) := by
    have h3 := hle σ.symm hsymm (σ u) (σ v)
    rwa [σ.symm_apply_apply u, σ.symm_apply_apply v] at h3
  exact le_antisymm h1 h2

theorem permMatrix_comm_adj {G : SimpleGraph X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) :
    permMatrix σ * adj (𝕜 := ℝ) G = adj (𝕜 := ℝ) G * permMatrix σ := by
  ext y z
  rw [permMatrix_mul_apply_left, permMatrix_mul_apply_right]
  conv_lhs => rw [show z = σ (σ.symm z) from (σ.apply_symm_apply z).symm]
  rw [adj_apply, adj_apply]
  by_cases hAdj : G.Adj y (σ.symm z)
  · rw [if_pos ((h y (σ.symm z)).mp hAdj), if_pos hAdj]
  · rw [if_neg (fun hh => hAdj ((h y (σ.symm z)).mpr hh)), if_neg hAdj]

theorem permMatrix_comm_subconst {G : SimpleGraph X} {x : X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) (hx : σ x = x) (j : ℕ) :
    permMatrix σ * subconst (𝕜 := ℝ) G x j
      = subconst (𝕜 := ℝ) G x j * permMatrix σ := by
  have hdist : ∀ w, G.dist x (σ w) = G.dist x w := by
    intro w
    rw [← dist_map h x w, hx]
  have hconj : permMatrix σ * subconst (𝕜 := ℝ) G x j * permMatrix σ.symm
      = subconst (𝕜 := ℝ) G x j := by
    ext y z
    rw [permMatrix_conj, subconst_apply, subconst_apply]
    by_cases hyz : y = z
    · subst hyz
      rw [hdist y]
      simp
    · rw [if_neg (fun hh => hyz (σ.injective hh)), if_neg hyz]
  calc permMatrix σ * subconst (𝕜 := ℝ) G x j
      = permMatrix σ * subconst (𝕜 := ℝ) G x j * permMatrix σ.symm * permMatrix σ := by
        rw [Matrix.mul_assoc, permMatrix_mul_cancel', mul_one]
    _ = subconst (𝕜 := ℝ) G x j * permMatrix σ := by rw [hconj]

theorem permMatrix_comm_subconstituentAlgebra {G : SimpleGraph X} {x : X} {σ : X ≃ X}
    (h : ∀ u v, G.Adj u v ↔ G.Adj (σ u) (σ v)) (hx : σ x = x)
    (a : Matrix X X ℝ)
    (ha : a ∈ (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra) :
    permMatrix σ * a = a * permMatrix σ := by
  have hgen : ∀ b ∈ ({adj (𝕜 := ℝ) G} ∪ Set.range (subconst (𝕜 := ℝ) G x)
        ∪ star ({adj (𝕜 := ℝ) G} ∪ Set.range (subconst (𝕜 := ℝ) G x)) : Set (Matrix X X ℝ)),
      permMatrix σ * b = b * permMatrix σ := by
    rintro b hb
    rcases hb with (hb | hb) | hb
    · rw [Set.mem_singleton_iff] at hb
      rw [hb]
      exact permMatrix_comm_adj h
    · obtain ⟨j, rfl⟩ := hb
      exact permMatrix_comm_subconst h hx j
    · rw [Set.mem_star] at hb
      rcases hb with hb | hb
      · rw [Set.mem_singleton_iff] at hb
        rw [← star_star b, hb, star_adj]
        exact permMatrix_comm_adj h
      · obtain ⟨j, hj⟩ := hb
        rw [← star_star b, ← hj, star_subconst]
        exact permMatrix_comm_subconst h hx j
  have hEq : (subconstituentAlgebra (𝕜 := ℝ) G x).toSubalgebra
      = Algebra.adjoin ℝ (({adj (𝕜 := ℝ) G} ∪ Set.range (subconst (𝕜 := ℝ) G x)) ∪
          star ({adj (𝕜 := ℝ) G} ∪ Set.range (subconst (𝕜 := ℝ) G x))) :=
    StarAlgebra.adjoin_toSubalgebra _ _
  rw [hEq] at ha
  induction ha using Algebra.adjoin_induction with
  | mem b hb => exact hgen b hb
  | algebraMap r =>
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, one_mul,
        mul_one]
  | add b c _ _ hb hc => rw [Matrix.mul_add, Matrix.add_mul, hb, hc]
  | mul b c _ _ hb hc =>
      calc permMatrix σ * (b * c) = permMatrix σ * b * c := (Matrix.mul_assoc _ _ _).symm
        _ = b * permMatrix σ * c := by rw [hb]
        _ = b * (permMatrix σ * c) := Matrix.mul_assoc _ _ _
        _ = b * (c * permMatrix σ) := by rw [hc]
        _ = b * c * permMatrix σ := (Matrix.mul_assoc _ _ _).symm

/-- The support of a compression: the `yz` entry of `E*ᵢ a E*ᵢ`. -/
theorem subconst_mul_mul_subconst_apply {G : SimpleGraph X} {x : X} {i : ℕ}
    (a : Matrix X X ℝ) (y z : X) :
    (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) y z
      = (if G.dist x y = i then 1 else 0) * a y z * (if G.dist x z = i then 1 else 0) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  rw [Finset.sum_eq_single y]
  · rw [subconst_apply, if_pos rfl, Matrix.mul_apply]
    rw [Finset.sum_eq_single z]
    · rw [subconst_apply, if_pos rfl]
      ring
    · intro k _ hk
      rw [subconst_apply, if_neg (fun h => hk h), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ z) h
  · intro k _ hk
    rw [subconst_apply, if_neg (fun h => hk h.symm), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ y) h

theorem property_g_implies_symmetric {G : SimpleGraph X} {x : X}
    (hG : HasPropertyG G x) : IsSymmetricSubconstituent G x := by
  intro i a ha
  ext y z
  rw [Matrix.transpose_apply]
  by_cases hy : G.dist x y = i
  · by_cases hz : G.dist x z = i
    · obtain ⟨σ, haut, hx, hyz, hzy⟩ := hG y z (by rw [hy, hz])
      have ha' := permMatrix_comm_subconstituentAlgebra haut hx a ha
      have hE := permMatrix_comm_subconst haut hx i
      have hM : permMatrix σ * (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
          = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) * permMatrix σ := by
        calc permMatrix σ * (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
            = (permMatrix σ * subconst (𝕜 := ℝ) G x i) * a
              * subconst (𝕜 := ℝ) G x i := by
                rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]
          _ = (subconst (𝕜 := ℝ) G x i * permMatrix σ) * a
              * subconst (𝕜 := ℝ) G x i := by rw [hE]
          _ = subconst (𝕜 := ℝ) G x i * (permMatrix σ * a)
              * subconst (𝕜 := ℝ) G x i := by rw [← Matrix.mul_assoc]
          _ = subconst (𝕜 := ℝ) G x i * (a * permMatrix σ)
              * subconst (𝕜 := ℝ) G x i := by rw [ha']
          _ = subconst (𝕜 := ℝ) G x i * a
              * (permMatrix σ * subconst (𝕜 := ℝ) G x i) := by
                rw [← Matrix.mul_assoc, Matrix.mul_assoc]
          _ = subconst (𝕜 := ℝ) G x i * a
              * (subconst (𝕜 := ℝ) G x i * permMatrix σ) := by rw [hE]
          _ = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) * permMatrix σ := by
                rw [← Matrix.mul_assoc]
      have hconj : permMatrix σ * (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
            * permMatrix σ.symm
          = subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i := by
        calc permMatrix σ * (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
              * permMatrix σ.symm
            = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) * permMatrix σ
              * permMatrix σ.symm := by rw [hM]
        _ = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
              * (permMatrix σ * permMatrix σ.symm) := by rw [← Matrix.mul_assoc]
        _ = subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i := by
              rw [permMatrix_mul_cancel, mul_one]
      calc (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) z y
          = (permMatrix σ * (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i)
              * permMatrix σ.symm) z y := by rw [hconj]
        _ = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) (σ z) (σ y) :=
              permMatrix_conj σ _ z y
        _ = (subconst (𝕜 := ℝ) G x i * a * subconst (𝕜 := ℝ) G x i) y z := by
              rw [hzy, hyz]
    · rw [subconst_mul_mul_subconst_apply, subconst_mul_mul_subconst_apply]
      simp [hy, hz]
  · rw [subconst_mul_mul_subconst_apply, subconst_mul_mul_subconst_apply]
    simp [hy]

end Terwilliger
