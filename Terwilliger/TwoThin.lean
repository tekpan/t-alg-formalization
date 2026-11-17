/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.Thin
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
# Lemma 12.2 (ii), (iii): the eigenvalue identities for two thin modules

Section E of the Lemma 12.2 campaign.  Let `Γ = (X, E)` be a finite simple graph
with adjacency matrix `A = adj G`, let `W` be a thin irreducible `T(x)`-module and
`W'` a thin irreducible `T(y)`-module, pick `0 ≠ w ∈ W`, `0 ≠ w' ∈ W'`, and let
`E_θ = spectralProj A θ` be the spectral projection of `A` for the eigenvalue `θ`.
Assume the two projection formulas of Lemma 12.2 (i):

`proj_W w' = (‖w'‖/‖w‖) • p'(A) w`,   `proj_{W'} w = (‖w‖/‖w'‖) • p(A) w'`.

Then, writing `S = ⟨E_θ w, E_θ w'⟩`:

* `S = (‖w'‖/‖w‖) p'(θ) ‖E_θ w‖² = (‖w‖/‖w'‖) conj(p(θ)) ‖E_θ w'‖²`
  (Lemma 12.2 (ii)), and
* `p(θ) p'(θ)` is real and lies in `[0,1]` at every eigenvalue at which both
  spectral measures are nonzero (Lemma 12.2 (iii)).

## Deviations from the campaign notes §4E

The notes' version of (ii) is **false**: its two right-hand sides are missing the
normalising factor `‖w‖‖w'‖`, and the conjugate in the first conjunct is on the
wrong factor.  With the notes' own convention `⟨u,v⟩ = star u ⬝ᵥ v`
(conjugate-linear in the *first* slot) one computes

`⟨E_θ w, p'(A) w⟩ = ⟨star(p'(A)) E_θ w, w⟩ = ⟨conj(p'(θ)) E_θ w, w⟩ = p'(θ) ‖E_θ w‖²`,

because `⟨c • v, w⟩ = conj c * ⟨v, w⟩`.  Similarly, moving `p(A)` onto the other
side of the pairing produces a conjugate on `p(θ)`.  Concretely, for `G = K₂`
with vertices `a ∼ b`, `x = a`, `y = b`, `W = W' = ℂ²` (thin, irreducible,
`r = r' = 0`, `d = d' = 1`), `w = 2 e_a`, `w' = e_b`, `θ = 1`, `p = p' = X`:
`E_1 = (A+1)/2`, so `E_1 w = e_a + e_b`, `E_1 w' = (e_a + e_b)/2`, and the left
side of (ii) is `1`; the notes' right-hand side gives `(‖E_1 w‖²/‖w‖²)·conj(p'(1)) = (2/4)·1 = 1/2`.

The corrected statements below differ from §4E by (a) the factor
`((vnorm w * vnorm w' : ℝ) : ℂ)` on each right-hand side, (b) the conjugate in
each equality placed where the pairing puts it — the first conjunct carries
`p'.eval θ`, the second `star (p.eval θ)` — and (c) the two missing membership
hypotheses `w ∈ W`, `w' ∈ W'`, without which `E_θ w ∈ W` (and hence the use of
`hprojW`) is not available; the notes' `hstable`/`hstable'` are otherwise unused,
which is the tell-tale sign that they were meant to be there.  Conclusion (iii)
is unchanged and is proved here byte-exactly as stated in §4E.

## What this file consumes from the other sections

`Basic`: `star_adj`, `boseMesner_le_subconstituentAlgebra`,
`subconst_mem_subconstituentAlgebra`, `mem_matImage`, `IsStable`.
`Hermitian` (A): `star_mulVec_dotProduct`, `star_dotProduct_symm`,
`star_dotProduct_self_real`, `star_dotProduct_self_re`,
`star_dotProduct_self_eq_zero`, `vnorm_eq_zero`, `abs_star_dotProduct_le_vnorm`.
`Spectral` (B): `isEigenvalue_iff_mem_eigFinset`, `spectralProj_mul_self`,
`star_spectralProj`, `aeval_mul_spectralProj`, and — load-bearing —
`spectralProj_mem_span : spectralProj A θ ∈ Algebra.adjoin ℂ ({A} : Set _)`,
which is what makes `E_θ w ∈ W` available.

Nothing else.  In particular this file never unfolds `spectralProj`, so section B
is free to define it however it likes as long as the lemmas above hold; and it
uses no part of `Thin.lean`, which it imports only to sit in the right place in
the build chain.  Verified: built against section A's and section B's *real*
files, `#print axioms lemma12_2_ii` and `lemma12_2_iii` return only
`[propext, Classical.choice, Quot.sound]`.
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Auxiliary lemmas -/

/-- `Eᵢ*(x)` keeps the `i`-th subconstituent and kills everything else. -/
theorem l122_subconst_apply (G : SimpleGraph X) (x : X) (i : ℕ) (u : X → ℂ) (z : X) :
    (subconst (𝕜 := ℂ) G x i *ᵥ u) z = if G.dist x z = i then u z else 0 := by
  rw [mulVec, dotProduct, Finset.sum_eq_single z]
  · rw [subconst_apply, if_pos rfl]
    by_cases h : G.dist x z = i <;> simp [h]
  · intro b _ hb
    rw [subconst_apply, if_neg (Ne.symm hb), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ z) h

theorem l122_vnorm_ne_zero_of_ne {u : X → ℂ} (h : u ≠ 0) : vnorm u ≠ 0 :=
  fun h0 => h (vnorm_eq_zero.mp h0)

/-- A polynomial in `A` lies in the subconstituent algebra `T(x)`. -/
theorem l122_aeval_mem {G : SimpleGraph X} (x : X) (q : Polynomial ℂ) :
    (Polynomial.aeval (adj (𝕜 := ℂ) G)) q ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra := by
  rw [Polynomial.aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun i _ => ?_
  exact Subalgebra.smul_mem _ (Subalgebra.pow_mem _ (adj_mem_subconstituentAlgebra G x) i) _

/-- The `A`-action of a sum of scalar multiples of polynomials. -/
theorem l122_aeval_sum_apply (G : SimpleGraph X) (c : ℕ → ℂ) (p : ℕ → Polynomial ℂ)
    (s : Finset ℕ) (w : X → ℂ) :
    ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (∑ j ∈ s, Polynomial.C (c j) * p j)) *ᵥ w
      = ∑ j ∈ s, c j • (((Polynomial.aeval (adj (𝕜 := ℂ) G)) (p j)) *ᵥ w) := by
  rw [map_sum, sum_mulVec]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
    smul_mulVec]

/-! ## The Gram-Schmidt data of the projection -/

/-- The coefficient `α j = ⟪w_j, w'⟫/⟪w_j, w_j⟫` of the projection of `w'` onto
the orthogonal basis `w j = thinVec G x r w j`. -/
noncomputable def l122coef (G : SimpleGraph X) (x : X) (r : ℕ) (w w' : X → ℂ) (j : ℕ) : ℂ :=
  (star (thinVec G x r w j) ⬝ᵥ w') / (star (thinVec G x r w j) ⬝ᵥ thinVec G x r w j)

/-- The polynomial `∑_j α_j p_j` whose `A`-action on `w` is the projection. -/
noncomputable def l122poly (a xs : ℕ → ℂ) (G : SimpleGraph X) (x : X) (r : ℕ)
    (w w' : X → ℂ) (d : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (d + 1), Polynomial.C (l122coef G x r w w' j) * thinPoly a xs j

/-- The projection of `w'` onto `W = span{w_0, …, w_d}`. -/
noncomputable def l122proj (G : SimpleGraph X) (x : X) (r : ℕ) (w w' : X → ℂ) (d : ℕ) : X → ℂ :=
  ∑ j ∈ Finset.range (d + 1), l122coef G x r w w' j • thinVec G x r w j

/-! ## Lemma 12.2 (i), one direction -/

/-- **Lemma 12.2 (i), one direction.**  The projection of `w'` onto `W` is
`p'(A)(‖w'‖/‖w‖)w`; moreover `r ≤ Δ + r'` (otherwise `W` and `W'` would be
orthogonal, contradicting the hypothesis). -/
theorem l122_aux {G : SimpleGraph X} (hG : G.Connected) {x y : X}
    {W W' : Submodule ℂ (X → ℂ)} {r r' d d' : ℕ} {a a' xs xs' : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA (𝕜 := ℂ) G x W r a)
    (hx : HasThinX (𝕜 := ℂ) G x W r xs)
    (hstable' : IsStable (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hirr' : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hthin' : ThinModule (𝕜 := ℂ) G y W') (hend' : IsEndpoint (𝕜 := ℂ) G y W' r')
    (hdiam' : IsDiameter (𝕜 := ℂ) G y W' r' d') (ha' : HasThinA (𝕜 := ℂ) G y W' r' a')
    (hx' : HasThinX (𝕜 := ℂ) G y W' r' xs')
    {w w' : X → ℂ} (hw : w ∈ subconstImage (𝕜 := ℂ) G x r W) (hwne : w ≠ 0)
    (hw' : w' ∈ subconstImage (𝕜 := ℂ) G y r' W') (hw'ne : w' ≠ 0)
    (hnotorth : ∃ u ∈ W, ∃ v ∈ W', star u ⬝ᵥ v ≠ 0) :
    r ≤ G.dist x y + r' ∧
      ∃ p' : Polynomial ℂ, p' ≠ 0 ∧ p'.natDegree ≤ d ∧
        p'.natDegree + r ≤ G.dist x y + r' ∧
        (∀ u ∈ W, star u ⬝ᵥ (w' - ((vnorm w' / vnorm w : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p' *ᵥ w)) = 0) ∧
        (((vnorm w' / vnorm w : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p' *ᵥ w) ∈ W) := by
  -- the thin structure of `W` and of `W'`
  obtain ⟨hne, hmem, hvan, hspan, -, -⟩ :=
    thin_module_structure (G := G) (x := x) (W := W) (r := r) (d := d) (a := a) (xs := xs)
      (w₀ := w) hstable hirr hthin hend hdiam ha hx hw hwne
  obtain ⟨hne', hmem', hvan', hspan', -, -⟩ :=
    thin_module_structure (G := G) (x := y) (W := W') (r := r') (d := d') (a := a')
      (xs := xs') (w₀ := w') hstable' hirr' hthin' hend' hdiam' ha' hx' hw' hw'ne
  -- the supports of `w j` and of `w'` are the spheres of radius `r + j` and `r'`
  have hsupp : ∀ (j : ℕ) (z : X), thinVec G x r w j z ≠ 0 → G.dist x z = r + j := by
    intro j z hz
    by_contra hd
    refine hz ?_
    rw [thinVec, l122_subconst_apply]
    simp [hd]
  have hsupp' : ∀ z : X, w' z ≠ 0 → G.dist y z = r' := by
    intro z hz
    obtain ⟨t, -, ht⟩ := mem_matImage.mp hw'
    by_contra hd
    refine hz ?_
    rw [← ht, l122_subconst_apply]
    simp [hd]
  -- `thinVec` lands in `W`
  have hsubW : ∀ i : ℕ, subconstImage (𝕜 := ℂ) G x i W ≤ W := by
    intro i v hv
    obtain ⟨u, hu, rfl⟩ := mem_matImage.mp hv
    exact hstable _ (subconst_mem_subconstituentAlgebra G x i) u hu
  have hmemW : ∀ j, thinVec G x r w j ∈ W := fun j => hsubW _ (hmem j)
  -- the `w j` are pairwise orthogonal, and nonzero for `j ≤ d`
  have horth : ∀ j k : ℕ, j ≠ k → star (thinVec G x r w j) ⬝ᵥ thinVec G x r w k = 0 := by
    intro j k hjk
    exact star_dotProduct_subconstImage_zero (i := r + j) (j := r + k) (by omega) (hmem j) (hmem k)
  have hself : ∀ j, j ≤ d → star (thinVec G x r w j) ⬝ᵥ thinVec G x r w j ≠ 0 := by
    intro j hj h0
    exact hne j hj (star_dotProduct_self_eq_zero h0)
  -- the defining property of the coefficients
  have hcoefmul : ∀ j, j ∈ Finset.range (d + 1) →
      l122coef G x r w w' j * (star (thinVec G x r w j) ⬝ᵥ thinVec G x r w j)
        = star (thinVec G x r w j) ⬝ᵥ w' := by
    intro j hj
    rw [l122coef]
    exact div_mul_cancel₀ _ (hself j (by simpa using hj))
  -- `w' - proj` is orthogonal to every `w j`
  have hkey : ∀ j : ℕ, star (thinVec G x r w j) ⬝ᵥ (w' - l122proj G x r w w' d) = 0 := by
    intro j
    rw [dotProduct_sub, l122proj, dotProduct_sum]
    by_cases hj : j ∈ Finset.range (d + 1)
    · rw [Finset.sum_eq_single_of_mem j hj]
      · rw [dotProduct_smul, smul_eq_mul, hcoefmul j hj, sub_self]
      · intro k _ hkj
        rw [dotProduct_smul, smul_eq_mul, horth j k (Ne.symm hkj), mul_zero]
    · have hdj : d < j := by
        simp only [Finset.mem_range, not_lt] at hj
        omega
      rw [hvan j hdj]
      simp
  -- hence `w' - proj` is orthogonal to `W`
  have hWle : W ≤ Submodule.span ℂ (Set.range fun j : ℕ => thinVec G x r w j) := by
    intro v hv
    obtain ⟨c, hc⟩ := hspan v hv
    rw [hc]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  have horthW : ∀ u ∈ W, star u ⬝ᵥ (w' - l122proj G x r w w' d) = 0 := by
    intro u hu
    refine Submodule.span_induction (p := fun z _ =>
      star z ⬝ᵥ (w' - l122proj G x r w w' d) = 0) ?_ ?_ ?_ ?_ (hWle hu)
    · intro s hs
      obtain ⟨j, rfl⟩ := hs
      exact hkey j
    · simp
    · intro p q _ _ hp hq
      rw [star_add, add_dotProduct, hp, hq, add_zero]
    · intro c p _ hp
      rw [star_smul, smul_dotProduct, hp, smul_zero]
  -- `proj` lies in `W`
  have hprojW : l122proj G x r w w' d ∈ W := by
    rw [l122proj]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hmemW j)
  -- `w'` pairs nontrivially with `W`
  have hnontriv : ∃ z ∈ W, star z ⬝ᵥ w' ≠ 0 := by
    obtain ⟨u, huW, v, hvW', huv⟩ := hnotorth
    obtain ⟨c, hc⟩ := hspan' v hvW'
    rw [hc, dotProduct_sum] at huv
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    refine huv (Finset.sum_eq_zero fun i hi => ?_)
    have hi' : i ≤ d' + 1 := by
      simp only [Finset.mem_range] at hi
      omega
    have hithin : thinVec G y r' w' i
        = ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a' xs' i)) *ᵥ w' :=
      (thinPoly_aeval (G := G) (x := y) (W := W') (r := r') (d := d') (a := a') (xs := xs')
        (w₀ := w') hstable' hirr' hthin' hend' hdiam' ha' hx' hw' hw'ne i hi').symm
    have hmemM : (star ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (thinPoly a' xs' i))) *ᵥ u ∈ W :=
      hstable _ (StarMemClass.star_mem (s := subconstituentAlgebra (𝕜 := ℂ) G x)
        (l122_aeval_mem x (thinPoly a' xs' i))) u huW
    rw [dotProduct_smul, smul_eq_mul, hithin, star_mulVec_dotProduct, hcon _ hmemM, mul_zero]
  have hprojne : l122proj G x r w w' d ≠ 0 := by
    intro h0
    obtain ⟨z, hzW, hz⟩ := hnontriv
    refine hz ?_
    have h := horthW z hzW
    rw [h0, sub_zero] at h
    exact h
  -- the polynomial computes the projection
  have hPeval : ((Polynomial.aeval (adj (𝕜 := ℂ) G)) (l122poly a xs G x r w w' d)) *ᵥ w
      = l122proj G x r w w' d := by
    rw [l122poly, l122_aeval_sum_apply, l122proj]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [thinPoly_aeval (G := G) (x := x) (W := W) (r := r) (d := d) (a := a) (xs := xs)
      (w₀ := w) hstable hirr hthin hend hdiam ha hx hw hwne j (by
        simp only [Finset.mem_range] at hj
        omega)]
  have hPne : l122poly a xs G x r w w' d ≠ 0 := by
    intro h0
    refine hprojne ?_
    rw [← hPeval, h0]
    simp
  -- the coefficients vanish beyond `Δ + r' - r`
  have hcoefzero : ∀ j : ℕ, j ≤ d → G.dist x y + r' < r + j →
      l122coef G x r w w' j = 0 := by
    intro j _ hlt
    rw [l122coef, div_eq_zero_iff]
    left
    refine star_dotProduct_disjoint fun z => ?_
    by_cases h1 : thinVec G x r w j z = 0
    · exact Or.inl h1
    · right
      by_contra h2
      exact not_dist_eq_of_lt hG (i := r + j) (j := r') hlt z ⟨hsupp j z h1, hsupp' z h2⟩
  -- degree bounds
  have hPdeg : (l122poly a xs G x r w w' d).natDegree ≤ d := by
    rw [l122poly]
    refine Polynomial.natDegree_sum_le_of_forall_le (s := Finset.range (d + 1)) (n := d)
      (f := fun j => Polynomial.C (l122coef G x r w w' j) * thinPoly a xs j) fun j hj => ?_
    refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
    rw [(thinPoly_monic_degree a xs j).2]
    simp only [Finset.mem_range] at hj
    omega
  have hcoeff : ∀ m : ℕ, G.dist x y + r' < m + r →
      (l122poly a xs G x r w w' d).coeff m = 0 := by
    intro m hm
    rw [l122poly, Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Polynomial.coeff_C_mul]
    simp only [Finset.mem_range] at hj
    rcases lt_trichotomy j m with h | h | h
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [(thinPoly_monic_degree a xs j).2]; omega),
        mul_zero]
    · rw [← h]
      have h1 : (thinPoly a xs j).coeff j = 1 := by
        have h2 := (thinPoly_monic_degree a xs j).1.coeff_natDegree
        rwa [(thinPoly_monic_degree a xs j).2] at h2
      rw [h1, mul_one, hcoefzero j (by omega) (by omega)]
    · rw [hcoefzero j (by omega) (by omega), zero_mul]
  have hrle : r ≤ G.dist x y + r' := by
    by_contra hcon
    simp only [not_le] at hcon
    refine hPne ?_
    rw [l122poly]
    refine Finset.sum_eq_zero fun j hj => ?_
    simp only [Finset.mem_range] at hj
    rw [hcoefzero j (by omega) (by omega)]
    simp
  have hpdegsharp : (l122poly a xs G x r w w' d).natDegree + r ≤ G.dist x y + r' := by
    have hle : (l122poly a xs G x r w w' d).natDegree ≤ G.dist x y + r' - r := by
      rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
      intro m hm
      exact hcoeff m (by omega)
    omega
  -- the scalar `(‖w'‖/‖w‖)·(‖w‖/‖w'‖)` is `1`
  have hscal : ((vnorm w' / vnorm w : ℝ) : ℂ) * ((vnorm w / vnorm w' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, Complex.ofReal_inj]
    have h1 : vnorm w ≠ 0 := l122_vnorm_ne_zero_of_ne hwne
    have h2 : vnorm w' ≠ 0 := l122_vnorm_ne_zero_of_ne hw'ne
    field_simp
  refine ⟨hrle, ((vnorm w / vnorm w' : ℝ) : ℂ) • l122poly a xs G x r w w' d, ?_, ?_, ?_, ?_, ?_⟩
  · refine smul_ne_zero ?_ hPne
    rw [Complex.ofReal_ne_zero]
    exact div_ne_zero (l122_vnorm_ne_zero_of_ne hwne) (l122_vnorm_ne_zero_of_ne hw'ne)
  · exact le_trans (Polynomial.natDegree_smul_le _ _) hPdeg
  · have h := Polynomial.natDegree_smul_le ((vnorm w / vnorm w' : ℝ) : ℂ)
      (l122poly a xs G x r w w' d)
    omega
  · intro u hu
    have h1 := horthW u hu
    have hp'eval : ((Polynomial.aeval (adj (𝕜 := ℂ) G))
        (((vnorm w / vnorm w' : ℝ) : ℂ) • l122poly a xs G x r w w' d)) *ᵥ w
        = ((vnorm w / vnorm w' : ℝ) : ℂ) • l122proj G x r w w' d := by
      rw [map_smul, smul_mulVec, hPeval]
    rw [hp'eval, smul_smul, hscal, one_smul]
    exact h1
  · have hp'eval : ((Polynomial.aeval (adj (𝕜 := ℂ) G))
        (((vnorm w / vnorm w' : ℝ) : ℂ) • l122poly a xs G x r w w' d)) *ᵥ w
        = ((vnorm w / vnorm w' : ℝ) : ℂ) • l122proj G x r w w' d := by
      rw [map_smul, smul_mulVec, hPeval]
    rw [hp'eval, smul_smul, hscal, one_smul]
    exact hprojW

/-! ## Lemma 12.2 (i) -/

/-- **Lemma 12.2 (i).**  If the thin irreducible `T(y)`-module `W'` is not
orthogonal to the thin irreducible `T(x)`-module `W`, then the orthogonal
projection of `w'` onto `W` is `p'(A) (‖w'‖/‖w‖) w` for a nonzero polynomial
`p'` of degree `≤ min(d, Δ - r + r')`, and symmetrically. -/
theorem lemma12_2_i {G : SimpleGraph X} (hG : G.Connected) {x y : X}
    {W W' : Submodule ℂ (X → ℂ)} {r r' d d' : ℕ} {a a' xs xs' : ℕ → ℂ}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hirr : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hthin : ThinModule (𝕜 := ℂ) G x W) (hend : IsEndpoint (𝕜 := ℂ) G x W r)
    (hdiam : IsDiameter (𝕜 := ℂ) G x W r d) (ha : HasThinA (𝕜 := ℂ) G x W r a)
    (hx : HasThinX (𝕜 := ℂ) G x W r xs)
    (hstable' : IsStable (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hirr' : IsIrreducible (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hthin' : ThinModule (𝕜 := ℂ) G y W') (hend' : IsEndpoint (𝕜 := ℂ) G y W' r')
    (hdiam' : IsDiameter (𝕜 := ℂ) G y W' r' d') (ha' : HasThinA (𝕜 := ℂ) G y W' r' a')
    (hx' : HasThinX (𝕜 := ℂ) G y W' r' xs')
    {w w' : X → ℂ} (hw : w ∈ subconstImage (𝕜 := ℂ) G x r W) (hwne : w ≠ 0)
    (hw' : w' ∈ subconstImage (𝕜 := ℂ) G y r' W') (hw'ne : w' ≠ 0)
    (hnotorth : ∃ u ∈ W, ∃ v ∈ W', star u ⬝ᵥ v ≠ 0) :
    ∃ p p' : Polynomial ℂ, p ≠ 0 ∧ p' ≠ 0 ∧
      (p'.natDegree ≤ d ∧ p'.natDegree + r ≤ G.dist x y + r') ∧
      (p.natDegree ≤ d' ∧ p.natDegree + r' ≤ G.dist x y + r) ∧
      (∀ u ∈ W, star u ⬝ᵥ
        (w' - ((vnorm w' / vnorm w : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p' *ᵥ w)) = 0) ∧
      (∀ u ∈ W', star u ⬝ᵥ
        (w - ((vnorm w / vnorm w' : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p *ᵥ w')) = 0) ∧
      (((vnorm w' / vnorm w : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p' *ᵥ w) ∈ W) ∧
      (((vnorm w / vnorm w' : ℝ) : ℂ) •
          ((Polynomial.aeval (adj (𝕜 := ℂ) G)) p *ᵥ w') ∈ W') := by
  -- the symmetric form of the non-orthogonality hypothesis
  have hnotorth' : ∃ u ∈ W', ∃ v ∈ W, star u ⬝ᵥ v ≠ 0 := by
    obtain ⟨u, huW, v, hvW', huv⟩ := hnotorth
    exact ⟨v, hvW', u, huW, fun h => huv (by rw [star_dotProduct, h, star_zero])⟩
  obtain ⟨-, p', hp'ne, hp'deg, hp'sharp, hp'orth, hp'mem⟩ :=
    l122_aux (G := G) (x := x) (y := y) (W := W) (W' := W') (r := r) (r' := r') (d := d)
      (d' := d') (a := a) (a' := a') (xs := xs) (xs' := xs') (w := w) (w' := w')
      hG hstable hirr hthin hend hdiam ha hx hstable' hirr' hthin' hend' hdiam' ha' hx'
      hw hwne hw' hw'ne hnotorth
  obtain ⟨-, p, hpne, hpdeg, hpsharp, hporth, hpmem⟩ :=
    l122_aux (G := G) (x := y) (y := x) (W := W') (W' := W) (r := r') (r' := r) (d := d')
      (d' := d) (a := a') (a' := a) (xs := xs') (xs' := xs) (w := w') (w' := w)
      hG hstable' hirr' hthin' hend' hdiam' ha' hx' hstable hirr hthin hend hdiam ha hx
      hw' hw'ne hw hwne hnotorth'
  have hpsharp' : p.natDegree + r' ≤ G.dist x y + r := by
    rw [SimpleGraph.dist_comm] at hpsharp
    exact hpsharp
  exact ⟨p, p', hpne, hp'ne, ⟨hp'deg, hp'sharp⟩, ⟨hpdeg, hpsharp'⟩, hp'orth, hporth, hp'mem,
    hpmem⟩

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Elementary facts about the Hermitian pairing -/

/-- A complex number fixed by `star` is the coercion of its real part. -/
theorem complex_eq_ofReal_re_of_star {z : ℂ} (h : star z = z) : z = ((z.re : ℝ) : ℂ) := by
  have him : z.im = 0 := by
    have h2 : (star z).im = z.im := by rw [h]
    rw [Complex.star_def, Complex.conj_im] at h2
    linarith
  exact Complex.ext (by simp) (by simp [him])

/-- `⟨u,u⟩ = ‖u‖²`, as a complex number. -/
theorem star_dotProduct_self_eq_ofReal_vnorm (u : X → ℂ) :
    star u ⬝ᵥ u = ((vnorm u * vnorm u : ℝ) : ℂ) := by
  rw [complex_eq_ofReal_re_of_star (star_dotProduct_self_real u), star_dotProduct_self_re]

/-- `⟨u,u⟩ ≠ 0` for a nonzero vector. -/
theorem star_dotProduct_self_ne_zero {u : X → ℂ} (hu : u ≠ 0) : star u ⬝ᵥ u ≠ 0 :=
  fun h => hu (star_dotProduct_self_eq_zero h)

/-- The norm is nonzero for a nonzero vector. -/
theorem vnorm_ne_zero {u : X → ℂ} (hu : u ≠ 0) : vnorm u ≠ 0 :=
  fun h => hu (vnorm_eq_zero.mp h)

/-- A subconstituent image of a stable module is contained in that module.  This is
the step that turns Lemma 12.2 (i)'s hypothesis `w ∈ E*_r(x) W` into the membership
`w ∈ W` used by `lemma12_2_ii`. -/
theorem subconstImage_le_of_isStable {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W) (i : ℕ) :
    subconstImage (𝕜 := ℂ) G x i W ≤ W := by
  intro v hv
  obtain ⟨u, hu, rfl⟩ := mem_matImage.mp hv
  exact hstable _ (subconst_mem_subconstituentAlgebra G x i) u hu

/-- In a thin setting the `E_θ`-spectral projection of a vector of a `T(x)`-module
still lies in that module: `E_θ` is a polynomial in `A`. -/
theorem spectralProj_mem_subconstituentAlgebra {G : SimpleGraph X} {x : X} (θ : ℂ) :
    spectralProj (adj (𝕜 := ℂ) G) θ ∈ (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra :=
  boseMesner_le_subconstituentAlgebra G x (spectralProj_mem_span (star_adj G) θ)

/-- Restriction of `spectralProj_mem_subconstituentAlgebra` to a module. -/
theorem spectralProj_mulVec_mem {G : SimpleGraph X} {x : X} {W : Submodule ℂ (X → ℂ)}
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W) (θ : ℂ)
    {w : X → ℂ} (hw : w ∈ W) :
    spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w ∈ W :=
  hstable _ (spectralProj_mem_subconstituentAlgebra θ) w hw

/-! ## `A` commutes with everything built from it -/

/-- `aeval A q` commutes with `A`. -/
theorem commute_aeval_adj (A : Matrix X X ℂ) (q : Polynomial ℂ) :
    Commute ((Polynomial.aeval (R := ℂ) A) q) A := by
  have h : Commute ((Polynomial.aeval (R := ℂ) A) q)
      ((Polynomial.aeval (R := ℂ) A) Polynomial.X) := by
    show (Polynomial.aeval (R := ℂ) A) q * (Polynomial.aeval (R := ℂ) A) Polynomial.X
        = (Polynomial.aeval (R := ℂ) A) Polynomial.X * (Polynomial.aeval (R := ℂ) A) q
    rw [← Polynomial.aeval_mul, ← Polynomial.aeval_mul, mul_comm]
  rwa [Polynomial.aeval_X] at h

/-- The adjoint of a polynomial in `A` commutes with `A` when `A` is self-adjoint. -/
theorem commute_star_aeval_adj {A : Matrix X X ℂ} (hA : star A = A) (q : Polynomial ℂ) :
    star ((Polynomial.aeval (R := ℂ) A) q) * A = A * star ((Polynomial.aeval (R := ℂ) A) q) := by
  have h := congrArg star (commute_aeval_adj A q)
  simp only [star_mul, hA] at h
  exact h.symm

/-- `star (aeval A q) * E_θ = conj (q.eval θ) • E_θ`.  This is what lets us move a
polynomial in `A` through the pairing against a spectral projection. -/
theorem star_aeval_mul_spectralProj {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) (q : Polynomial ℂ) :
    star ((Polynomial.aeval (R := ℂ) A) q) * spectralProj A θ
      = (star (q.eval θ)) • spectralProj A θ := by
  have hME : (Polynomial.aeval (R := ℂ) A) q * spectralProj A θ
      = q.eval θ • spectralProj A θ := aeval_mul_spectralProj hA q hθ
  have hEs : star (spectralProj A θ) = spectralProj A θ := star_spectralProj hA hθ
  have h1 : spectralProj A θ * star ((Polynomial.aeval (R := ℂ) A) q)
      = (star (q.eval θ)) • spectralProj A θ := by
    have h2 : star ((Polynomial.aeval (R := ℂ) A) q * spectralProj A θ)
        = star (q.eval θ • spectralProj A θ) := by rw [hME]
    rwa [star_mul, hEs, star_smul, hEs] at h2
  have hle : Algebra.adjoin ℂ ({A} : Set (Matrix X X ℂ)) ≤
      Subalgebra.centralizer ℂ ({star ((Polynomial.aeval (R := ℂ) A) q)} : Set (Matrix X X ℂ)) := by
    rw [Algebra.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine (Subalgebra.mem_centralizer_iff (R := ℂ)).mpr ?_
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact commute_star_aeval_adj hA q
  have hmem := hle (spectralProj_mem_span hA θ)
  have h2 := (Subalgebra.mem_centralizer_iff (R := ℂ)
    (s := ({star ((Polynomial.aeval (R := ℂ) A) q)} : Set (Matrix X X ℂ)))).mp hmem
    (star ((Polynomial.aeval (R := ℂ) A) q)) rfl
  rw [h2, h1]

/-- **The characteristic computation of Lemma 12.2 (ii).**  For a self-adjoint `A`,
an eigenvalue `θ` with spectral projection `E = spectralProj A θ`, and any
polynomial `q`, the pairing `⟨E w, q(A) v⟩` is `q(θ) ⟨E w, E v⟩`. -/
theorem star_dotProduct_spectralProj_aeval {A : Matrix X X ℂ} (hA : star A = A) {θ : ℂ}
    (hθ : θ ∈ eigFinset A) (q : Polynomial ℂ) (w v : X → ℂ) :
    star (spectralProj A θ *ᵥ w) ⬝ᵥ ((Polynomial.aeval (R := ℂ) A) q *ᵥ v)
      = q.eval θ * (star (spectralProj A θ *ᵥ w) ⬝ᵥ (spectralProj A θ *ᵥ v)) := by
  have hEE : spectralProj A θ * spectralProj A θ = spectralProj A θ :=
    spectralProj_mul_self hA hθ
  have hEs : star (spectralProj A θ) = spectralProj A θ := star_spectralProj hA hθ
  have hME : star ((Polynomial.aeval (R := ℂ) A) q) * spectralProj A θ
      = (star (q.eval θ)) • spectralProj A θ := star_aeval_mul_spectralProj hA hθ q
  have hEEw : spectralProj A θ *ᵥ (spectralProj A θ *ᵥ w) = spectralProj A θ *ᵥ w := by
    rw [Matrix.mulVec_mulVec (M := spectralProj A θ) (N := spectralProj A θ) (v := w), hEE]
  -- `⟨E w, E v⟩ = ⟨E w, v⟩`
  have hidem : star (spectralProj A θ *ᵥ w) ⬝ᵥ (spectralProj A θ *ᵥ v)
      = star (spectralProj A θ *ᵥ w) ⬝ᵥ v := by
    rw [star_mulVec_dotProduct (a := spectralProj A θ), hEs, hEEw]
  -- `star M *ᵥ E w = conj (q.eval θ) • E w`
  have h1 : star ((Polynomial.aeval (R := ℂ) A) q) *ᵥ (spectralProj A θ *ᵥ w)
      = (star (q.eval θ)) • (spectralProj A θ *ᵥ w) := by
    rw [Matrix.mulVec_mulVec (M := star ((Polynomial.aeval (R := ℂ) A) q))
      (N := spectralProj A θ) (v := w), hME, Matrix.smul_mulVec]
  rw [star_mulVec_dotProduct (a := (Polynomial.aeval (R := ℂ) A) q), h1, star_smul, star_star,
    smul_dotProduct, ← hidem, smul_eq_mul]

/-! ## The eigenvalue identities of Lemma 12.2 (ii) -/

/-- The raw form of Lemma 12.2 (ii): the pairing `⟨E_θ w, E_θ w'⟩` in terms of the
projection-normalised polynomial values.  Both right-hand sides carry the ratios of
the norms explicitly. -/
theorem lemma12_2_ii_raw {G : SimpleGraph X} {x y : X}
    {W W' : Submodule ℂ (X → ℂ)} {w w' : X → ℂ} {p p' : Polynomial ℂ}
    (hwne : w ≠ 0) (hw'ne : w' ≠ 0) (hw : w ∈ W) (hw' : w' ∈ W')
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hstable' : IsStable (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hprojW : ∀ u ∈ W, star u ⬝ᵥ
      (w' - ((vnorm w' / vnorm w : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p' *ᵥ w)) = 0)
    (hprojW' : ∀ u ∈ W', star u ⬝ᵥ
      (w - ((vnorm w / vnorm w' : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p *ᵥ w')) = 0)
    {θ : ℂ} (hθ : IsEigenvalue (adj (𝕜 := ℂ) G) θ) :
    star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
        (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
      = ((vnorm w' / vnorm w : ℝ) : ℂ) * (p'.eval θ) *
        (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
          (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w))
    ∧ star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
        (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
      = ((vnorm w / vnorm w' : ℝ) : ℂ) * (star (p.eval θ)) *
        (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
          (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')) := by
  have hA : star (adj (𝕜 := ℂ) G) = adj (𝕜 := ℂ) G := star_adj G
  have hθmem : θ ∈ eigFinset (adj (𝕜 := ℂ) G) := (isEigenvalue_iff_mem_eigFinset hA).mp hθ
  have hEE : spectralProj (adj (𝕜 := ℂ) G) θ * spectralProj (adj (𝕜 := ℂ) G) θ
      = spectralProj (adj (𝕜 := ℂ) G) θ := spectralProj_mul_self hA hθmem
  have hEs : star (spectralProj (adj (𝕜 := ℂ) G) θ) = spectralProj (adj (𝕜 := ℂ) G) θ :=
    star_spectralProj hA hθmem
  have huW : spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w ∈ W := spectralProj_mulVec_mem hstable θ hw
  have hu'W : spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w' ∈ W' := spectralProj_mulVec_mem hstable' θ hw'
  have hEEw : spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
      = spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w := by
    rw [Matrix.mulVec_mulVec (M := spectralProj (adj (𝕜 := ℂ) G) θ)
      (N := spectralProj (adj (𝕜 := ℂ) G) θ) (v := w), hEE]
  have hEEw' : spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
      = spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w' := by
    rw [Matrix.mulVec_mulVec (M := spectralProj (adj (𝕜 := ℂ) G) θ)
      (N := spectralProj (adj (𝕜 := ℂ) G) θ) (v := w'), hEE]
  constructor
  · have h1 : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
          (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
        = star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ w' := by
      rw [star_mulVec_dotProduct (a := spectralProj (adj (𝕜 := ℂ) G) θ), hEs, hEEw]
    have h2 : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ w'
        = ((vnorm w' / vnorm w : ℝ) : ℂ) *
          (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
            ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p' *ᵥ w)) := by
      have h := hprojW _ huW
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h
      exact h
    have h3 := star_dotProduct_spectralProj_aeval hA hθmem p' w w
    rw [h1, h2, h3]
    ring
  · have h1 : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
          (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
        = star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ w := by
      rw [star_mulVec_dotProduct (a := spectralProj (adj (𝕜 := ℂ) G) θ), hEs, hEEw']
    have h2 : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ w
        = ((vnorm w / vnorm w' : ℝ) : ℂ) *
          (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
            ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p *ᵥ w')) := by
      have h := hprojW' _ hu'W
      rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_eq_zero] at h
      exact h
    have h3 : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
          ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p *ᵥ w')
        = p.eval θ * (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
            (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')) :=
      star_dotProduct_spectralProj_aeval hA hθmem p w' w'
    have hmain : star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
          (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
        = ((vnorm w / vnorm w' : ℝ) : ℂ) * (p.eval θ) *
          (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
            (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')) := by
      rw [h1, h2, h3]; ring
    rw [← star_dotProduct_symm (u := spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
      (v := spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w), hmain, star_mul, star_mul,
      star_dotProduct_self_real (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')]
    rw [show star ((vnorm w / vnorm w' : ℝ) : ℂ) = ((vnorm w / vnorm w' : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    ring

/-- **Lemma 12.2 (ii)** (corrected form; see the module docstring).

For every eigenvalue `θ` of `Γ`,
`⟨E_θ w, E_θ w'⟩ = m(θ) p'(θ) ‖w‖‖w'‖ = m'(θ) conj(p(θ)) ‖w‖‖w'‖`,
where `m(θ) = ‖E_θ w‖²/‖w‖²` is the spectral measure of `w` and `m'(θ)` that of `w'`.

Thus the only difference from the notes' §4E statement is (a) the factor
`((vnorm w * vnorm w' : ℝ) : ℂ)`, without which the identity is false, and (b) the
membership hypotheses `w ∈ W`, `w' ∈ W'`. -/
theorem lemma12_2_ii {G : SimpleGraph X} {x y : X}
    {W W' : Submodule ℂ (X → ℂ)} {w w' : X → ℂ} {p p' : Polynomial ℂ}
    (hwne : w ≠ 0) (hw'ne : w' ≠ 0) (hw : w ∈ W) (hw' : w' ∈ W')
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hstable' : IsStable (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hprojW : ∀ u ∈ W, star u ⬝ᵥ
      (w' - ((vnorm w' / vnorm w : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p' *ᵥ w)) = 0)
    (hprojW' : ∀ u ∈ W', star u ⬝ᵥ
      (w - ((vnorm w / vnorm w' : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p *ᵥ w')) = 0) :
    ∀ θ, IsEigenvalue (adj (𝕜 := ℂ) G) θ →
      (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
          ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w'))
        = ((star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
              ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w))
            / (star w ⬝ᵥ w)) * (p'.eval θ)
          * ((vnorm w * vnorm w' : ℝ) : ℂ)
      ∧ (star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w)
          ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w'))
        = ((star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w')
              ⬝ᵥ (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w'))
            / (star w' ⬝ᵥ w')) * (star (p.eval θ))
          * ((vnorm w * vnorm w' : ℝ) : ℂ) := by
  intro θ hθ
  have hraw := lemma12_2_ii_raw hwne hw'ne hw hw' hstable hstable' hprojW hprojW' hθ
  have hN : star w ⬝ᵥ w = ((vnorm w * vnorm w : ℝ) : ℂ) :=
    star_dotProduct_self_eq_ofReal_vnorm w
  have hN' : star w' ⬝ᵥ w' = ((vnorm w' * vnorm w' : ℝ) : ℂ) :=
    star_dotProduct_self_eq_ofReal_vnorm w'
  have ha : vnorm w ≠ 0 := vnorm_ne_zero hwne
  have ha' : vnorm w' ≠ 0 := vnorm_ne_zero hw'ne
  have hNne : star w ⬝ᵥ w ≠ 0 := star_dotProduct_self_ne_zero hwne
  have hN'ne : star w' ⬝ᵥ w' ≠ 0 := star_dotProduct_self_ne_zero hw'ne
  have hc : ((vnorm w' / vnorm w : ℝ) : ℂ)
      = ((vnorm w * vnorm w' : ℝ) : ℂ) / (star w ⬝ᵥ w) := by
    rw [hN, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
    have haC : ((vnorm w : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha
    field_simp
  have hc' : ((vnorm w / vnorm w' : ℝ) : ℂ)
      = ((vnorm w * vnorm w' : ℝ) : ℂ) / (star w' ⬝ᵥ w') := by
    rw [hN', Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul]
    have ha'C : ((vnorm w' : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha'
    field_simp
  constructor
  · rw [hraw.1, hc]
    field_simp
  · rw [hraw.2, hc']
    field_simp

/-- **Lemma 12.2 (iii).**  For every eigenvalue `θ` of `Γ` at which both spectral
measures are nonzero, `p(θ) p'(θ)` is a real number in `[0,1]`.  (The side
condition is necessary: the notes' own argument divides by `m(θ) m'(θ)`.) -/
theorem lemma12_2_iii {G : SimpleGraph X} {x y : X}
    {W W' : Submodule ℂ (X → ℂ)} {w w' : X → ℂ} {p p' : Polynomial ℂ}
    (hwne : w ≠ 0) (hw'ne : w' ≠ 0) (hw : w ∈ W) (hw' : w' ∈ W')
    (hstable : IsStable (subconstituentAlgebra (𝕜 := ℂ) G x).toSubalgebra W)
    (hstable' : IsStable (subconstituentAlgebra (𝕜 := ℂ) G y).toSubalgebra W')
    (hprojW : ∀ u ∈ W, star u ⬝ᵥ
      (w' - ((vnorm w' / vnorm w : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p' *ᵥ w)) = 0)
    (hprojW' : ∀ u ∈ W', star u ⬝ᵥ
      (w - ((vnorm w / vnorm w' : ℝ) : ℂ) •
        ((Polynomial.aeval (R := ℂ) (adj (𝕜 := ℂ) G)) p *ᵥ w')) = 0) :
    ∀ θ, IsEigenvalue (adj (𝕜 := ℂ) G) θ →
      star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ⬝ᵥ
        (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w) ≠ 0 →
      star (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ⬝ᵥ
        (spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w') ≠ 0 →
      ∃ t : ℝ, (p.eval θ) * (p'.eval θ) = (t : ℂ) ∧ 0 ≤ t ∧ t ≤ 1 := by
  intro θ hθ hM hM'
  obtain ⟨hraw1, hraw2⟩ :=
    lemma12_2_ii_raw hwne hw'ne hw hw' hstable hstable' hprojW hprojW' hθ
  set u := spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w with hu
  set u' := spectralProj (adj (𝕜 := ℂ) G) θ *ᵥ w' with hu'
  set S := star u ⬝ᵥ u' with hS
  have hraw1' : S = ((vnorm w' / vnorm w : ℝ) : ℂ) * (p'.eval θ) * (star u ⬝ᵥ u) := by
    rw [hS, hu, hu']; exact hraw1
  have hraw2' : S = ((vnorm w / vnorm w' : ℝ) : ℂ) * (star (p.eval θ)) * (star u' ⬝ᵥ u') := by
    rw [hS, hu, hu']; exact hraw2
  have hune : u ≠ 0 := by
    intro h0; exact hM (by rw [h0]; simp)
  have hu'ne : u' ≠ 0 := by
    intro h0; exact hM' (by rw [h0]; simp)
  have hm : vnorm u ≠ 0 := vnorm_ne_zero hune
  have hm' : vnorm u' ≠ 0 := vnorm_ne_zero hu'ne
  have ha : vnorm w ≠ 0 := vnorm_ne_zero hwne
  have ha' : vnorm w' ≠ 0 := vnorm_ne_zero hw'ne
  -- the conjugate identity
  have hconj : star S = ((vnorm w / vnorm w' : ℝ) : ℂ) * (p.eval θ) * (star u' ⬝ᵥ u') := by
    rw [hraw2', star_mul, star_mul, star_dotProduct_self_real u', star_star]
    rw [show star ((vnorm w / vnorm w' : ℝ) : ℂ) = ((vnorm w / vnorm w' : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    ring
  have hcoef : ((vnorm w' / vnorm w : ℝ) : ℂ) * ((vnorm w / vnorm w' : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_one, Complex.ofReal_inj]
    field_simp
  have hMM : (star u ⬝ᵥ u) * (star u' ⬝ᵥ u') = (((vnorm u * vnorm u') ^ 2 : ℝ) : ℂ) := by
    rw [star_dotProduct_self_eq_ofReal_vnorm u, star_dotProduct_self_eq_ofReal_vnorm u',
      ← Complex.ofReal_mul]
    congr 1
    ring
  have hm2 : ((vnorm u * vnorm u') ^ 2 : ℝ) ≠ 0 :=
    pow_ne_zero 2 (mul_ne_zero hm hm')
  have hm2pos : (0 : ℝ) < (vnorm u * vnorm u') ^ 2 :=
    pow_pos (mul_pos (vnorm_pos hune) (vnorm_pos hu'ne)) 2
  -- the product identity
  have hkey : S * star S = (p.eval θ * p'.eval θ) * ((star u ⬝ᵥ u) * (star u' ⬝ᵥ u')) := by
    rw [hconj, hraw1']
    calc ((vnorm w' / vnorm w : ℝ) : ℂ) * (p'.eval θ) * (star u ⬝ᵥ u)
          * (((vnorm w / vnorm w' : ℝ) : ℂ) * (p.eval θ) * (star u' ⬝ᵥ u'))
        = (((vnorm w' / vnorm w : ℝ) : ℂ) * ((vnorm w / vnorm w' : ℝ) : ℂ))
            * (p'.eval θ * p.eval θ) * ((star u ⬝ᵥ u) * (star u' ⬝ᵥ u')) := by ring
      _ = (p.eval θ * p'.eval θ) * ((star u ⬝ᵥ u) * (star u' ⬝ᵥ u')) := by
            rw [hcoef]; ring
  have hSS : S * star S = ((Complex.normSq S : ℝ) : ℂ) := Complex.mul_conj S
  have hprod : (p.eval θ * p'.eval θ) * (((vnorm u * vnorm u') ^ 2 : ℝ) : ℂ)
      = ((Complex.normSq S : ℝ) : ℂ) := by
    rw [← hMM, ← hkey, hSS]
  have hCS : Complex.normSq S ≤ (vnorm u * vnorm u') ^ 2 := by
    have h1 : Complex.normSq S = ‖S‖ ^ 2 := Complex.normSq_eq_norm_sq S
    have h2 : ‖S‖ ≤ vnorm u * vnorm u' := abs_star_dotProduct_le_vnorm u u'
    have h3 : ‖S‖ ^ 2 ≤ (vnorm u * vnorm u') ^ 2 := pow_le_pow_left₀ (norm_nonneg S) h2 2
    linarith
  refine ⟨Complex.normSq S / ((vnorm u * vnorm u') ^ 2), ?_, ?_, ?_⟩
  · rw [(eq_div_iff (Complex.ofReal_ne_zero.mpr hm2)).mpr hprod, ← Complex.ofReal_div]
  · exact div_nonneg (Complex.normSq_nonneg S) (le_of_lt hm2pos)
  · rw [div_le_one hm2pos]
    exact hCS

end Terwilliger
