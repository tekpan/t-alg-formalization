/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
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
# Association schemes (Chapters 17–19)

A (commutative) association scheme on a finite set `X` with `D+1` relations, in
the sense of Definition 17.1 of Terwilliger's notes.  We record the association
matrices `Aᵢ`, the Bose–Mesner algebra `M = Span(A₀, …, A_D)`, and the two main
structural results: `AᵢAⱼ = ∑ₕ p^h_{ij} Aₕ` (Definition 17.2 (iv')) and the
existence of a basis of primitive idempotents (Lemma 19.1).
-/

set_option linter.unusedSectionVars false

open scoped Classical
open Matrix

noncomputable section

namespace Terwilliger

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## Auxiliary linear maps and closure lemmas -/

/-- Right multiplication by `P` as a linear map. -/
def mulRightLM (P : Matrix X X ℂ) : Matrix X X ℂ →ₗ[ℂ] Matrix X X ℂ where
  toFun a := a * P
  map_add' a b := Matrix.add_mul a b P
  map_smul' c a := Matrix.smul_mul c a P

@[simp] theorem mulRightLM_apply (P a : Matrix X X ℂ) : mulRightLM P a = a * P := rfl

/-- Powers of an element of a multiplicative submodule, multiplied by the identity. -/
theorem pow_mul_mem {A : Submodule ℂ (Matrix X X ℂ)}
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) {h : Matrix X X ℂ} (hh : h ∈ A)
    {e : Matrix X X ℂ} (he : e ∈ A) : ∀ k : ℕ, h ^ k * e ∈ A
  | 0 => by simpa using he
  | k + 1 => by
      have h1 : h ^ k * e ∈ A := pow_mul_mem hmul hh he k
      rw [pow_succ', Matrix.mul_assoc]
      exact hmul h hh (h ^ k * e) h1

/-- A polynomial in `h`, multiplied by the identity of the subalgebra, lies in it. -/
theorem aeval_mul_mem {A : Submodule ℂ (Matrix X X ℂ)}
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) {h : Matrix X X ℂ} (hh : h ∈ A)
    {e : Matrix X X ℂ} (he : e ∈ A) (q : Polynomial ℂ) :
    (Polynomial.aeval h) q * e ∈ A := by
  have h1 : (Polynomial.aeval h) q
      = ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i • h ^ i :=
    Polynomial.aeval_eq_sum_range (p := q) h
  rw [h1, Finset.sum_mul]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Matrix.smul_mul]
  exact Submodule.smul_mem _ _ (pow_mul_mem hmul hh he i)

/-- The conclusion package: `s` is a family of pairwise orthogonal self-adjoint
nonzero idempotents of `A`, summing to the identity `e` of `A` and spanning `A`. -/
def IsIdemBasis (A : Submodule ℂ (Matrix X X ℂ)) (e : Matrix X X ℂ)
    (s : Finset (Matrix X X ℂ)) : Prop :=
  (∀ E ∈ s, E ∈ A) ∧ (∀ E ∈ s, E * E = E) ∧ (∀ E ∈ s, star E = E) ∧
  (∀ E ∈ s, E ≠ 0) ∧
  (∀ E ∈ s, ∀ E' ∈ s, E ≠ E' → E * E' = 0) ∧
  (∑ E ∈ s, E = e) ∧
  (∀ a ∈ A, ∃ c : Matrix X X ℂ → ℂ, a = ∑ E ∈ s, c E • E)


/-- An element commuting with `h` commutes with every polynomial in `h`. -/
theorem aeval_comm_of_commute {r h : Matrix X X ℂ} (hc : r * h = h * r) (q : Polynomial ℂ) :
    r * (Polynomial.aeval h) q = (Polynomial.aeval h) q * r := by
  have hpow : ∀ k : ℕ, r * h ^ k = h ^ k * r := by
    intro k
    induction k with
    | zero => rw [pow_zero, mul_one, one_mul]
    | succ k ih =>
        rw [pow_succ', ← mul_assoc, hc, mul_assoc, ih, ← mul_assoc, ← pow_succ']
  rw [Polynomial.aeval_eq_sum_range (p := q) h, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hpow k]

/-- The product of two commuting idempotents is an idempotent. -/
theorem idem_mul_of_commute {p e : Matrix X X ℂ} (hp : p * p = p) (he : e * e = e)
    (hc : e * p = p * e) : (p * e) * (p * e) = p * e := by
  rw [← Matrix.mul_assoc (p * e) p e, Matrix.mul_assoc p e p, hc,
    ← Matrix.mul_assoc p p e, hp, Matrix.mul_assoc p e e, he]

/-! ## The all-ones matrix -/

/-- The all-ones matrix `J`. -/
def allOnesMat : Matrix X X ℂ := fun _ _ => (1 : ℂ)

@[simp] theorem allOnesMat_apply (x y : X) : allOnesMat x y = (1 : ℂ) := rfl

@[simp] theorem star_allOnesMat : star (allOnesMat : Matrix X X ℂ) = allOnesMat := by
  ext x y
  simp [allOnesMat]

/-! ## The piece of a subalgebra cut out by an idempotent -/

/-- The set `{a * f : a ∈ A}` inherits the closure properties, with identity `f`. -/
structure PieceData (A : Submodule ℂ (Matrix X X ℂ)) (f : Matrix X X ℂ) : Prop where
  mul_mem : ∀ a ∈ A.map (mulRightLM f), ∀ b ∈ A.map (mulRightLM f),
    a * b ∈ A.map (mulRightLM f)
  star_mem : ∀ a ∈ A.map (mulRightLM f), star a ∈ A.map (mulRightLM f)
  comm : ∀ a ∈ A.map (mulRightLM f), ∀ b ∈ A.map (mulRightLM f), a * b = b * a
  ident : ∀ a ∈ A.map (mulRightLM f), a * f = a
  le : A.map (mulRightLM f) ≤ A
  f_mem : f ∈ A.map (mulRightLM f)

theorem mul_mul_right_eq {A : Submodule ℂ (Matrix X X ℂ)}
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {f : Matrix X X ℂ} (hf : f ∈ A) (hfid : f * f = f)
    {a₀ b₀ : Matrix X X ℂ} (ha₀ : a₀ ∈ A) (hb₀ : b₀ ∈ A) :
    (a₀ * f) * (b₀ * f) = (a₀ * b₀) * f := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc a₀ b₀ f, ← Matrix.mul_assoc f b₀ f,
    hcomm f hf b₀ hb₀, Matrix.mul_assoc b₀ f f, hfid]

theorem pieceData {A : Submodule ℂ (Matrix X X ℂ)}
    (hmul : ∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
    (hstar : ∀ a ∈ A, star a ∈ A)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    {f : Matrix X X ℂ} (hf : f ∈ A) (hfid : f * f = f) (hfstar : star f = f) :
    PieceData A f := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Submodule.mem_map.mp hb
    refine Submodule.mem_map.mpr ⟨a₀ * b₀, hmul a₀ ha₀ b₀ hb₀, ?_⟩
    simp only [mulRightLM_apply]
    exact (mul_mul_right_eq hcomm hf hfid ha₀ hb₀).symm
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp ha
    refine Submodule.mem_map.mpr ⟨star a₀, hstar a₀ ha₀, ?_⟩
    simp only [mulRightLM_apply, star_mul, hfstar]
    exact (hcomm f hf (star a₀) (hstar a₀ ha₀)).symm
  · intro a ha b hb
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Submodule.mem_map.mp hb
    simp only [mulRightLM_apply]
    rw [mul_mul_right_eq hcomm hf hfid ha₀ hb₀, mul_mul_right_eq hcomm hf hfid hb₀ ha₀,
      hcomm a₀ ha₀ b₀ hb₀]
  · intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp ha
    simp only [mulRightLM_apply]
    rw [Matrix.mul_assoc, hfid]
  · intro x hx
    obtain ⟨a₀, ha₀, rfl⟩ := Submodule.mem_map.mp hx
    exact hmul a₀ ha₀ f hf
  · refine Submodule.mem_map.mpr ⟨f, hf, ?_⟩
    simp only [mulRightLM_apply, hfid]


/-- **A commutative, invariant subalgebra is spanned by orthogonal self-adjoint
idempotents.**  Let `A` be a `ℂ`-submodule of the matrix algebra, closed under
multiplication and under `star`, commutative, and let `e` be a nonzero
self-adjoint idempotent in `A` that acts as an identity on `A`.  Then `A` has a
family of pairwise orthogonal, self-adjoint, nonzero idempotents summing to `e`
and spanning `A`. -/
theorem exists_isIdemBasis : ∀ (n : ℕ), ∀ (A : Submodule ℂ (Matrix X X ℂ)) (e : Matrix X X ℂ),
    (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A) → (∀ a ∈ A, star a ∈ A) →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → e ∈ A → e * e = e → star e = e → e ≠ 0 →
    (∀ a ∈ A, a * e = a) → Module.finrank ℂ A = n → ∃ s, IsIdemBasis A e s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro A e hmul hstar hcomm he heid hstare hene hident hfin
    by_cases hcase : Module.finrank ℂ A = 1
    · -- base case: `A` is the line spanned by `e`
      have hspan : A = Submodule.span ℂ ({e} : Set (Matrix X X ℂ)) := by
        have hfr : Module.finrank ℂ (Submodule.span ℂ ({e} : Set (Matrix X X ℂ))) = 1 :=
          finrank_span_singleton hene
        have hle : Submodule.span ℂ ({e} : Set (Matrix X X ℂ)) ≤ A := by
          rw [Submodule.span_le]
          simpa using he
        exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hcase, hfr])).symm
      refine ⟨{e}, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro E hE
        rw [Finset.mem_singleton] at hE
        rw [hE]
        exact he
      · intro E hE
        rw [Finset.mem_singleton] at hE
        rw [hE]
        exact heid
      · intro E hE
        rw [Finset.mem_singleton] at hE
        rw [hE]
        exact hstare
      · intro E hE
        rw [Finset.mem_singleton] at hE
        rw [hE]
        exact hene
      · intro E hE E' hE' hne
        rw [Finset.mem_singleton] at hE hE'
        exact absurd (hE.trans hE'.symm) hne
      · rw [Finset.sum_singleton]
      · intro a ha
        have ham : a ∈ Submodule.span ℂ ({e} : Set (Matrix X X ℂ)) := by rw [← hspan]; exact ha
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ham
        exact ⟨fun _ => c, by rw [Finset.sum_singleton]; exact hc.symm⟩
    · -- step
      have hpos : 0 < Module.finrank ℂ A := by
        rw [Module.finrank_pos_iff]
        exact ⟨⟨⟨e, he⟩, 0, fun h => hene (congrArg Subtype.val h)⟩⟩
      have hge2 : 2 ≤ Module.finrank ℂ A := by omega
      -- (1) a non-scalar self-adjoint element of `A`
      have hns : ∃ a ∈ A, ∀ c : ℂ, a ≠ c • e := by
        by_contra hcon
        push_neg at hcon
        have hle : A ≤ Submodule.span ℂ ({e} : Set (Matrix X X ℂ)) := by
          intro a ha
          obtain ⟨c, hc⟩ := hcon a ha
          rw [hc]
          exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton e))
        have hfr : Module.finrank ℂ (Submodule.span ℂ ({e} : Set (Matrix X X ℂ))) = 1 :=
          finrank_span_singleton hene
        have hle1 : Module.finrank ℂ A ≤ 1 := by
          rw [← hfr]
          exact Submodule.finrank_mono hle
        omega
      obtain ⟨a, haA, hane⟩ := hns
      have hstara : star a ∈ A := hstar a haA
      have hI1 : star ((2 : ℂ) * Complex.I) = -((2 : ℂ) * Complex.I) := by
        simp [Complex.conj_I]
      have hI2 : star ((2 : ℂ) * Complex.I)⁻¹ = -((2 : ℂ) * Complex.I)⁻¹ := by
        rw [star_inv₀, hI1, inv_neg]
      have hI3 : Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ := by
        have h : ((2 : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by norm_num) Complex.I_ne_zero
        field_simp
      have hex : ∃ h ∈ A, star h = h ∧ ∀ c : ℂ, h ≠ c • e := by
        by_cases h1 : ∃ c : ℂ, (2 : ℂ)⁻¹ • (a + star a) = c • e
        · obtain ⟨c1, hc1⟩ := h1
          refine ⟨(2 * Complex.I)⁻¹ • (a - star a), ?_, ?_, ?_⟩
          · exact Submodule.smul_mem _ _ (Submodule.sub_mem A haA hstara)
          · have h1 : star a - a = -(a - star a) := by abel
            rw [star_smul_matrix, hI2, star_sub, star_star, h1, smul_neg, neg_smul, neg_neg]
          · intro c hc
            apply hane (c1 + Complex.I * c)
            have h2 : Complex.I • ((2 * Complex.I)⁻¹ • (a - star a)) = (2 : ℂ)⁻¹ • (a - star a) := by
              rw [smul_smul, hI3]
            have hsum : (2 : ℂ)⁻¹ • (a + star a) + (2 : ℂ)⁻¹ • (a - star a) = a := by
              rw [← smul_add]
              have h2a : (a + star a) + (a - star a) = a + a := by abel
              rw [h2a, ← two_smul ℂ a, ← mul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
            calc a = (2 : ℂ)⁻¹ • (a + star a) + Complex.I • ((2 * Complex.I)⁻¹ • (a - star a)) := by
                    rw [h2, hsum]
              _ = c1 • e + Complex.I • (c • e) := by rw [hc1, hc]
              _ = (c1 + Complex.I * c) • e := by rw [add_smul, smul_smul]
        · push_neg at h1
          refine ⟨(2 : ℂ)⁻¹ • (a + star a), ?_, ?_, h1⟩
          · exact Submodule.smul_mem _ _ (Submodule.add_mem A haA hstara)
          · rw [star_smul_matrix, star_add, star_star]
            norm_num
            abel
      obtain ⟨h, hhA, hhH, hhns⟩ := hex
      -- (2) two distinct eigenvalues whose projections do not vanish on `e`
      have hsum1 : ∑ θ ∈ eigFinset h, spectralProj h θ * e = e := by
        rw [← Finset.sum_mul, sum_spectralProj hhH, Matrix.one_mul]
      have hspec : h = ∑ θ ∈ eigFinset h, θ • (spectralProj h θ * e) := by
        conv_lhs => rw [← hident h hhA, spectral_theorem hhH]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun θ _ => by rw [Matrix.smul_mul]
      have htwo : ∃ θ₁ ∈ eigFinset h, ∃ θ₂ ∈ eigFinset h, θ₁ ≠ θ₂ ∧
          spectralProj h θ₁ * e ≠ 0 ∧ spectralProj h θ₂ * e ≠ 0 := by
        set S := (eigFinset h).filter (fun θ => spectralProj h θ * e ≠ 0) with hSdef
        have hcard : 1 < S.card := by
          rw [Finset.one_lt_card]
          by_contra hcon
          push_neg at hcon
          have hzero : ∀ θ ∈ eigFinset h, θ ∉ S → θ • (spectralProj h θ * e) = 0 := by
            intro θ hθ hθS
            have h0 : spectralProj h θ * e = 0 := by
              by_contra hne
              exact hθS (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hθ, hne⟩)
            rw [h0, smul_zero]
          have hcollapse : h = ∑ θ ∈ S, θ • (spectralProj h θ * e) := by
            conv_lhs => rw [hspec]
            exact (Finset.sum_subset (s₁ := S) (s₂ := eigFinset h)
              (Finset.filter_subset _ _) hzero).symm
          have hce : e = ∑ θ ∈ S, spectralProj h θ * e := by
            conv_lhs => rw [← hsum1]
            exact (Finset.sum_subset (s₁ := S) (s₂ := eigFinset h) (Finset.filter_subset _ _)
              (fun θ hθ hθS => by
                by_contra hne
                exact hθS (by rw [hSdef]; exact Finset.mem_filter.mpr ⟨hθ, hne⟩))).symm
          rcases S.eq_empty_or_nonempty with hemp | ⟨θ₀, hθ₀⟩
          · refine hhns 0 ?_
            rw [hcollapse, hemp, Finset.sum_empty, zero_smul]
          · have hsingle : ∀ θ ∈ S, θ = θ₀ := fun θ hθ => hcon θ hθ θ₀ hθ₀
            have hS1 : S = {θ₀} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hθ₀, hsingle⟩
            have hee : e = spectralProj h θ₀ * e := by
              conv_lhs => rw [hce, hS1, Finset.sum_singleton]
            refine hhns θ₀ ?_
            rw [hcollapse, hS1, Finset.sum_singleton]
            conv_rhs => rw [hee]
        have hmemS : ∀ θ, θ ∈ S ↔ θ ∈ eigFinset h ∧ spectralProj h θ * e ≠ 0 := by
          intro θ
          rw [hSdef]
          exact Finset.mem_filter
        rw [Finset.one_lt_card] at hcard
        obtain ⟨θ₁, hθ₁, θ₂, hθ₂, hne⟩ := hcard
        exact ⟨θ₁, ((hmemS θ₁).mp hθ₁).1, θ₂, ((hmemS θ₂).mp hθ₂).1, hne,
          ((hmemS θ₁).mp hθ₁).2, ((hmemS θ₂).mp hθ₂).2⟩
      -- (3) the idempotent `P`
      obtain ⟨θ₁, hθ₁T, θ₂, hθ₂T, hθ₁₂, hP1ne, hP2ne⟩ := htwo
      have he_h : e * h = h * e := hcomm e he h hhA
      have he_P : e * spectralProj h θ₁ = spectralProj h θ₁ * e :=
        aeval_comm_of_commute (r := e) (h := h) he_h (lagrangePoly (eigFinset h) θ₁)
      let P : Matrix X X ℂ := spectralProj h θ₁ * e
      have hPne0 : P ≠ 0 := hP1ne
      have hPmem : P ∈ A :=
        aeval_mul_mem hmul hhA he (lagrangePoly (eigFinset h) θ₁)
      have heP : e * P = P := (hcomm e he P hPmem).trans (hident P hPmem)
      have hPe : P * e = P := hident P hPmem
      have hPidem : P * P = P :=
        idem_mul_of_commute (spectralProj_mul_self hhH hθ₁T) heid he_P
      have hPstar : star P = P := by
        show star (spectralProj h θ₁ * e) = spectralProj h θ₁ * e
        rw [star_mul, star_spectralProj hhH hθ₁T, hstare, he_P]
      have hP2zero : spectralProj h θ₂ * P = 0 := by
        show spectralProj h θ₂ * (spectralProj h θ₁ * e) = 0
        rw [← Matrix.mul_assoc,
          spectralProj_mul_of_ne hhH (θ := θ₂) (ψ := θ₁) (Ne.symm hθ₁₂), Matrix.zero_mul]
      have hQne : e - P ≠ 0 := by
        intro hQ
        have h1 : spectralProj h θ₂ * (e - P) = 0 := by rw [hQ, Matrix.mul_zero]
        rw [Matrix.mul_sub, hP2zero, sub_zero] at h1
        exact hP2ne h1
      have hPne : P ≠ e := by
        intro hPe'
        exact hQne (by rw [hPe', sub_self])
      -- (4) the two complementary pieces
      have hQidem : (e - P) * (e - P) = e - P := by
        have h1 : (e - P) * (e - P) = e * e - e * P - (P * e - P * P) := by
          rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
        rw [h1, heid, heP, hPe, hPidem]
        abel
      have hQstar : star (e - P) = e - P := by
        rw [star_sub, hstare, hPstar]
      have dP : PieceData A P := pieceData hmul hstar hcomm hPmem hPidem hPstar
      have hQmem : e - P ∈ A := Submodule.sub_mem A he hPmem
      have dQ : PieceData A (e - P) := pieceData hmul hstar hcomm hQmem hQidem hQstar
      have hQ0 : (e - P) * P = 0 := by rw [Matrix.sub_mul, heP, hPidem, sub_self]
      have hne1 : A.map (mulRightLM P) ≠ A := by
        intro hEq
        have he' : e ∈ A.map (mulRightLM P) := by rw [hEq]; exact he
        obtain ⟨a₀, ha₀, hEq2⟩ := Submodule.mem_map.mp he'
        refine hPne ?_
        calc P = e * P := heP.symm
          _ = (a₀ * P) * P := by
              conv_lhs => rw [← hEq2]
              simp only [mulRightLM_apply]
          _ = a₀ * P := by rw [Matrix.mul_assoc, hPidem]
          _ = e := hEq2
      have hne2 : A.map (mulRightLM (e - P)) ≠ A := by
        intro hEq
        have he' : e ∈ A.map (mulRightLM (e - P)) := by rw [hEq]; exact he
        obtain ⟨a₀, ha₀, hEq2⟩ := Submodule.mem_map.mp he'
        have hP0 : P = 0 := by
          calc P = e * P := heP.symm
            _ = (a₀ * (e - P)) * P := by
                conv_lhs => rw [← hEq2]
                simp only [mulRightLM_apply]
            _ = a₀ * ((e - P) * P) := by rw [Matrix.mul_assoc]
            _ = 0 := by rw [hQ0, Matrix.mul_zero]
        exact hPne0 hP0
      have hlt1 : Module.finrank ℂ ↥(A.map (mulRightLM P)) < n := by
        have hlt : A.map (mulRightLM P) < A := lt_of_le_of_ne dP.le hne1
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      have hlt2 : Module.finrank ℂ ↥(A.map (mulRightLM (e - P))) < n := by
        have hlt : A.map (mulRightLM (e - P)) < A := lt_of_le_of_ne dQ.le hne2
        have := Submodule.finrank_lt_finrank_of_lt hlt
        omega
      obtain ⟨s₁, hs₁⟩ := ih (Module.finrank ℂ ↥(A.map (mulRightLM P))) hlt1
        (A.map (mulRightLM P)) P dP.mul_mem dP.star_mem dP.comm dP.f_mem hPidem hPstar
        hPne0 dP.ident rfl
      obtain ⟨s₂, hs₂⟩ := ih (Module.finrank ℂ ↥(A.map (mulRightLM (e - P)))) hlt2
        (A.map (mulRightLM (e - P))) (e - P) dQ.mul_mem dQ.star_mem dQ.comm dQ.f_mem
        hQidem hQstar hQne dQ.ident rfl
      -- (5) the two families are disjoint and combine
      have hinter : ∀ x ∈ A.map (mulRightLM P), x ∈ A.map (mulRightLM (e - P)) → x = 0 := by
        intro x hx1 hx2
        obtain ⟨a₂, ha₂, hEq⟩ := Submodule.mem_map.mp hx2
        have hx1' : x * P = x := dP.ident x hx1
        calc x = x * P := hx1'.symm
          _ = (a₂ * (e - P)) * P := by
              rw [← hEq]
              simp only [mulRightLM_apply]
          _ = a₂ * ((e - P) * P) := by rw [Matrix.mul_assoc]
          _ = 0 := by rw [hQ0, Matrix.mul_zero]
      have hdisjF : Disjoint s₁ s₂ := by
        rw [Finset.disjoint_left]
        intro E hE1 hE2
        exact hs₁.2.2.2.1 E hE1 (hinter E (hs₁.1 E hE1) (hs₂.1 E hE2))
      refine ⟨s₁ ∪ s₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro E hE
        rcases Finset.mem_union.mp hE with hE | hE
        · exact dP.le (hs₁.1 E hE)
        · exact dQ.le (hs₂.1 E hE)
      · intro E hE
        rcases Finset.mem_union.mp hE with hE | hE
        · exact hs₁.2.1 E hE
        · exact hs₂.2.1 E hE
      · intro E hE
        rcases Finset.mem_union.mp hE with hE | hE
        · exact hs₁.2.2.1 E hE
        · exact hs₂.2.2.1 E hE
      · intro E hE
        rcases Finset.mem_union.mp hE with hE | hE
        · exact hs₁.2.2.2.1 E hE
        · exact hs₂.2.2.2.1 E hE
      · intro E hE E' hE' hne
        rcases Finset.mem_union.mp hE with hE | hE <;> rcases Finset.mem_union.mp hE' with hE' | hE'
        · exact hs₁.2.2.2.2.1 E hE E' hE' hne
        · have hEP : E * P = E := dP.ident E (hs₁.1 E hE)
          have hE'e : E' * e = E' := hident E' (dQ.le (hs₂.1 E' hE'))
          have hE'EP : E' * (e - P) = E' := dQ.ident E' (hs₂.1 E' hE')
          have hE'P : E' * P = 0 := by
            have h2 : E' * P = E' * e - E' * (e - P) := by
              rw [Matrix.mul_sub]
              abel
            rw [h2, hE'e, hE'EP, sub_self]
          have hPE' : P * E' = 0 := by
            rw [hcomm P hPmem E' (dQ.le (hs₂.1 E' hE')), hE'P]
          calc E * E' = (E * P) * E' := by rw [hEP]
            _ = E * (P * E') := by rw [Matrix.mul_assoc]
            _ = 0 := by rw [hPE', Matrix.mul_zero]
        · have hE'P : E' * P = E' := dP.ident E' (hs₁.1 E' hE')
          have hEPe : E * e = E := hident E (dQ.le (hs₂.1 E hE))
          have hEEP : E * (e - P) = E := dQ.ident E (hs₂.1 E hE)
          have hEP0 : E * P = 0 := by
            have h2 : E * P = E * e - E * (e - P) := by
              rw [Matrix.mul_sub]
              abel
            rw [h2, hEPe, hEEP, sub_self]
          have hPE' : P * E' = E' := by
            rw [hcomm P hPmem E' (dP.le (hs₁.1 E' hE')), hE'P]
          have h3 : E * (P * E') = E * E' := by rw [hPE']
          have h2 : (E * P) * E' = 0 := by rw [hEP0, Matrix.zero_mul]
          calc E * E' = E * (P * E') := h3.symm
            _ = (E * P) * E' := by rw [← Matrix.mul_assoc]
            _ = 0 := h2
        · exact hs₂.2.2.2.2.1 E hE E' hE' hne
      · rw [Finset.sum_union hdisjF, hs₁.2.2.2.2.2.1, hs₂.2.2.2.2.2.1]
        abel
      · intro a ha
        obtain ⟨c₁, hc₁⟩ := hs₁.2.2.2.2.2.2 (a * P) (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
        obtain ⟨c₂, hc₂⟩ := hs₂.2.2.2.2.2.2 (a * (e - P)) (Submodule.mem_map.mpr ⟨a, ha, rfl⟩)
        refine ⟨fun E => if E ∈ s₁ then c₁ E else c₂ E, ?_⟩
        rw [Finset.sum_union hdisjF]
        have h1 : ∑ E ∈ s₁, (if E ∈ s₁ then c₁ E else c₂ E) • E = ∑ E ∈ s₁, c₁ E • E :=
          Finset.sum_congr rfl fun E hE => by rw [if_pos hE]
        have h2 : ∑ E ∈ s₂, (if E ∈ s₁ then c₁ E else c₂ E) • E = ∑ E ∈ s₂, c₂ E • E :=
          Finset.sum_congr rfl fun E hE => by
            rw [if_neg (Finset.disjoint_left.mp hdisjF.symm hE)]
        rw [h1, h2, ← hc₁, ← hc₂]
        have h3 : a * P + a * (e - P) = a := by
          rw [Matrix.mul_sub, hident a ha]
          abel
        rw [h3]


/-- A nonzero idempotent lying below `|X|⁻¹ • J` equals `|X|⁻¹ • J`: the latter has
rank one, so its only nonzero sub-idempotent is itself. -/
theorem eq_of_idem_below_allOnesMat [Nonempty X] {P : Matrix X X ℂ}
    (hidem : P * P = P)
    (hl : P * ((1 / (Fintype.card X : ℂ)) • allOnesMat) = P)
    (hr : ((1 / (Fintype.card X : ℂ)) • allOnesMat) * P = P) (hne : P ≠ 0) :
    P = (1 / (Fintype.card X : ℂ)) • allOnesMat := by
  classical
  have hn0 : (Fintype.card X : ℂ) ≠ 0 := by
    have h : 0 < Fintype.card X := Fintype.card_pos
    exact_mod_cast h.ne'
  have hrow : ∀ x y y', P x y = P x y' := by
    intro x y y'
    have h1 := congrFun (congrFun hl x) y
    have h2 := congrFun (congrFun hl x) y'
    simp only [Matrix.mul_apply, Matrix.smul_apply, allOnesMat_apply, mul_one, smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
  have hcol : ∀ x x' y, P x y = P x' y := by
    intro x x' y
    have h1 := congrFun (congrFun hr x) y
    have h2 := congrFun (congrFun hr x') y
    simp only [Matrix.mul_apply, Matrix.smul_apply, allOnesMat_apply, smul_eq_mul] at h1 h2
    rw [← h1, ← h2]
  have hconst : ∀ x y x' y', P x y = P x' y' :=
    fun x y x' y' => (hrow x y y').trans (hcol x x' y')
  obtain ⟨x₀⟩ := ‹Nonempty X›
  set d := P x₀ x₀ with hd
  have hPJ : P = d • (allOnesMat : Matrix X X ℂ) := by
    ext x y
    have h1 : P x y = d := by rw [hconst x y x₀ x₀, ← hd]
    rw [h1]
    simp [allOnesMat]
  have hJJ : (allOnesMat : Matrix X X ℂ) * allOnesMat = (Fintype.card X : ℂ) • allOnesMat := by
    ext x y
    simp [Matrix.mul_apply, allOnesMat]
  have hsc : d * d * (Fintype.card X : ℂ) = d := by
    have h1 : (d • (allOnesMat : Matrix X X ℂ)) * (d • allOnesMat) = d • allOnesMat := by
      rw [← hPJ]; exact hidem
    have h2 : (d • (allOnesMat : Matrix X X ℂ)) * (d • allOnesMat)
        = (d * d * (Fintype.card X : ℂ)) • allOnesMat := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hJJ, smul_smul]
    rw [h2] at h1
    have h3 := congrFun (congrFun h1 x₀) x₀
    simpa [allOnesMat] using h3
  have hd0 : d ≠ 0 := by
    intro h
    exact hne (by rw [hPJ, h, zero_smul])
  have hd1 : d = (1 / (Fintype.card X : ℂ)) := by
    have h : d * (d * (Fintype.card X : ℂ) - 1) = 0 := by
      rw [mul_sub, mul_one, ← mul_assoc, hsc, sub_self]
    have h2 : d * (Fintype.card X : ℂ) = 1 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' hd0
      · linear_combination h'
    rw [eq_inv_of_mul_eq_one_left h2, one_div]
  rw [hPJ, hd1]


/-- **Definition 17.1.** A commutative association scheme with `D+1` classes. -/
structure AssociationScheme (X : Type*) [Fintype X] (D : ℕ) where
  /-- The `i`-th relation. -/
  rel : Fin (D + 1) → X → X → Prop
  /-- `R₀` is the diagonal relation. -/
  rel_zero : ∀ x y, rel 0 x y ↔ x = y
  /-- Every pair of vertices lies in exactly one relation. -/
  rel_total : ∀ x y, ∃! i, rel i x y
  /-- Each relation has a transpose, which is again one of the relations. -/
  rel_symm : ∀ i, ∃ j, ∀ x y, rel i x y ↔ rel j y x
  /-- The intersection numbers `p^h_{ij}`. -/
  p : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℕ
  /-- `p^h_{ij}` counts the common neighbours. -/
  p_spec : ∀ (h i j : Fin (D + 1)) (x y : X), rel h x y →
    (Finset.univ.filter fun z => rel i x z ∧ rel j z y).card = p h i j
  /-- Commutativity of the scheme. -/
  p_comm : ∀ h i j, p h i j = p h j i

namespace AssociationScheme

variable {D : ℕ} (Y : AssociationScheme X D)

/-- The `i`-th association matrix `Aᵢ` (Definition 17.2). -/
def assocMatrix (i : Fin (D + 1)) : Matrix X X ℂ :=
  fun x y => if Y.rel i x y then 1 else 0

@[simp]
theorem assocMatrix_apply (i : Fin (D + 1)) (x y : X) :
    Y.assocMatrix i x y = if Y.rel i x y then 1 else 0 := rfl

/-- **Definition 17.2 (iv').** `Aᵢ Aⱼ = ∑ₕ p^h_{ij} Aₕ`. -/
theorem assocMatrix_mul (i j : Fin (D + 1)) :
    Y.assocMatrix i * Y.assocMatrix j
      = ∑ h : Fin (D + 1), (Y.p h i j : ℂ) • Y.assocMatrix h := by
  ext x y
  rw [Matrix.mul_apply]
  have key : (∑ z, Y.assocMatrix i x z * Y.assocMatrix j z y)
      = ((Finset.univ.filter fun z => Y.rel i x z ∧ Y.rel j z y).card : ℂ) := by
    rw [← Finset.sum_boole (s := Finset.univ)
      (p := fun z => Y.rel i x z ∧ Y.rel j z y)]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [assocMatrix_apply, assocMatrix_apply]
    by_cases h1 : Y.rel i x z <;> by_cases h2 : Y.rel j z y <;> simp [h1, h2]
  rw [key]
  simp only [Matrix.sum_apply, Matrix.smul_apply]
  obtain ⟨h₀, hh₀, huniq⟩ := Y.rel_total x y
  rw [Finset.sum_eq_single h₀]
  · rw [assocMatrix_apply, if_pos hh₀, smul_eq_mul, mul_one, Y.p_spec h₀ i j x y hh₀]
  · intro h _ hne
    rw [assocMatrix_apply, if_neg (fun hh => hne (huniq h hh)), smul_zero]
  · intro h; exact absurd (Finset.mem_univ h₀) h

/-- The association matrix of `R₀` is the identity. -/
theorem assocMatrix_zero : Y.assocMatrix 0 = 1 := by
  ext x y
  rw [assocMatrix_apply, Matrix.one_apply]
  exact if_congr (Y.rel_zero x y) rfl rfl

/-- `Y` is symmetric when every relation is its own transpose. -/
def IsSymmetric : Prop := ∀ i, ∀ x y, Y.rel i x y ↔ Y.rel i y x

/-- The Bose–Mesner algebra of the scheme: `Span(A₀, …, A_D)`. -/
def boseMesnerSubmodule : Submodule ℂ (Matrix X X ℂ) :=
  Submodule.span ℂ (Set.range Y.assocMatrix)

/-- The association matrices span a subalgebra of the full matrix algebra
(Definition 17.2). -/
theorem mul_mem_boseMesnerSubmodule {a b : Matrix X X ℂ}
    (ha : a ∈ Y.boseMesnerSubmodule) (hb : b ∈ Y.boseMesnerSubmodule) :
    a * b ∈ Y.boseMesnerSubmodule := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          rw [Y.assocMatrix_mul]
          exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h, rfl⟩)
      | zero => rw [mul_zero]; exact Submodule.zero_mem _
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hu
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [add_mul]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ c hu

/-! ## The association matrices are self-adjoint up to a permutation and commute -/


/-- `star` of an association matrix is an association matrix. -/
theorem exists_star_assocMatrix (i : Fin (D + 1)) :
    ∃ j, star (Y.assocMatrix i) = Y.assocMatrix j := by
  obtain ⟨j, hj⟩ := Y.rel_symm i
  refine ⟨j, ?_⟩
  ext x y
  rw [Matrix.star_apply, Y.assocMatrix_apply, Y.assocMatrix_apply]
  have hxy : Y.rel i y x ↔ Y.rel j x y := hj y x
  by_cases h : Y.rel j x y
  · rw [if_pos (hxy.mpr h), if_pos h]
    simp
  · rw [if_neg (fun hh => h (hxy.mp hh)), if_neg h]
    simp

/-- The Bose–Mesner algebra is closed under `star`. -/
theorem star_mem_boseMesnerSubmodule {a : Matrix X X ℂ} (ha : a ∈ Y.boseMesnerSubmodule) :
    star a ∈ Y.boseMesnerSubmodule := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      obtain ⟨j, hj⟩ := Y.exists_star_assocMatrix i
      rw [hj]
      exact Submodule.subset_span ⟨j, rfl⟩
  | zero => rw [star_zero]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [star_add]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [star_smul_matrix]; exact Submodule.smul_mem _ _ hu

/-- The association matrices commute pairwise. -/
theorem assocMatrix_mul_comm (i j : Fin (D + 1)) :
    Y.assocMatrix i * Y.assocMatrix j = Y.assocMatrix j * Y.assocMatrix i := by
  rw [Y.assocMatrix_mul, Y.assocMatrix_mul]
  exact Finset.sum_congr rfl fun h _ => by rw [Y.p_comm h i j]

/-- The Bose–Mesner algebra is commutative. -/
theorem mul_comm_boseMesnerSubmodule {a b : Matrix X X ℂ}
    (ha : a ∈ Y.boseMesnerSubmodule) (hb : b ∈ Y.boseMesnerSubmodule) : a * b = b * a := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          exact Y.assocMatrix_mul_comm i j
      | zero => rw [mul_zero, zero_mul]
      | add u v _ _ hu hv => rw [mul_add, add_mul, hu, hv]
      | smul c u _ hu => rw [Matrix.mul_smul, Matrix.smul_mul, hu]
  | zero => rw [zero_mul, mul_zero]
  | add u v _ _ hu hv => rw [add_mul, mul_add, hv, hu]
  | smul c u _ hu => rw [Matrix.smul_mul, Matrix.mul_smul, hu]

/-- The identity matrix lies in the Bose–Mesner algebra. -/
theorem one_mem_boseMesnerSubmodule : (1 : Matrix X X ℂ) ∈ Y.boseMesnerSubmodule := by
  rw [← Y.assocMatrix_zero]
  exact Submodule.subset_span ⟨0, rfl⟩

/-- The all-ones matrix is the sum of the association matrices. -/
theorem allOnesMat_eq_sum_assocMatrix :
    allOnesMat = ∑ i, Y.assocMatrix i := by
  ext x y
  rw [allOnesMat_apply]
  have h1 : (∑ i : Fin (D + 1), Y.assocMatrix i) x y
      = ∑ i : Fin (D + 1), Y.assocMatrix i x y :=
    (congrFun (Finset.sum_apply x Finset.univ (fun i : Fin (D + 1) => Y.assocMatrix i)) y).trans
      (Finset.sum_apply y Finset.univ (fun i : Fin (D + 1) => Y.assocMatrix i x))
  rw [h1]
  obtain ⟨i, hi, huniq⟩ := Y.rel_total x y
  rw [Finset.sum_eq_single i]
  · rw [Y.assocMatrix_apply, if_pos hi]
  · intro j _ hj
    rw [Y.assocMatrix_apply, if_neg (fun hh => hj (huniq j hh))]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- The all-ones matrix lies in the Bose–Mesner algebra. -/
theorem allOnesMat_mem_boseMesnerSubmodule : allOnesMat ∈ Y.boseMesnerSubmodule := by
  rw [Y.allOnesMat_eq_sum_assocMatrix]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, rfl⟩

/-- The association matrices are linearly independent for a scheme without
empty relations. -/
theorem linearIndependent_assocMatrix (hnd : ∀ i, ∃ x y, Y.rel i x y) :
    LinearIndependent ℂ Y.assocMatrix := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  obtain ⟨x, y, hxy⟩ := hnd i
  have h1 : (∑ j, g j • Y.assocMatrix j) x y = (0 : Matrix X X ℂ) x y := by rw [hg]
  rw [Matrix.sum_apply] at h1
  simp only [Matrix.smul_apply, Y.assocMatrix_apply, smul_eq_mul] at h1
  rw [Finset.sum_eq_single i] at h1
  · rwa [if_pos hxy, mul_one] at h1
  · intro j _ hji
    rw [if_neg (fun hh => hji ((Y.rel_total x y).unique hh hxy)), mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi


/-- **Lemma 19.1** (strengthened form).  A commutative association scheme whose
relations are all nonempty has a basis `E₀, …, E_D` of primitive idempotents of
its Bose–Mesner algebra: pairwise orthogonal, self-adjoint, nonzero, spanning the
algebra, summing to `1`, with `E₀ = |X|⁻¹J` (here `allOnesMat` is the all-ones
matrix `J`). -/
theorem exists_primitive_idempotents (hY : 0 < D + 1) (hnd : ∀ i, ∃ x y, Y.rel i x y) :
    ∃ E : Fin (D + 1) → Matrix X X ℂ,
      (∀ i j, E i * E j = if i = j then E i else 0) ∧
      (∑ i, E i = 1) ∧
      (∀ i, E i ∈ Y.boseMesnerSubmodule) ∧
      (∀ i, E i * E i = E i) ∧
      (∀ i, E i ≠ 0) ∧
      (Submodule.span ℂ (Set.range E) = Y.boseMesnerSubmodule) ∧
      (E 0 = (1 / (Fintype.card X : ℂ)) • allOnesMat) ∧
      (∀ i, star (E i) = E i) := by
  classical
  have hne' : Nonempty X := by
    obtain ⟨x, y, -⟩ := hnd 0
    exact ⟨x⟩
  haveI : Nonempty X := hne'
  have hmul : ∀ a ∈ Y.boseMesnerSubmodule, ∀ b ∈ Y.boseMesnerSubmodule,
      a * b ∈ Y.boseMesnerSubmodule := fun a ha b hb => Y.mul_mem_boseMesnerSubmodule ha hb
  have hstar : ∀ a ∈ Y.boseMesnerSubmodule, star a ∈ Y.boseMesnerSubmodule :=
    fun a ha => Y.star_mem_boseMesnerSubmodule ha
  have hcomm : ∀ a ∈ Y.boseMesnerSubmodule, ∀ b ∈ Y.boseMesnerSubmodule, a * b = b * a :=
    fun a ha b hb => Y.mul_comm_boseMesnerSubmodule ha hb
  have he : (1 : Matrix X X ℂ) ∈ Y.boseMesnerSubmodule := Y.one_mem_boseMesnerSubmodule
  have hone : (1 : Matrix X X ℂ) ≠ 0 := by
    intro h
    obtain ⟨x⟩ := hne'
    have h1 := congrFun (congrFun h x) x
    simp at h1
  have hfin : Module.finrank ℂ Y.boseMesnerSubmodule = D + 1 := by
    have h1 : Module.finrank ℂ Y.boseMesnerSubmodule = Fintype.card (Fin (D + 1)) :=
      finrank_span_eq_card (Y.linearIndependent_assocMatrix hnd)
    rwa [Fintype.card_fin] at h1
  obtain ⟨s, hs⟩ := exists_isIdemBasis (D + 1) Y.boseMesnerSubmodule 1 hmul hstar hcomm he
    (Matrix.one_mul 1) (star_one (Matrix X X ℂ)) hone
    (fun a _ => Matrix.mul_one a) hfin
  -- `s` spans the algebra and is linearly independent
  have hspan_s : Submodule.span ℂ (↑s : Set (Matrix X X ℂ)) = Y.boseMesnerSubmodule := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      intro E hE
      exact hs.1 E hE
    · intro a ha
      obtain ⟨c, hc⟩ := hs.2.2.2.2.2.2 a ha
      rw [hc]
      exact Submodule.sum_mem _ fun E hE => Submodule.smul_mem _ _ (Submodule.subset_span hE)
  have hlin_s : LinearIndependent ℂ (fun E : ↥s => (E : Matrix X X ℂ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg E0
    have horth : ∀ E : ↥s, E ≠ E0 → (E : Matrix X X ℂ) * (E0 : Matrix X X ℂ) = 0 := by
      intro E hE
      exact hs.2.2.2.2.1 E E.2 E0 E0.2 (fun h => hE (Subtype.ext h))
    have h1 : (∑ E : ↥s, g E • (E : Matrix X X ℂ)) * (E0 : Matrix X X ℂ) = 0 := by
      rw [hg, Matrix.zero_mul]
    rw [Finset.sum_mul] at h1
    simp only [Matrix.smul_mul] at h1
    rw [Finset.sum_eq_single E0] at h1
    · rw [show (E0 : Matrix X X ℂ) * (E0 : Matrix X X ℂ) = E0 from hs.2.1 E0 E0.2] at h1
      exact (smul_eq_zero.mp h1).resolve_right (hs.2.2.2.1 E0 E0.2)
    · intro E _ hE
      rw [horth E hE, smul_zero]
    · intro h; exact absurd (Finset.mem_univ E0) h
  have hcard : s.card = D + 1 := by
    have h1 : Module.finrank ℂ (Submodule.span ℂ (↑s : Set (Matrix X X ℂ))) = Fintype.card ↥s := by
      have h2 : (↑s : Set (Matrix X X ℂ)) = Set.range (fun E : ↥s => (E : Matrix X X ℂ)) := by
        ext x
        simp only [Finset.mem_coe, Set.mem_range]
        exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨E, hE⟩ => hE ▸ E.2⟩
      rw [h2]
      exact finrank_span_eq_card hlin_s
    rw [hspan_s, hfin] at h1
    have h3 : Fintype.card ↥s = s.card := Fintype.card_coe s
    omega
  -- reindex by `Fin (D+1)`
  have hcard' : Fintype.card ↥s = D + 1 := by rw [Fintype.card_coe, hcard]
  let idx : ↥s ≃ Fin (D + 1) := Fintype.equivFinOfCardEq hcard'
  let F : Fin (D + 1) → Matrix X X ℂ := fun k => (idx.symm k : Matrix X X ℂ)
  have hFmem : ∀ k, F k ∈ Y.boseMesnerSubmodule := fun k => hs.1 _ (idx.symm k).2
  have hFidem : ∀ k, F k * F k = F k := fun k => hs.2.1 _ (idx.symm k).2
  have hFstar : ∀ k, star (F k) = F k := fun k => hs.2.2.1 _ (idx.symm k).2
  have hFne : ∀ k, F k ≠ 0 := fun k => hs.2.2.2.1 _ (idx.symm k).2
  have hForth : ∀ k l, k ≠ l → F k * F l = 0 := by
    intro k l hkl
    have h : (idx.symm k : Matrix X X ℂ) ≠ (idx.symm l : Matrix X X ℂ) :=
      fun hh => hkl (idx.symm.injective (Subtype.ext hh))
    exact hs.2.2.2.2.1 _ (idx.symm k).2 _ (idx.symm l).2 h
  have hFsum : ∑ k, F k = 1 := by
    have h1 : ∑ k : Fin (D + 1), F k = ∑ x : ↥s, (x : Matrix X X ℂ) :=
      Equiv.sum_comp idx.symm (fun x : ↥s => (x : Matrix X X ℂ))
    rw [h1, Finset.univ_eq_attach]
    rw [Finset.sum_attach s (fun E : Matrix X X ℂ => E)]
    exact hs.2.2.2.2.2.1
  have hFspan : Submodule.span ℂ (Set.range F) = Y.boseMesnerSubmodule := by
    have h1 : Set.range F = (↑s : Set (Matrix X X ℂ)) := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩
        exact (idx.symm k).2
      · intro hx
        exact ⟨idx ⟨x, hx⟩, by simp [F]⟩
    rw [h1, hspan_s]
  have hlin_F : LinearIndependent ℂ F :=
    hlin_s.comp idx.symm idx.symm.injective
  have hexp : ∀ a ∈ Y.boseMesnerSubmodule, ∃ c : Fin (D + 1) → ℂ, a = ∑ k, c k • F k := by
    intro a ha
    obtain ⟨c', hc'⟩ := hs.2.2.2.2.2.2 a ha
    refine ⟨fun k => c' (idx.symm k), ?_⟩
    rw [hc']
    have h1 : ∑ k : Fin (D + 1), c' (idx.symm k) • (idx.symm k : Matrix X X ℂ)
        = ∑ x : ↥s, c' (x : Matrix X X ℂ) • (x : Matrix X X ℂ) :=
      Equiv.sum_comp idx.symm (fun x : ↥s => c' (x : Matrix X X ℂ) • (x : Matrix X X ℂ))
    rw [h1, Finset.univ_eq_attach]
    rw [Finset.sum_attach s (fun E : Matrix X X ℂ => c' E • E)]
  -- the uniform idempotent and its expansion
  have hn0 : (Fintype.card X : ℂ) ≠ 0 := by
    have h : 0 < Fintype.card X := Fintype.card_pos
    exact_mod_cast h.ne'
  have hJmem : (allOnesMat : Matrix X X ℂ) ∈ Y.boseMesnerSubmodule :=
    Y.allOnesMat_mem_boseMesnerSubmodule
  have he₀mem : ((1 / (Fintype.card X : ℂ)) • allOnesMat) ∈ Y.boseMesnerSubmodule :=
    Submodule.smul_mem _ _ hJmem
  have hstarScalar : star (1 / (Fintype.card X : ℂ)) = (1 / (Fintype.card X : ℂ) : ℂ) := by
    simp
  have he₀star : star ((1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ))
      = (1 / (Fintype.card X : ℂ)) • allOnesMat := by
    rw [star_smul_matrix, star_allOnesMat, hstarScalar]
  have hJJ : (allOnesMat : Matrix X X ℂ) * allOnesMat = (Fintype.card X : ℂ) • allOnesMat := by
    ext x y
    simp [Matrix.mul_apply, allOnesMat]
  have he₀idem : ((1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ))
      * ((1 / (Fintype.card X : ℂ)) • allOnesMat) = (1 / (Fintype.card X : ℂ)) • allOnesMat := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hJJ, smul_smul]
    congr 1
    field_simp
  have he₀ne : ((1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ)) ≠ 0 := by
    intro h
    obtain ⟨x⟩ := hne'
    have h1 : ((1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ)) x x = 0 := by
      rw [h]; rfl
    simp [allOnesMat] at h1
  obtain ⟨c, hc⟩ := hexp _ he₀mem
  have hc2 : ∀ k, c k * c k = c k := by
    intro k
    have hmul_sum : (∑ k, c k • F k) * (∑ l, c l • F l) = ∑ k, (c k * c k) • F k := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.mul_sum]
      rw [Finset.sum_eq_single k]
      · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hFidem k]
      · intro l _ hlk
        rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hForth k l (Ne.symm hlk), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    have h3 : ∑ k, (c k * c k) • F k = ∑ k, c k • F k := by
      rw [← hmul_sum, ← hc, he₀idem, hc]
    have h4 : ∑ k, (c k * c k - c k) • F k = 0 := by
      have h5 : ∑ k, (c k * c k) • F k - ∑ k, c k • F k = 0 := by rw [h3, sub_self]
      rw [← Finset.sum_sub_distrib] at h5
      simpa only [sub_smul] using h5
    have h6 := (Fintype.linearIndependent_iff.mp hlin_F) (fun k => c k * c k - c k) h4 k
    linear_combination h6
  have hc01 : ∀ k, c k = 0 ∨ c k = 1 := by
    intro k
    have h := hc2 k
    have h' : c k * (c k - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (by linear_combination h1)
  have hbelow : ∀ k, c k = 1 → F k = (1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ) := by
    intro k hk
    refine eq_of_idem_below_allOnesMat (hFidem k) ?_ ?_ (hFne k)
    · rw [hc, Matrix.mul_sum]
      rw [Finset.sum_eq_single k]
      · rw [Matrix.mul_smul, hFidem k, hk, one_smul]
      · intro l _ hlk
        rw [Matrix.mul_smul, hForth k l (Ne.symm hlk), smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
    · rw [hc, Finset.sum_mul]
      rw [Finset.sum_eq_single k]
      · rw [Matrix.smul_mul, hFidem k, hk, one_smul]
      · intro l _ hlk
        rw [Matrix.smul_mul, hForth l k hlk, smul_zero]
      · intro h; exact absurd (Finset.mem_univ k) h
  have he₀sum : (1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ)
      = ∑ k ∈ Finset.univ.filter (fun k => c k = 1), F k := by
    rw [hc]
    have h1 : ∑ k, c k • F k = ∑ k, (if c k = 1 then F k else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rcases hc01 k with h0 | h1
      · rw [h0, zero_smul, if_neg zero_ne_one]
      · rw [h1, one_smul, if_pos rfl]
    rw [h1, ← Finset.sum_filter]
  have hfilter_le : (Finset.univ.filter fun k => c k = 1).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k hk l hl
    by_contra hkl
    have hk1 : c k = 1 := (Finset.mem_filter.mp hk).2
    have hl1 : c l = 1 := (Finset.mem_filter.mp hl).2
    have h1 : F k * F l = 0 := hForth k l hkl
    rw [hbelow k hk1, hbelow l hl1] at h1
    rw [he₀idem] at h1
    exact he₀ne h1
  have hfilter_ge : 1 ≤ (Finset.univ.filter fun k => c k = 1).card := by
    by_contra h
    rw [not_le] at h
    have h0 : Finset.univ.filter (fun k => c k = 1) = ∅ := Finset.card_eq_zero.mp (by omega)
    apply he₀ne
    rw [he₀sum, h0, Finset.sum_empty]
  have hfilter1 : (Finset.univ.filter fun k => c k = 1).card = 1 :=
    le_antisymm hfilter_le hfilter_ge
  obtain ⟨k₀, hk₀⟩ := Finset.card_eq_one.mp hfilter1
  have hFk : F k₀ = (1 / (Fintype.card X : ℂ)) • (allOnesMat : Matrix X X ℂ) := by
    rw [he₀sum, hk₀, Finset.sum_singleton]
  -- relabel so that the uniform idempotent is `E 0`
  refine ⟨fun k => F (Equiv.swap 0 k₀ k), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : i = j
    · subst hij; rw [if_pos rfl, hFidem]
    · rw [if_neg hij, hForth (Equiv.swap 0 k₀ i) (Equiv.swap 0 k₀ j)
        (fun h => hij ((Equiv.swap 0 k₀).injective h))]
  · have h1 : ∑ i : Fin (D + 1), F (Equiv.swap 0 k₀ i) = ∑ i : Fin (D + 1), F i :=
      Equiv.sum_comp (Equiv.swap 0 k₀) F
    rw [h1, hFsum]
  · intro i; exact hFmem _
  · intro i; exact hFidem _
  · intro i; exact hFne _
  · have h1 : Set.range (fun k => F (Equiv.swap 0 k₀ k)) = Set.range F := by
      ext x
      constructor
      · rintro ⟨k, rfl⟩; exact ⟨Equiv.swap 0 k₀ k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨Equiv.swap 0 k₀ k, ?_⟩
        show F (Equiv.swap 0 k₀ (Equiv.swap 0 k₀ k)) = F k
        rw [Equiv.swap_apply_self]
    rw [h1, hFspan]
  · show F (Equiv.swap 0 k₀ 0) = (1 / (Fintype.card X : ℂ)) • allOnesMat
    rw [Equiv.swap_apply_left]
    exact hFk
  · intro i; exact hFstar _

/-! ## The Krein parameters (W-g, proved; merged from the repo's version)

The `exists_krein_parameters` below is the wave-2 W-g theorem with the fix-2
hypotheses (`hspan`/`hherm`), already proved — kept from the committed library.
-/

/-- The entrywise product of Hermitian matrices is Hermitian. -/
theorem hadamard_conjTranspose (a b : Matrix X X ℂ) :
    (a ⊙ b)ᴴ = aᴴ ⊙ bᴴ := by
  ext x y
  rw [Matrix.conjTranspose_apply, Matrix.hadamard_apply, Matrix.hadamard_apply,
    Matrix.conjTranspose_apply, Matrix.conjTranspose_apply, star_mul, mul_comm]

/-- **Lecture 19.** `Aᵢ ⊙ Aⱼ = δᵢⱼAᵢ`: distinct association matrices are
orthogonal for the entrywise product. -/
theorem hadamard_assocMatrix (i j : Fin (D + 1)) :
    Y.assocMatrix i ⊙ Y.assocMatrix j = if i = j then Y.assocMatrix i else 0 := by
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    ext x y
    by_cases h : Y.rel i x y <;> simp [Matrix.hadamard_apply, assocMatrix_apply, h]
  · rw [if_neg hij]
    ext x y
    obtain ⟨k, _, huniq⟩ := Y.rel_total x y
    by_cases h1 : Y.rel i x y
    · have h2 : ¬ Y.rel j x y := by
        intro h2
        exact hij ((huniq i h1).trans (huniq j h2).symm)
      simp [Matrix.hadamard_apply, assocMatrix_apply, h1, h2]
    · simp [Matrix.hadamard_apply, assocMatrix_apply, h1]

/-- The Bose–Mesner algebra is closed under the entrywise product (Lecture 19:
`Aᵢ ⊙ Aⱼ = δᵢⱼAᵢ`, and the entrywise product is bilinear). -/
theorem hadamard_mem_boseMesnerSubmodule {a b : Matrix X X ℂ}
    (ha : a ∈ Y.boseMesnerSubmodule) (hb : b ∈ Y.boseMesnerSubmodule) :
    a ⊙ b ∈ Y.boseMesnerSubmodule := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      induction hb using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨j, rfl⟩ := hy
          rw [Y.hadamard_assocMatrix]
          by_cases h : i = j
          · rw [if_pos h]; exact Submodule.subset_span ⟨i, rfl⟩
          · rw [if_neg h]; exact Submodule.zero_mem _
      | zero => rw [Matrix.hadamard_zero]; exact Submodule.zero_mem _
      | add u v _ _ hu hv => rw [Matrix.hadamard_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu => rw [Matrix.hadamard_smul]; exact Submodule.smul_mem _ c hu
  | zero => rw [Matrix.zero_hadamard]; exact Submodule.zero_mem _
  | add u v _ _ hu hv => rw [Matrix.add_hadamard]; exact Submodule.add_mem _ hu hv
  | smul c u _ hu => rw [Matrix.smul_hadamard]; exact Submodule.smul_mem _ c hu

/-- Two expansions of the same matrix in a `⊙`-orthogonal family agree at every
index at which the family member is nonzero: the nonzero members of a
`⊙`-orthogonal family are linearly independent. -/
theorem coeff_eq_of_sum_smul_eq {E : Fin (D + 1) → Matrix X X ℂ}
    (hidem : ∀ i j, E i * E j = if i = j then E i else 0)
    {c d : Fin (D + 1) → ℂ} (h : ∑ i, c i • E i = ∑ i, d i • E i) :
    ∀ i, E i = 0 ∨ c i = d i := by
  have hzero : ∑ i, (c i - d i) • E i = 0 := by
    have hsplit : ∑ i, (c i - d i) • E i
        = (∑ i, c i • E i) - (∑ i, d i • E i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => sub_smul (c i) (d i) (E i)
    rw [hsplit, h, sub_self]
  intro k
  by_cases hE : E k = 0
  · exact Or.inl hE
  · refine Or.inr (sub_eq_zero.mp ?_)
    have hmul : E k * (∑ i, (c i - d i) • E i) = 0 := by rw [hzero, mul_zero]
    rw [Matrix.mul_sum] at hmul
    have hterm : ∀ i, E k * ((c i - d i) • E i)
        = (c i - d i) • (if k = i then E k else 0) := by
      intro i
      rw [Matrix.mul_smul, hidem k i]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)] at hmul
    have hsingle : ∑ i, (c i - d i) • (if k = i then E k else 0) = (c k - d k) • E k := by
      have h0 := Finset.sum_eq_single (s := Finset.univ)
        (f := fun i => (c i - d i) • (if k = i then E k else 0)) k
        (fun b _ hb => by rw [if_neg (Ne.symm hb), smul_zero])
        (fun hk => absurd (Finset.mem_univ k) hk)
      simp only at h0
      exact h0
    rw [hsingle] at hmul
    exact (smul_eq_zero.mp hmul).resolve_right hE

/-- **Lecture 19, Krein parameters.**  If `E₀, …, E_D` are Hermitian,
`⊙`-orthogonal idempotents spanning the Bose–Mesner algebra, then the entrywise
products are `Eᵢ ⊙ Eⱼ = |X|⁻¹ ∑ₕ q^h_{ij} Eₕ` with *real* coefficients
`q^h_{ij}` — the Krein parameters of the scheme.

The hypothesis `hspan` (the `Eᵢ` span the Bose–Mesner algebra) is necessary:
`hidem` + `hsum` + `hbasis` alone do not force `Eᵢ ⊙ Eⱼ` into the span of the
`Eᵢ` — a family of orthogonal idempotents summing to `1` can span a proper
subspace of `M` (the Klein four-group and the `C₄` scheme are counterexamples;
the audit is in the wave-1 notes).  The hypothesis `hherm` is what makes the
coefficients *real*: the expansion of the Hermitian matrix `Eᵢ ⊙ Eⱼ` in the
`⊙`-orthogonal family `E` has real coefficients. -/
theorem exists_krein_parameters (E : Fin (D + 1) → Matrix X X ℂ)
    (hidem : ∀ i j, E i * E j = if i = j then E i else 0)
    (hsum : ∑ i, E i = 1) (hbasis : ∀ i, E i ∈ Y.boseMesnerSubmodule)
    (hspan : ∀ a ∈ Y.boseMesnerSubmodule, ∃ c : Fin (D + 1) → ℂ, a = ∑ i, c i • E i)
    (hherm : ∀ i, (E i)ᴴ = E i) :
    ∃ q : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℝ,
      ∀ i j, (fun x y => E i x y * E j x y)
        = (1 / (Fintype.card X : ℂ)) •
            ∑ h, (q i j h : ℂ) • E h := by
  by_cases hX : Nonempty X
  · have hcard : (Fintype.card X : ℂ) ≠ 0 := by
      have hpos : Fintype.card X ≠ 0 := (Fintype.card_pos_iff.mpr hX).ne'
      exact_mod_cast hpos
    -- expand each `Eᵢ ⊙ Eⱼ` in the spanning family
    have hcoef : ∀ i j, ∃ c : Fin (D + 1) → ℂ,
        (fun x y => E i x y * E j x y) = ∑ h, c h • E h := by
      intro i j
      exact hspan (E i ⊙ E j)
        (Y.hadamard_mem_boseMesnerSubmodule (hbasis i) (hbasis j))
    choose c hc using hcoef
    -- the coefficients of a Hermitian element are real
    have hreal : ∀ (i j h : Fin (D + 1)), E h = 0 ∨ star (c i j h) = c i j h := by
      intro i j
      have h2 : (fun x y => E i x y * E j x y)ᴴ = fun x y => E i x y * E j x y := by
        show (E i ⊙ E j)ᴴ = E i ⊙ E j
        rw [hadamard_conjTranspose, hherm i, hherm j]
      have h1 : (fun x y => E i x y * E j x y)ᴴ = ∑ h, star (c i j h) • E h := by
        rw [hc i j]
        simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hherm]
      rw [h1] at h2
      exact coeff_eq_of_sum_smul_eq hidem (h2.trans (hc i j))
    -- replace the coefficients at vanishing members by `0`
    set F : Fin (D + 1) → Fin (D + 1) → Fin (D + 1) → ℂ :=
      fun i j h => if E h = 0 then 0 else c i j h with hF
    have hF_apply : ∀ (i j h : Fin (D + 1)),
        F i j h = if E h = 0 then 0 else c i j h := fun i j h => by rw [hF]
    refine ⟨fun i j h => (Fintype.card X : ℝ) * (F i j h).re, fun i j => ?_⟩
    have hF_real : ∀ h, star (F i j h) = F i j h := by
      intro h
      by_cases hE : E h = 0
      · rw [hF_apply i j h, if_pos hE, star_zero]
      · rw [hF_apply i j h, if_neg hE]
        exact (hreal i j h).resolve_left hE
    have hF_sum : (fun x y => E i x y * E j x y) = ∑ h, F i j h • E h := by
      rw [hc i j]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [hF_apply i j h]
      by_cases hE : E h = 0
      · rw [if_pos hE, hE, smul_zero, zero_smul]
      · rw [if_neg hE]
    rw [hF_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have hq : (1 / (Fintype.card X : ℂ)) *
        (((Fintype.card X : ℝ) * (F i j h).re : ℝ) : ℂ) = F i j h := by
      have hcast : (((Fintype.card X : ℝ) * (F i j h).re : ℝ) : ℂ)
          = (Fintype.card X : ℂ) * ((F i j h).re : ℂ) := by push_cast; ring
      rw [hcast, Complex.conj_eq_iff_re.mp (hF_real h), one_div, ← mul_assoc,
        inv_mul_cancel₀ hcard, one_mul]
    rw [smul_smul, hq]
  · -- `X` empty: there are no matrix entries, and `1 / (0 : ℂ) = 0`
    have hcard0 : Fintype.card X = 0 := by
      have h : ¬ (0 < Fintype.card X) := Fintype.card_pos_iff.not.mpr hX
      omega
    refine ⟨fun _ _ _ => 0, fun i j => ?_⟩
    have hz : (fun x y => E i x y * E j x y) = 0 := by
      ext x y
      exact absurd ⟨x⟩ hX
    rw [hz, hcard0, Nat.cast_zero, div_zero, zero_smul]
    rfl


end AssociationScheme

end Terwilliger
