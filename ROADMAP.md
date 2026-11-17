# Roadmap

The lecture note has 40 chapters and 133 labelled environments.  Every chapter is
represented in this library: all definitions are formalized and every labelled
result has a Lean statement.  **7 statements are `sorry`** (all in `LateChapters.lean`, Chapters 33–40).  This file says
where they are and in what order they should be discharged.

## The 7 remaining `sorry`s (from 46 at the finish-book campaign's start)

All seven are in `LateChapters.lean`, in the deep Chapters 33–40 block.  Each
carries a refutation-checked restatement and a precise gap docstring.  Wave 3
closed two of the former eight — `raising_pow_three_injective_of_thin` (the
`E*₄(y)A³` injectivity, by the RRR ladder and a dimension induction) and, with
it, Lemma 14.2 (iii) `basic_data_diam_bound` (the diameter bound `D ≤ 2r+d`, from
QA's primitive idempotents `drg_idempotent_basis`); the 38.1 chain
(`raising_pow_three_injective_of_thin` → `e11_to_e22_injective(')`) now closes
modulo nothing.  The shared structural blocker (recorded by the wave-2 audit)
remains: `DRGData` has no Q-polynomiality field, so the chapters' running
hypothesis is stated through the standing idiom
`hθ : Function.Injective Y.thetaStar` wherever it is needed.

| Statement | Status |
| --- | --- |
| `e1star_te1star_span` (33.4 (iii)) | reduced by W-l to the single Chapter-33 ideal-theoretic input `e1star_te1star_span_of_adjoin`; wave 3 (QD) proved `eonemmstar` (Lemma 33.2 (i)) and reduced the input to a single right-`A`-closure — the hard case needs the primal idempotents, now in the library (`drg_idempotent_basis`) |
| `module_of_endpoint_one` (34.2) | wave 3 (QE): the `Ã`-cum identity, the `v⁻` lemmas and the `M`-half are proved; the statement is reduced to a single `cyclicModule`-stability input (the `M*`-half needs `eonemmstar`, proved) |
| `dim_e1star_te1star_le_five` (35.1 (ii)) | restated (W-m); Claim 1 (`E*₁ME*₁ = Span(J̃, E*₁, Ã)`) proved; wave 3 (QG) added the `p^h_{ij}` intersection-number calculus and the quartic-annihilator endgame reduction (any element of `E*₁TE*₁` determined by four structure coefficients); the quartic case split remains |
| `thin_of_dim_two_eq_one` (37.1) | wave 3 (QF): the context-free draft REFUTED, machine-checked (`thin_of_dim_two_eq_one_draft_false`: a 7-vertex graph, an irreducible endpoint-1 `T(0)`-module with `dim E*₁W = 2`, `dim E*₂W = 1`, not thin); restated with the `Q`-polynomial hypothesis (`hθ`) and `dim E*₁W = 1` (Lemma `tv`'s output) explicit; the remaining gap is the transposed Chapter-30 relations (`fr2lr2r2l` (i)/(iii)) |
| `tyx_eq_txy` (39.4) | restated (thin at every vertex, 5 ≤ D) after the K_{1,2} refutation; wave 3 (QH) mapped the (i)–(v) chain — it needs 33.4 (iii), 35.1 (ii), 39.3 and the `δ^±` layer |
| `zi_independent` (40.4) | restated; wave 3 (QI) proved the entry-vs-count identification `ziDelta_apply` (`zᵢ` = the `(z,x)`-entry of `Δ = E*_{i-1}(y)A_{i-1}E*₁(y)AE*₁(y)`), the level dichotomy, 40.4 itself for triangle-free (in particular bipartite) graphs, and the reduction of the general case to constancy of the `Δ`-entry; the gap is the `δ^±`/`Ψ` machinery (Lemma 39.2) |
| `aplus_aminus_generalized` (39.3) | restated around `IsGeneralizedAdjacencyFirstSubconst` after the refutation; wave 3 (QH) audited four further defects (the membership conjunct's generating set must be `{Ã, J̃, E*₁}` — machine-checked; `hR` is not the notes' Lemma 31.1; thinness at `y` is missing; `Ψ` unpinned) and proved the `E*_{ij}` level calculus, the `S₁(x)×S₁(x)` support of `A±`, and the reduction of conjunct (ii) to the two explicit inputs |

## Order of work

The dependencies run mostly forward through the book, so the natural order is:

1. **Chapter 1, completed.**  Lemma 1.8 (iii) (the standard module is an
   orthogonal direct sum of irreducible `T(x)`-modules) is a minimal-counterexample
   argument on `finrank`; the ingredients (`W ↦ Wᗮ`, finite dimensionality) are in
   `Basic.lean`.  Lemma 1.2 (i) needs Perron–Frobenius.
2. ~~**The trivial module is thin.**~~  **Completed:** Lemma 12.1 is proved in
   full (`(i) ⇔ (ii) ⇔ (iii)`, `DistanceRegular.lean`).  The (iii) ⇒ (i), (ii)
   half goes through `adj_mulVec_sphereSum`; the converse half takes the
   Perron vector `δ` (strictly positive, simple eigenvalue), shows `δ ∈ T(x)x̂`
   for every `x` by a Krylov-space argument, uses thinness at every vertex to
   make `δ` constant on neighbourhoods and hence on spheres, and finishes with
   the thin-line spanning argument.  Lemma 11.2 (bipartite graphs) is still
   open.
3. ~~**Perron–Frobenius.**~~  Route (a) (Collatz–Wielandt) was taken:
   Theorem 2.4 (i), (ii) and Lemma 1.2 (i), (ii) are proved
   (`CollatzWielandt.lean`).  Still open: Theorem 2.4 (iii), (iv), which need
   the spectral theorem for Hermitian matrices.
4. **Chapter 16.**  `AAᵢ = c_{i+1}A_{i+1} + aᵢAᵢ + b_{i-1}A_{i-1}` is the same
   finite count as `adj_mulVec_sphereSum`, with the base point moved from `x` to
   `y`; the counting lemmas `filter_card_eq_{bnum,anum,cnum,zero}` already have
   the right shape.
5. **Chapters 5–8.**  These need concrete computations: `H(D,2)` is
   distance-regular with `θᵢ = D - 2i`, and the `sl₂`-computation of Chapter 5
   (the raising/lowering operators `R`, `L` and `A* = D - 2i`) gives Theorem 5.2.
6. **Chapters 9–10.**  Linear algebra on a tridiagonal matrix once 9.2 (iii) is
   available; the measure `m_W` and the orthogonality relations follow.
7. **Chapters 13–16.**  The algebraic core: algebraic integers (`IsIntegral` in
   Mathlib) for Theorem 16.2, and the `γᵢ` recursion.
8. **Chapters 17–27.**  `exists_primitive_idempotents` is the entry point; then the
   entrywise (Hadamard) algebra, the `q^h_{ij}`, the vanishing conditions and the
   balanced conditions.
9. **Chapters 28–40.**  The tridiagonal pair theorem (29.1) is self-contained
   linear algebra and can be done independently of everything else; then `R, F, L`
   and the endpoint-one theory.

## Notes on the formalization choices

* The notes assume a connected graph of order `≥ 2` from Chapter 1 onwards.  Here
  connectivity is an explicit hypothesis (`G.Connected`) wherever the notes use
  it, so the definitions remain meaningful for arbitrary finite graphs.
* `T(x)` is a `StarSubalgebra`.  This is not cosmetic: Lemma 1.8 (ii) is false
  for an arbitrary subalgebra of `Mat_X(𝕜)`, and the notes' proof uses exactly the
  fact that the generators are symmetric.
* Subconstituent projections are indexed by `ℕ`, with `Eᵢ*(x) = 0` for `i` larger
  than the eccentricity, rather than by `Fin (d(x)+1)`.
* Distances come from `SimpleGraph.dist`.  For a connected graph this is the graph
  metric of the notes; `dist_eq_one_iff_adj` and `Adj.diff_dist_adj` do most of the
  combinatorial work.
* From Chapter 20 onwards the notes work inside a commutative association scheme
  with a chosen spectral decomposition.  `SchemeData` and `DRGData` make those
  hypotheses explicit: the primitive idempotents, the eigenvalues `θᵢ`, the dual
  eigenvalues `θ*ᵢ` and the Krein parameters are fields of the structure.  Stating
  the theorems this way is faithful — they are exactly the running assumptions of
  the second half of the book — and it isolates the one genuinely missing piece of
  library support (the spectral theorem) in a single place.
