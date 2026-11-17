# Coverage of the lecture note

Every labelled definition and result of <https://icu-hsuzuki.github.io/t-algebra/>
(40 chapters, 133 labelled environments), with the corresponding status in this
library.  Statuses: *proved* (checked by Lean), *stated* (`sorry`), *defined*
(the definition is formalized).

| Ch. | Title | Labelled statements | Status |
| --- | --- | --- | --- |
| 1 | Subconstituent Algebra of a Graph | `four-vertex-graph` · `adjacency-matrix` · `regular` · `largestev` · `path` · `distance` · `connected` · `diameter` · `t-algebra` · `module` · `complete-reducibility` | defs proved (`Basic.lean`); 1.8 (i),(ii) proved; 1.8 (iii) and 1.2 open |
| 2 | Perron-Frobenius Theorem | `reducible` · `bipartite-mat` · `pf` · `pfl` · `bipartite` · `spec` | **Theorem 2.4 (i)–(iv) and Lemma 2.3 proved** (`CollatzWielandt.lean`, `PerronFrobenius.lean`) |
| 3 | Cayley Graphs | `isom` · `auto` · `transitive` · `cayley` · `cyclic6` · `k6minus1` · `d6` · `cayley-graph` · `character` · `cyclic3` · `charactergroup` | 3.4, 3.5(i) proved; 3.5(ii), 3.7 stated (`Cayley.lean`) |
| 4 | Examples | `charcter-group` · `character-cyclic6` · `hd2` · `rd` · `irreducible` | Def 4.1 + Lemma 4.3(i) proved (`Subconstituent.lean`) |
| 5 | $T$-Modules of $H(D,2)$, I | `isomorphic-modules` · `hd2-modules` | `H(D,2)` defined; Thm 5.2 stated (`Hamming.lean`) |
| 6 | $T$-Modules of $H(D,2)$, II | `hd2-modules2` · `thin-dualthin` · `q-polynomial-graph` | 6.6 defined; Thm 6.1 stated (`Hamming.lean`) |
| 7 | The Johnson Graph $J(D,N)$ | `johnson` · `j42` · `ev-johnson` · `thin-condition` | `J(D,N)` defined; **7.3 (charpoly factorization, ℤ-cast) and 7.4 (all implications) proved** (`Hamming.lean`) |
| 8 | Thin Graphs | `property-g` | **(G)⇒(S) proved** (with the swap clause and (S) over ℝ; `Hamming.lean`); 8.3 open |
| 9 | Thin $T$-Module, I | `thin-module-structure` · `thin-is-dualthin` · `measure-wi` · `measure` | **Lemma 9.2 proved** (`thin_parameters_real`, `thin_module_structure`, `thinPoly_aeval`; `Thin.lean`) |
| 10 | Thin $T$-Module, II | `orthogonality` · `determined-by-m` · `isomorphic` | 10.1 stated (`Thin.lean`) |
| 11 | Examples of $T$-Module | `principal-module` · `baiparite-principal` · `distance-regular` | Def 11.1 defined; 11.2, 11.3 open (`DistanceRegular.lean`) |
| 12 | Distance-Regular | `distance-reguarity` · `two-thin-modules` | **Lemmas 12.1 and 12.2 proved in full** (`DistanceRegular.lean`, `TwoThin.lean`; 12.2 (iii) carries the measure-nonvanishing side condition the notes' own proof needs) |
| 13 | Modules of a DRG | `two-principal-modules` · `distance-regular-x` · `dim-diameter` | 13.2, 13.3 open |
| 14 | Parameters of Thin Modules, I | `basic-data` · `thin-endpoint1` | **14.2 (iii) proved** (`basic_data_diam_bound`, the diameter bound `D ≤ 2r+d`, with the attained-diameter repair `hDex`; wave 3); 14.2 (i),(ii), 14.3 open |
| 15 | Parameters of Thin Modules, II | `complete-graph` · `sedond-and-largest-ev` | 15.2 open |
| 16 | Thin Modoles of a DRG | `ith-incidence` · `incidence-matrices` · `endpoint1` · `aixigi` | 16.1 defined; 16.2 stated (`DistanceMatrix.lean`) |
| 17 | Association Schemes | `association-scheme` · `incidencemat-of-as` · `dr` · `gen-tr` · `gen-tr-case` · `centralizer-alg` | Def 17.1, 17.2 defined; `AᵢAⱼ = ∑ p A` proved (`AssociationScheme.lean`) |
| 18 | Polynomial Schemes | `dr-scheme` | 18.1 open |
| 19 | Commutative Association Schemes | `ei` · `dual-bose-mesner` | **19.1 (strengthened, via `exists_isIdemBasis` + the Spectral machinery) and the Krein parameters (`hspan`/`hherm` fix) proved** (`AssociationScheme.lean`) |
| 20 | Vanishing Conditions | `pij-qij` · `phijqhij` · `vanishing-condition` · `qhij` · `vector-function-product` | **20.1–20.4 proved** (with the `kval` definition fix and the `hne`/`hherm`/`hrel` hypotheses; `Schemes2.lean`) |
| 21 | Norton Algebras | `norton-algebra` · `autom-of-norton-algebra` | 21.1 stated (Norton vanishing) |
| 22 | $Q$-Polynomial Schemes | `phijqhij2` · `q-polynomial` · `q-conditions` | Def 22.2 defined (six-clause fix); **22.3 proved**; the q-conditions bonus (Q-orthogonality, `qcoef_one_injective`) proved |
| 23 | Representation of a Scheme | `q-polynomial-space` · `representation-of-y` · `representation-of-hd2` · `equivalence-of-representation` · `rep-of-scheme` | Def 23.2 defined; 23.4 stated |
| 24 | Balanced Conditions, I | `q-poly-representation` · `balanced` | **24.2 (the (ia)⇒(ic) half — the direction the notes prove) proved** (`Schemes2.lean`) |
| 25 | Balanced Conditions, II | — | proof of 24.2 continued — no separate statement in the notes |
| 26 | Representation Diagrams | `beta` · `dual-eigenvalues` | 26.1, 26.2 open |
| 27 | $P$-and $Q$-Polynomial Schemes | `p-and-q` · `qbinomial` · `classical` · `classical-parameters` · `classical-parameters` | Def 27.3 defined; **27.4 (corrected statement) proved** (draft refuted by the one-point scheme); 27.1 open |
| 28 | The First Eigenspace of a $Q$-DRG | `EV` | **Lemma 28.1 proved (restated; draft refuted on C₈), modulo the 24.2 balanced identity** (`LateChapters.lean`) |
| 29 | Tridiagonal Pair $A, A^*$ | `aastar` | **Theorem 29.1 proved (restated per the fix-8 hypotheses; draft refuted)** |
| 30 | $R, F, L$ Matrices | `rfl-relations` · `epm-gpm` · `fr2lr2r2l` | R, F, L defined; **A = R+F+L and the memberships proved; 30.1 (ii) proved (restated, unconditional — draft refuted on the dodecahedron)** |
| 31 | The "Inverse" of $R$ | `inverse-of-r` | **Lemma 31.1 (i),(iv) proved at general RCLike** |
| 32 | Irreducible Modules of Endpoint $i$ | `action-of-r` · `vix` · `action-on-estar1v-new` · `generator-endpoint1-mod` | Def 32.2 defined; **32.1 proved (restated with stability/thinness/diameter)** |
| 33 | Algebra on First Subconstitutent | `mezerostarm` · `eonemmstar` · `tildej-tildea` · `e1starte1star` | 33.3, **33.2 (i) (`eonemmstar`)** and **33.4 (iv)** (the entry symmetry `e1star_te1star_entry_symm`, the input to Lemma 39.2) proved; 33.4 (iii) reduced to a single right-`A`-closure input, open |
| 34 | Modules of Endpoint One | `mvplusmstarvstar` · `tv` · `tv-thin` | 34.1–34.3 stated; wave 3 proved the `Ã`-cum identity, the `v⁻` lemmas and the reduction of 34.2 to a single `cyclicModule`-stability input |
| 35 | $\dim E$~1~^\*^$TE$~1~^\*^ $\leq 5$ | `dim5` | 35.1 restated; Claim 1 (`E*₁ME*₁ = Span(J̃, E*₁, Ã)`) and the `p^h_{ij}` calculus proved; the quartic-annihilator endgame reduction proved; the case split remains |
| 36 | Dual Endpoint | `dual-endpoint` | Def 36.1 defined; the three conjectures open |
| 37 | Generalized Adjacency Matrix | `1-thin-condition` · `generalized-adjacency-matrix` · `generalized-adjacecy-matrix` · `generalized-adjacecy-matrix` | Def 37.2 defined; 37.1 restated with the `Q`-polynomial hypothesis and `dim E*₁W = 1` explicit after the machine-checked 7-vertex refutation of the context-free draft (`thin_of_dim_two_eq_one_draft_false`); open (needs `fr2lr2r2l` (i)/(iii)) |
| 38 | An Injection from E~11~^\*^  to E~22~^\*^ | `e11star-to-e22star` · `Psi` · `map-e11star-to-e22star` | **38.1 (i) proved (restated — the draft was false for every graph; two-vertex E* calculus; the diameter-bound input `basic_data_diam_bound` was discharged in wave 3, so the chain closes modulo nothing)**; `Ψ` discussed |
| 39 | $A^+$ and $A^-$ | `delta-minus11` · `psi` · `aplus-aminus` · `tyx-equals-txy` | 39.3, 39.4 restated after refuting the drafts, open; wave 3 proved the `E*_{ij}` two-vertex level calculus (48 lemmas), the `S₁(x)×S₁(x)` support of `A±`, the reduction of 39.3 (ii) to two explicit inputs, and the `E*₁ ∉ adjoin{Ã,J̃}` witness for the membership defect |
| 40 | Structure of 1-Thin DRG | `endpoint-at-most-one` · `tilde-mi` · `h` · `zi` | 40.1–40.3 open; 40.4 restated, with the entry-vs-count identification `ziDelta_apply`, the level dichotomy and the triangle-free/bipartite cases proved; the general case needs the `δ^±`/`Ψ` machinery |
