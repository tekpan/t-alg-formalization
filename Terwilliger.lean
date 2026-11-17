/-
Copyright (c) 2026 Yushan Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yushan Pan
-/

import Mathlib
import Terwilliger.Basic
import Terwilliger.Subconstituent
import Terwilliger.PerronFrobenius
import Terwilliger.CollatzWielandt
import Terwilliger.Cayley
import Terwilliger.Hamming
import Terwilliger.DistanceRegular
import Terwilliger.Thin
import Terwilliger.DistanceMatrix
import Terwilliger.AssociationScheme
import Terwilliger.Schemes2
import Terwilliger.RFL
import Terwilliger.LateChapters

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
# Terwilliger algebras

A Lean 4 formalization of P. Terwilliger's *Lecture Note on Terwilliger Algebra*
(edited by H. Suzuki, <https://icu-hsuzuki.github.io/t-algebra/>), modulo
Mathlib.  All forty chapters are represented; see `COVERAGE.md` for the status of
each labelled statement and `ROADMAP.md` for what remains.

The library, in the order of the notes:

* `Terwilliger.Basic` — Chapter 1: the adjacency matrix, the subconstituent
  projections `Eᵢ*(x)`, the algebras `M`, `M*(x)`, `T(x)`, `T`-modules,
  irreducibility, and Lemma 1.8 (i)/(ii).
* `Terwilliger.PerronFrobenius` — Chapter 2: reducible/bipartite matrices, the
  Perron–Frobenius theorem.
* `Terwilliger.CollatzWielandt` — Chapter 2: the variational half of
  Perron–Frobenius: the compactness of the nonnegative unit sphere, the
  first-order condition at a maximiser of the quadratic form, and the strict
  positivity of such a maximiser for an irreducible matrix.
* `Terwilliger.Cayley` — Chapter 3: Cayley graphs, vertex transitivity, characters.
* `Terwilliger.Subconstituent` — Chapter 4: `Eᵢ* A Eⱼ* = 0` for `|i - j| > 1`,
  endpoints and diameters, commutativity of `M` and `M*(x)`.
* `Terwilliger.Hamming` — Chapters 5–8: `H(D,2)`, `J(D,N)` and the thin condition
  `(TH) ⇔ (C) ⇐ (S) ⇐ (G)`.
* `Terwilliger.Thin` — Chapters 9–10: the parameters `aᵢ(W)`, `xᵢ(W)` of a thin
  module, the basis `wᵢ = Eᵢ* Aⁱ w₀`, and the orthogonality relations.
* `Terwilliger.DistanceRegular` — Chapters 11–13: intersection numbers,
  distance-regularity, the trivial module, and Lemma 12.1.
* `Terwilliger.DistanceMatrix` — Chapter 16: the distance matrices `Aᵢ`.
* `Terwilliger.AssociationScheme` — Chapters 17–19: association schemes,
  association matrices, the Bose–Mesner algebra.
* `Terwilliger.Schemes2` — Chapters 20–27: the vanishing conditions, the Krein
  parameters, Norton algebras, `Q`-polynomial schemes, representations and the
  balanced conditions.
* `Terwilliger.RFL` — Chapters 30–31: the raising, flat and lowering matrices and
  the partial inverse of `R`.
* `Terwilliger.LateChapters` — Chapters 28–40: the tridiagonal pair theorem, the
  modules of endpoint one, generalized adjacency matrices, `Ψ`, `A⁺`/`A⁻` and the
  constants `zᵢ`.
-/

