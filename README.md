# The Number of Polytope Trees and Beyond — Lean 4 Formalization

**Article:** Ali Aliev and Natalia Amburg, [*The Number of Polytope Trees and Beyond*](https://arxiv.org/abs/2610.33344v1), arXiv:2610.33344v1 [math.CO], 23 October 2026.  
**DOI:** [10.48550/arXiv.2610.33344](https://doi.org/10.48550/arXiv.2610.33344).  
**Formalization author and maintainer:** Ali Aliev (`alialiev78`).  
**Code license:** MIT.

This formalization was obtained with assistance from OpenAI ChatGPT.

This repository formalizes the enumerative model of the paper above. Its
principal objects are finite coloured facet pairings, counted with
inverse-automorphism weights. All paper references and equation numbers below
refer to **arXiv:2610.33344v1**. The correspondence table and fidelity discussion
specify the scope of the formalization.

`Article.lean` is the entry point of the complete proof library. `Challenge.lean` is a separate,
self-contained specification of 39 public claims, including explicit definitions
of the finite carriers, analytic functions, ordinary triangulation classes and
actual geometric facet maps. The comparator configuration
selects those theorem statements, enables NanoDa and allows no definition holes. The challenge's
statement placeholders are not imported by the proof library. All proofs in
`Article` are checked without `sorry`, additional axioms or native evaluation.
The default build includes both `Article` and the separate specification.

## Geometric interpretation

The geometric input `RegularCell` consists of a finite nonempty vertex set,
full affine span, transitivity of its actual isometry group on complete face
flags, and dimension at least two. Its facets are maximal proper supporting
faces. The construction uses the actual affine isometries of their intrinsic
spaces; an extension to the whole cell is not included in the definition of a
facet map.

The library proves unique extension of every vertex-preserving intrinsic facet
isometry, determinant compatibility, existence of a negative facet stabilizer,
and the signed facet system. It constructs a palette for every ordered pair of
facets, proves that its size is the order `r` of the actual facet rotation
group, and derives `tau = h*r`. No palette, reflection, restriction-surjectivity
certificate or orientation-compatibility certificate is an input to the final
`RegularCell` results.

`intrinsic_boundary_mass_formula` and `intrinsic_boundary_mass_recurrence`
count presentations whose seams carry the intrinsic facet isometries themselves,
under positive local cell symmetries and cell permutations. Their individual
stabilizers agree with those of the transporter presentations. For a cell in a
normed vector space, pointwise affine compatibility is equivalent to the group
action and induces a homeomorphism of the convex-hull quotient realizations.

These are cellular affine presentation classes with inverse-automorphism
weights. They are not bare quotient spaces classified up to arbitrary
homeomorphisms. Arbitrary pairings need not be manifolds.

All geometric modules belong to `Proofs/`, are imported by `Article`, and are
included in the default build and transitive axiom audit.

## Counting model

There are `n` ordinary cells, `h` facet slots per cell and `r` seam colours. A
finite group `L` acts on the slots, with `tau = |L|`. Distinct slots are paired;
unused slots carry boundary labels. Loops and parallel edges in the dual graph
are allowed. A fixed root cell has `h0` slots and is not renamed.

The public counts `U`, `Psi`, `R`, `T` and `W` are defined from finite matching
carriers, independently of their recurrences and formulas. Counts divide by
`n! tau^n`; `W` additionally divides by `m!`. This is symmetry-weighted
cardinality. Connectivity and circuit rank concern the dual graph. In particular,
the Lean name `W` denotes the paper's boundary-unlabelled count
`\widehat{W}_{n,\mathsf{m}}`; `R` and `T` retain the paper's boundary-labelled
normalization. The Lean parameter `h0` is the paper's `h_0` (or `\mathsf{m}_0`
in Section 6), and `Fintype.card L` is `\tau`.

For positive parameters in the theorem signatures, the tree and fixed-core
formulas, equations (20) and (27), are

```math
R_n=\frac1r\left(\frac{hr}{\tau}\right)^n\frac{(n(h-1))!}{n!},
\qquad
T_n=T_0\left(\frac{hr}{\tau}\right)^n
\frac{(n(h-1)+h_0-1)!}{(h_0-1)!\,n!}.
```

For `hn = m + 2e`, the disconnected formula, equation (46), is

```math
\widehat{W}_{n,\mathsf{m}}=\frac{(hn)!}{n!\tau^n\mathsf{m}!e!}\left(\frac r2\right)^e.
```

For example, for tetrahedra `h=4`, `r=3` and `tau=12`. The first two
boundary-labelled tree masses are `R_1=2` and `R_2=120`; after forgetting
boundary labels they are `2/4! = 1/12` and `120/6! = 1/6`. A fractional
mass is expected: each isomorphism class contributes the reciprocal of its
automorphism-group order.

Unsupported boundary sizes have zero count. The formal exponential and
root-component identities use these finite carriers, rather than defining the
counts by the desired identities.

## Correspondence with arXiv:2610.33344v1

All module names below are in `Proofs/` unless stated otherwise. Numbered
references use the published v1 numbering. Geometric construction lemmas
justify the interpretation in Section 5; they are not additional numbered
claims of the paper.

| Paper content | Proofs |
| --- | --- |
| [Statements 6.1 and 6.5](https://arxiv.org/html/2610.33344v1#S6): connected and fixed-root cut–join recurrences, including all circuit ranks; (31)–(36), (50)–(51) | `UnconditionalFinalRecurrences`, `Solution.lean` |
| [Statements 5.1–5.2 and Theorems 5.1–5.2](https://arxiv.org/html/2610.33344v1#S5): tree recurrences and factorial formulas (18), (20), (24), (27); tetrahedron specializations in Sections 3–4 | `ManuscriptTreeExplicit`, `ManuscriptFixedCoreExplicit`, `MassTreeExplicit`, `MassFixedCoreExplicit` |
| [Theorem 3.2 and Corollaries 3.2–3.3](https://arxiv.org/html/2610.33344v1#S3.ThmTh2): polynomial Lagrange–Bürmann theorem and the coefficient-extraction applications used for (11)–(12) and (20), (27) | `LagrangeBurmannPolynomial`, `RaneyApplication`, `ScaledRaneyApplication` |
| Formal differential equations: (19), (26), (37), (39), and the fixed-root equations in the proof of Statement 6.6 | `AuxiliarySeriesDifferential`, `AuxiliaryRecurrenceSolution`, `DisconnectedGeneratingPDE`, `CountingSeriesDerivations` |
| [Remarks 3.4, 4.4 and 5.4](https://arxiv.org/html/2610.33344v1#S5.Thmrem4): identities (13), (17), (29), (30) | `MainBinomialConsequences` |
| [Corollaries 5.1 and 5.2](https://arxiv.org/html/2610.33344v1#S5.Thmcorollary1): tree and fixed-core asymptotics | `AffineFactorialStirling`, `ConcreteTreeAsymptotics` |
| [Lemma 6.1 and Appendix C](https://arxiv.org/html/2610.33344v1#S6.Thmlem1): boundary support and vanishing | `StratumBalanceSpecialization` |
| [Statements 6.3 and 6.6](https://arxiv.org/html/2610.33344v1#S6.Thmstat3): the formal identities `W = exp V` and `Xi = W Psi` | `ConcreteExponentialFormula`, `ConcreteFormalExpPair`, `ConcreteXiConvolution` |
| [Statement 6.3 and Remark 6.3](https://arxiv.org/html/2610.33344v1#S6.Thmrem3): disconnected recurrence (43), coefficient formula (46), and Hermite formula (47) | `DisconnectedPairingFormula`, `ConcreteWTotalHermite` |
| [Statement 6.4](https://arxiv.org/html/2610.33344v1#S6.Thmstat4): disconnected asymptotic with no additional asymptotic hypothesis | `UnconditionalMatchingAsymptotic`, `PublicationAsymptotic` |
| [Section 7](https://arxiv.org/html/2610.33344v1#S7): the one-dimensional case `h=2`, (60)–(61) | `HtwoExplicitFormulas` |
| [Theorem 3.1, Corollary 3.1 and Appendix A](https://arxiv.org/html/2610.33344v1#A1): radicals, analytic generating functions and coefficients; Statements A.1–A.3, (63)–(64) | `AppendixAClosedForms`, `AppendixARadicals`, `AppendixAAnalytic`, `ScalarAnalyticSeries` |
| [Appendix D](https://arxiv.org/html/2610.33344v1#A4): all maximizing boundary sizes, including the odd case of Remark D.1 | `AppendixDMaximum`, `ArticleStatements` |
| [Appendix E](https://arxiv.org/html/2610.33344v1#A5): the implication (30) implies (29), using (73)–(75) | `AppendixE` |
| Stellar subdivision: actual complexes, final-graph reconstruction and a global relative homeomorphism | `IntrinsicStellarFaces`, `IntrinsicGraphRecovery`, `GlobalStellarHomeomorphism` |
| Actual Euclidean symmetry groups and intrinsic restriction | `FiniteEuclideanSymmetry`, `EuclideanFacetRestriction`, `ExposedFacetRigidity` |
| Actual supporting faces, full flags, rigidity and unique extension | `SupportingFaceFlags`, `GeometricFlagTransport`, `GeometricFacetExtension`, `IntrinsicFacetRestriction` |
| Orientation, reflections and the geometric signed facet system | `FacetOrientationCompatibility`, `ConcreteGeometricFlagInterface`, `RegularPolytopeReflections`, `AllFacetsOrientedFlags` |
| All ordered facet pairs, intrinsic palettes and `tau = h*r` | `EuclideanFacetTransporters` |
| Mass formula, recurrence, individual stabilizers and quotient realizations for regular cells | `EuclideanRegularPolytopeMass`, `IntrinsicGeometricPresentations`, `EuclideanPolytopeRealization` |
| Uniform affine simplex palettes in every dimension | `SimplexUniformPalette` |
| General signed facet / regular flag interface, with explicit geometric inputs | `RegularFacetPalette`, `RegularFlagSystem`, `RegularFacetRestriction`, `AffineFlagRigidity`, `RegularPolytopeMass` |
| [Corollary 5.3](https://arxiv.org/html/2610.33344v1#S5.Thmcorollary3): ordinary triangulation classes in dimension at least two | `IntrinsicCorollary53`, `IntrinsicExponentialLowerBound`, `RelabellingCardinality` |
| Affine gluing presentations and equivariant quotient realizations | `SimplexPairingRealization`, `SimplexFacetTransport`, `GeometricPresentationAction`, `GeometricRealizationEquivariance`, `GeometricPresentationMass` |

Intermediate reduction lemmas may have hypotheses; the concrete endpoints
listed above discharge the counting and asymptotic inputs. Exact parameter
restrictions are part of the Lean statements.

## Analytic branches

Put `q=h-2>0` and assume `tau=hr`, as in the regular-polytope special cases.
The counting series satisfies `Y=X+Y^(q+1)` with constant coefficient zero.
Its zero-constant branch is unique. The analytic inverse function theorem
supplies a convergent branch for every such `q`.

For `h=4`, the cube roots in Cardano's formula are coupled: their product is
`1/3`, and their values at zero are `-i/sqrt(3)` and `i/sqrt(3)`. Thus their
sum vanishes at zero. Independent principal cube roots would give the wrong
branch.

For `h=5`, Ferrari's resolvent uses a cube root `a` with `a(0)=1`. Its companion
is `4t/(3a)`. The square roots are normalized to one at zero. Their denominators
are proved nonzero near zero, and the selected root satisfies `y^4-y+t=0`.

The analytic primitive is

```math
R(t)=\frac1r\left(\frac{y(t)^h}{h}-\frac{y(t)^{2h-2}}2\right),
\qquad R'(t)=\frac{y(t)-t}{r}.
```

The proof identifies its full Taylor series: the coefficient at degree
`(h-2)n+2` is `R_n/((h-2)n+2)!` for `n>0`, and all other coefficients vanish.
The fixed-core function is `T_0 y(t)^h0/h0!`, with the corresponding finite-count
coefficients. The triangle branch agrees with the real square-root expression
in (64) on `t<=1/4`; the Taylor identification is local at zero.

## Maximum in Appendix D

Let `N=hn`, `p=N mod 2`, and `r>0`. The smaller maximizing index is

```math
\alpha=\frac{\sqrt{r^2+6r+1+4rN}-(3r+1)}{2r},\qquad
M=p+2\max\left(0,\left\lceil\frac{\alpha-p}{2}\right\rceil\right).
```

The maximizer is unique unless `N=M+r(M+1)(M+2)`, in which case the maximizers
are exactly `M` and `M+2`. This covers parity, endpoints and small sizes. For
tetrahedra (`h=4,r=3`) a tie is impossible. This gives a precise version of the
paper's alternative between two neighbouring indices.

## Topology and Corollary 5.3

A finite simplicial complex is represented by its finite family of maximal
faces; every subset of a maximal face is a simplex. Its realization consists
of nonnegative barycentric coordinates supported in a maximal face and summing
to one. `stellarHomeomorph` constructs a homeomorphism from the subdivided
realization to the original one. The unchanged exterior is fixed, and explicit
linear formulas describe the inverse on its finitely many sectors.

Let a fixed finite pure d-dimensional complex K triangulate M, with d >= 2
and v vertices. Write a_M(N) for the ordinary number of combinatorial
isomorphism classes of finite pure d-dimensional triangulations of M on exactly
N vertices. For n >= 1, the project proves

```math
a_M(v+n) \ge \frac{2^{n-1}}{(v+n)^v}.
```

For every fixed 1 < c < 2, it consequently proves a_M(v+n) >= c^n for all
sufficiently large n. The construction is a binary subfamily of the paper's
inductive subdivisions. Graph reconstruction and preservation of homeomorphism
type are proved; neither is a hypothesis of the final corollary. The initial
triangulation and its homeomorphism to M are inputs.

`triangulationCount` is a quotient cardinality of actual finite complexes under
vertex permutations. It is not an inverse-automorphism-weighted count. The
polynomial denominator bounds the loss from forgetting the v old vertex names.
The construction also has exactly f + dn maximal simplices after n insertions,
where f is the initial number; exact-size face counts follow this progression.

## Fidelity and verification scope

The enumerative, formal-series and analytic results use the finite facet-pairing
model described above. General regular-cell palettes and geometric mass formulas
are derived from the concrete geometric input, not assumed. The simplex
specialization also proves `r = (h-1)!/2` and `tau = h!/2` explicitly for `h >= 3`.

Corollary 5.3 concerns ordinary triangulation classes for a fixed finite pure
initial triangulation of dimension at least two, with the precise lower bound
stated above. The formalization does not attempt to solve the paper's open
questions or classify arbitrary geometric quotients.

`Challenge.lean` contains 39 intentional statement placeholders for the
Comparator specification. It is not imported by `Article`. The proof library
has no `sorry`, added axioms or native-evaluation proofs. The axiom audit permits
only `propext`, `Quot.sound` and `Classical.choice`.

The selected statements comprise the cut–join recurrences and factorial
formulas; the normalized radical branches and analytic coefficient
identifications; the Appendix D maximizers and binomial identities; the
formal exponential formula and its differential identity; the tree, fixed-core
and disconnected asymptotics; the ordinary-class bounds of Corollary 5.3; and
unique extension of every intrinsic facet isometry between actual facets.
The exact declaration list is `comparator.json`.

The remaining geometric results, including intrinsic presentation masses,
orientation compatibility and quotient-realization homeomorphisms, are proved
in `Article` and covered by the project-wide axiom audit and kernel replay.
They are supporting library results rather than additional declarations
selected by this Comparator configuration.

No claim of mathematical novelty, exhaustive literature comparison,
independent human mathematical review or Palomar registration is made.
The source is the public preprint arXiv:2610.33344v1 by Ali Aliev and Natalia
Amburg. The paper itself is available from arXiv and is not distributed in
this code archive. The MIT license covers this repository's code, not the
arXiv article. This repository contains the substantive proof development;
it is not a wrapper around an
external formalization. Mathlib and its exact dependencies are acknowledged
in the dependency manifest.

Current local verification results and their precise scope are recorded in
`verification.json`. A local check is distinct from the registry's own
mechanical verification and editorial review.

## Citation

```bibtex
@misc{aliev2026numberpolytopetrees,
  title         = {The Number of Polytope Trees and Beyond},
  author        = {Ali Aliev and Natalia Amburg},
  year          = {2026},
  eprint        = {2610.33344},
  archivePrefix = {arXiv},
  primaryClass  = {math.CO},
  doi           = {10.48550/arXiv.2610.33344},
  url           = {https://arxiv.org/abs/2610.33344v1},
  note          = {Version 1, 23 October 2026}
}
```

`CITATION.cff` supplies the same preferred paper citation for GitHub.

## Reproducibility

Lean is pinned to **4.35.0-rc2**. Mathlib is pinned to
`065356127b1dc0016f66b7283ce0ce2c4055aa55`; its toolchain agrees with the project.
The complete transitive dependency lock is `lake-manifest.json`.

```sh
lake exe cache get
lake build
lake env lean Audit.lean
lake env bash scripts/check_kernel.sh
```

The GitHub workflow runs the build, axiom audit and kernel replay. `Audit.lean` checks all
imported project declarations against `propext`, `Quot.sound` and
`Classical.choice`. The verification record is `verification.json`.

`leanchecker` replays project declarations through the Lean kernel. It uses the
pinned imported dependencies and is not an independent implementation of Lean.

The separate `Comparator and NanoDa` workflow runs

```sh
bash scripts/run_comparator.sh
```

This uses the pinned toolchain's `lake comparator`, its export format, Lean's
kernel and the bundled independent NanoDa kernel. It requires Linux with
working `bubblewrap` isolation. The workflow preserves the result log.
