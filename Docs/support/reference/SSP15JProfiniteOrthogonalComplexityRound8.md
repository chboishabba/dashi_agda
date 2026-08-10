# SSP15 indexed-j Round 8: normalized fibres, adic histories, signed multiplicity and controlled symmetry

This round continues Round 7's rule: numerical resemblance is never promoted to structure without an explicit map and law witnessing that promotion.

## 1. Pro-object versus inverse-limit object

The inverse system

```text
... -> X_2 -> X_1 -> X_0
```

is the tower/pro-object datum.  A compatible-history object `InverseLimitPoint tower`, when regarded as the actual limit in an ambient category where that limit exists, is the limit object.  The code therefore avoids calling an individual compatible history or its carrier "the pro-object".

Primary reference: Saunders Mac Lane, *Categories for the Working Mathematician*, 2nd ed., DOI `10.1007/978-1-4757-4721-8`.

## 2. Probability-normalized fibres and a literal orthogonal split

`DASHI.Analysis.NormalizedFibreAveragingExact` constructs the finite conditional-probability case with a two-point fibre of weights `1/2,1/2`.  It proves exactly

```text
fibre mass = 1
average (pullback f) = f
P (P g) = P g
P g + Q g = g.
```

`DASHI.Analysis.WeightedCoarseFineOrthogonalExact` adds the compatible weighted inner products and proves the finite adjoint identity, self-adjointness of `P`, annihilation `PQ=QP=0`, and exact coarse/residual orthogonality.

This is the finite theorem schema behind the measure-disintegration discussion.  It is not a proof of the full Rokhlin disintegration theorem for arbitrary measurable spaces.

Primary reference: Vladimir I. Bogachev, *Measure Theory*, DOI `10.1007/978-3-540-34514-5`.

Wavelet context: Stephane G. Mallat, "A Theory for Multiresolution Signal Decomposition: The Wavelet Representation", DOI `10.1109/34.192463`.

## 3. The glasses involution is constructive in the finite fibre

For a fine observable with fibre coordinates `(a,b)`, Round 8 defines

```text
J(a,b) = (a,-b).
```

For the averaging projector `P` and residual projector `Q=I-P`, Agda proves pointwise

```text
J^2 = I
J P J = Q
J Q J = P
Omega = J P J - Q = 0.
```

Thus the "same carrier/opposite decomposition" picture has a concrete finite algebraic witness.  The code does not interpret `J` as an ideological truth operator.

## 4. Associated graded data does not manufacture a split

`DASHI.Foundations.FilteredExtensionSplittingExact` puts the distinction into separate types:

```text
ShortExtension G1 J G0
SplitExtension extension
```

A split extension contains an explicit section with `project(section x)=x`.  The finite `1 + 10 = 11` equality is proved separately in `Nat`; the numeral equality is not used to synthesize a section.  This is the exact distinction between graded counting and extension/gluing data.

Primary reference: Charles A. Weibel, *An Introduction to Homological Algebra*, DOI `10.1017/CBO9781139644136`.

## 5. Decimal addresses are explicitly identified with finite residue representatives

`DASHI.Biology.DecimalResidueTowerExact` constructs, at every finite `r`, mutually inverse maps

```text
DecimalAddress r <-> Fin (10^r)
```

and proves that decimal `prefix` commutes with the canonical remainder/reduction map.  This is stronger than the Round-7 cardinality observation and is the first actual tower equivalence.

`Fin (10^r)` is used here as the finite set of canonical residue representatives.  A set equivalence alone does not create the quotient-ring operations or a ring isomorphism.

Primary reference: Fernando Q. Gouvea, *p-adic Numbers: An Introduction*, 2nd ed., DOI `10.1007/978-3-642-59058-0`.

## 6. Cardinal factorization is separated from arithmetic CRT

`DASHI.Biology.DecimalCRTResolutionExact` proves for every finite level

```text
10^r = 2^r * 5^r
Fin (10^r) <-> Fin (2^r) x Fin (5^r)
```

with exact round trips using the standard library's finite mixed-radix decomposition.

That bijection is deliberately **not** called the Chinese remainder map.  The file defines the stronger `CoherentCRTSystem` interface: an actual CRT implementation must provide inverse stage maps and prove that both directions commute with the residue-reduction maps.  This prevents a cardinality bijection from being mislabeled as arithmetic CRT.

The standard mathematical theorem motivating the interface is

```text
Z/(10^r)Z ~= Z/(2^r)Z x Z/(5^r)Z
```

because `2^r` and `5^r` are coprime.  Constructing the canonical arithmetic CRT instance and its ring laws remains distinct from the finite-set factorization already proved here.

## 7. Inverse limits are transported only through coherent tower maps

`DASHI.Biology.TenAdicInverseLimitBridge` proves a generic theorem: a levelwise equivalence commuting with the projection maps transports compatible inverse-limit histories in both directions.

It then proves:

```text
DecimalAddress histories <-> 10^r residue-representative histories
```

and exactly splits a product-tower history into a pair of histories and rejoins it.

Given an explicit `CoherentCRTSystem`, the code therefore constructs

```text
Decimal histories <-> (2-adic-style histories x 5-adic-style histories).
```

This is the correct conditional bridge to the standard `10`-adic decomposition.  It is not the full profinite completion of the integers, and this file does not yet transport quotient-ring operations to the inverse limit.

## 8. Closest multiresolution literature

Round 7/8 sits near an established non-Euclidean multiresolution literature.  These references are context for the standard machinery, not attribution of DASHI's Monster/SSP interpretation:

- Sergio Albeverio, Sergei Evdokimov, Maria Skopina, "$p$-Adic multiresolution analysis and wavelet frames", *Journal of Fourier Analysis and Applications* 16 (2010), 693-714, DOI `10.1007/s00041-009-9118-5`.
- Andrei Yu. Khrennikov, V. M. Shelkovich, M. Skopina, "$p$-Adic refinable functions and MRA-based wavelets", *Journal of Approximation Theory* 161 (2009), 226-238, DOI `10.1016/j.jat.2008.08.008`.  The paper includes a 3-adic wavelet-basis example.
- John J. Benedetto, Robert L. Benedetto, "A wavelet theory for local fields and related groups", *Journal of Geometric Analysis* 14 (2004), 423-456, DOI `10.1007/BF02922099`.
- Marcin Bownik, Qaiser Jahan, "Wavelets on compact abelian groups", *Applied and Computational Harmonic Analysis* 49 (2020), 471-494, DOI `10.1016/j.acha.2020.05.004`.
- S. V. Kozyrev, "Ultrametric pseudodifferential operators and wavelets for the case of non homogeneous measure", arXiv `math-ph/0412082`.

A cautious novelty statement is: **no established literature was identified here connecting this specific stratified/profinite multiresolution construction to DASHI's Monster/moonshine interpretation**.  This is evidence about the search neighbourhood, not a proof that no obscure precedent exists.

## 9. Occurrence is a lossy Boolean shadow; multiplicity is retained

`DASHI.Biology.SignedMultiplicityObstructionExact` defines

```text
delta_i(A,B) = m_A(i) - m_B(i) : Integer
orientation(delta) in {- , 0 , +}.
```

It proves

```text
delta_i(B,A) = - delta_i(A,B)
```

and shows concretely that multiplicities `1` and `2` have the same Boolean presence value while retaining a nonzero signed defect.  With an involution `iota` on labels it proves the exact twisted anti-symmetry

```text
twistedDelta B A (iota i) = - twistedDelta A B i.
```

This is deliberately aligned with the published distinction between occurrence and multiplicity obstructions, while not claiming a new permanent-versus-determinant lower bound.

References:

- Peter Buergisser, Christian Ikenmeyer, Greta Panova, "No occurrence obstructions in geometric complexity theory", *JAMS* 32 (2019), 163-193, DOI `10.1090/jams/908`.
- Julian Doerfler, Christian Ikenmeyer, Greta Panova, "On Geometric Complexity Theory: Multiplicity Obstructions Are Stronger Than Occurrence Obstructions", *SIAM Journal on Applied Algebra and Geometry* 4(2) (2020), 354-376, DOI `10.1137/19M1287638`.

## 10. Yin/yang is used only as a fail-closed interpretive vocabulary

The repository already contains `DASHI.Culture.YinYangPolarityBoundary`, whose authority bits make it candidate-only and non-promoting.  `DASHI.Culture.SignedMultiplicityYinYangBridgeExact` maps the exact algebraic sign states

```text
negative -> yin
zero     -> balanced middle
positive -> yang
```

and proves that swapping the multiplicity order reverses this candidate polarity.  The exact theorem is the signed-integer anti-symmetry; the cultural labels do not acquire empirical, philosophical, political, clinical, or canonical authority from the bridge.

## 11. FRACTRAN control plus wreath symmetry is now an executable machine

`DASHI.Biology.FRACTRANWreathControlledSymmetryExact` combines existing repository modules instead of rebuilding them:

```text
FRACTRANSSPTransitionExact
SignedSSPFRACTRANWeaveExact
FiniteWreathRefinementExact.
```

A controlled state has an arithmetic valuation state and a local fibre assignment.  An enabled arithmetic rule advances the first-enabled FRACTRAN state and fires the already-proved local-transform/index-permutation action.  The canonical witness computes both arithmetic and fibre effects exactly.

The file also proves a left-invertible two-bit encoding of the three local states.  That establishes finite expressive sufficiency only.  It explicitly does not identify expressive equivalence with local-rule count, MDL, execution length, normal-form size, or equivariance cost.

Cohn--Kleinberg--Szegedy--Umans is cited as a genuine precedent for group structure affecting algorithmic complexity, not as a source for this DASHI machine:

Henry Cohn, Robert Kleinberg, Balazs Szegedy, Christopher Umans, "Group-theoretic algorithms for matrix multiplication", FOCS 2005, DOI `10.1109/SFCS.2005.39`.

## 12. Reachability and cost are now separate mathematical structure

`DASHI.Biology.SpectralReachabilityComplexityExact` adds finite-step reachability and proves two generic results:

1. If every legal step preserves `Phi`, every finite reachable endpoint has the same `Phi`; unequal values therefore obstruct reachability.
2. If every legal step increases a natural-valued potential by at most `c`, an `n`-step path satisfies

```text
potential(end) <= potential(start) + n*c.
```

Violating that budget proves no path of that length exists.

It also introduces the proposed three-index carrier

```text
X[n,d,r]
```

for input size, relational/depth horizon and observational resolution, plus separate verification and search cost interfaces.  A polynomial verification bound does not manufacture a polynomial search bound.

References:

- Sanjeev Arora, Boaz Barak, *Computational Complexity: A Modern Approach*, DOI `10.1017/CBO9780511804090`.
- Ketan D. Mulmuley, Milind Sohoni, "Geometric Complexity Theory I: An Approach to the P vs. NP and Related Problems", DOI `10.1137/S009753970038715X`.

This layer proves **no P-versus-NP result**, no NP-completeness result for a DASHI fibre problem, and no Monster complexity lower bound.  The analytic projection `P` and complexity class `P` are given distinct typed tags to prevent the glyph collision from becoming a conceptual identification.

## 13. Belief in the fibre is a conditional dynamical theorem only

`DASHI.Culture.BeliefFibreReplicationExact` formalizes the narrow product-state claim

```text
(material, belief) -> (materialStep material, beliefStep material belief).
```

For this model, two different belief values over the same material state have exactly the same projected material successor.  This proves the mathematical sentence "the auxiliary coordinate lies in the transition fibre" under the stated model.  It does not establish that any actual society or political system is belief-insensitive.

## 14. Boundary records are claim-scope certificates

`DASHI.Foundations.ClaimScopeCertificateExact` now states the repository convention explicitly.  A Boolean field proved equal to `false` says that the layer does not establish/claim the proposition named by the field.  It is not itself a proof of mathematical impossibility.

A genuine negative theorem has the separate type

```text
Refutation Claim = Claim -> bottom.
```

Future descriptions of legacy `*Boundary` flags should therefore say **"this layer does not establish/claim X"**, unless an actual `Refutation X` (or equivalent theorem) has been constructed.

## Round-8 methodological summary

Round 7:

> Do not infer structure from a numeric resemblance.

Round 8:

> When structure exists, construct the maps, inverse laws, commutative squares, adjoints, involutions, invariants, and cost bounds that make the statement true; when a stronger promotion remains open, represent its required hypotheses as a stronger type rather than pretending the promotion has already happened.
