# Clifford full multivector, SU3 colour, Lorentz dimension, Cayley–Dickson and Diamond MCG max-cut

## Full Cl(3,1) constructive finite algebra
`scripts/check_cl31_full_multivector_product.py` implements the entire canonical ordered signed 16-blade product of Cl(3,1), e0²=-1, e1²=e2²=e3²=+1. For basis masks a,b:
```text
productSign(a,b) = (-1) ^ (sum_{j in bits(b)} popcount(a >> (j+1)) + bit0(a & b))
productBlade(a,b) = a XOR b.
```
(The first sum counts swaps required to restore ascending basis order; the bit0 intersection handles the negative time axis.) The script checks all 16³=4096 associativity triples, diagonal generator squares, all anticommutations, the Pin e1 reflection on all four generators, and (e1e2)²=-1. By **bilinearity**, basis associativity extends to arbitrary finite-support multivectors over any associative commutative coefficient ring. This yields a mathematical complete construction of the finite free rank-16 Clifford algebra at the executable rational/integer level. It is not a kernel-checked formal Agda theorem; the bridge into the existing `ConcreteCl31LinearExtensionBoundary` is still required. This is significantly stronger than merely declaring a record.

## Colour obstruction — precise steelman and available escape
Older owners `ColourFromNcThreeLanesReceipt` and `ColourSU3FromCoprimeLanesReceipt` equate three unequal prime-lane carrier weights to an SU3 colour metric; this **explicitly breaks invariance**. To test this: for metric diag(w1,w2,w3), any unitary mixing of axes i,j fails to preserve the metric unless wi=wj. If the weights represent *flavour masses, labels, or basis normalizations* rather than colour-gauge kinetic metric, the physically motivated repair is NOT requiring equal quark masses, but separating:
  - a three-complex-dimensional colour fibre with canonical invariant Hermitian metric h=I and det-one unitary transformations SU(3);
  - independent family/flavour sectors with nondegenerate masses in gauge-singlet or suitable covariant Yukawa terms;
  - actual fundamental and conjugate representations, a nonabelian su3 connection with 8 gauge boson directions, curvature dA+A∧A, Yang–Mills action, gauge constraints and physical matching.
The mathematical freedom to **choose a different invariant colour metric** solves the algebraic candidate obstruction, but does NOT show that the originally given prime-lane metric is physically colour-neutral. It changes the claimed physical identification and must be justified by a producer map. Colour Weyl S3 is also not literally the full SU3 group.

## KK / nonabelian extension
The 5D KK circle connection is U1; tensoring or taking product with a separate SU3 principal bundle can add independent nonabelian structure. A geometrisation purely from internal compact isometries requires further geometry, e.g. a fibre with an SU3 isometry action (not a 1D circle). The actual 4+1 Ricci scalar and coupled equations remain unpaid.

## Existing proven/conditional owners
- PR #246 changed files `CliffordQuotientUniversalTheorem.agda`, `ContinuousSpin31LorentzCover.agda`, `LargePosetContinuumLorentz31.agda`. Need exact-head theorem review and direct owner integration before duplicating complete universality/Spin or claiming dimension selection.
- `DASHI/Algebra/Quantum/LorentzSignatureUniqueness.agda` proves one timelike direction plus d spacelike signs -> canonical (d,1), but **not d=3** without further geometrical selection.
- Cayley–Dickson rational complex→quaternion and rational octonions supply a well-defined algebraic extension route. Imaginary i alone cannot imply every mathematical object as a theorem; steelman is *universality within an explicitly selected category of complexified modules and geometric representations*, with real structure recovered via antilinear involution. Excluding objects with no chosen complexification is necessary to avoid a false universal claim.
- PR #1238 (today's Diamond MCG) actually imported PR #1239 KK additive gauge module on its branch, and added `NVDiscreteGaugeCurvatureBridgeExact` composing discrete gauge curvature, affine sensor field and spin-one resonance. Its own documentation explicitly calls physical flux conversion/calibration and 5D reduction outstanding. It is a **consumer of KK** at local gauge-invariance level, not evidence that magnetic observations uniquely validate KK.
- User's 3/6/9/18/27 notation denotes line, glued lines, sheet, glued sheets, compatible cube or graph extension, not total state counts. A twelve-step motion samples a nine-site grid; no twelve-site lattice is asserted.

## Kernelisation cutset
1. Promote the executable 16×16 basis multiplication table and exhaustive associative witness into an Agda `Fin 16` signed monomial algebra and complete sum algebra; reuse PR #246's universal quotient theorem and `ConcreteCl31Basis` rather than adding a competing universal-property axiom.
2. Construct the typed Pin twisted adjoint on full vectors with a genuine product proof; transport mirror-equivariance to balanced-ternary spatial x axis. Reflections do not belong to SU2, while two reflections have an even Spin representative.
3. Provide SU3 fundamental/adjoint exact matrix carriers, invariant h and the actual distinction between flavour masses and colour geometry. Re-assess the old candidate obstruction under the revised, declared physical mapping.
4. Inspect PR #246 physical 3+1 large-poset constructor and verify its assumptions are inhabited by an actual physical carrier, not merely structured theorem declarations.
5. Glue KK circle U1 to nonabelian SU3 gauge producers with explicit same-object map; do not treat product-bundle existence as derivation of physical strong interaction.
6. Use PR #1238 NV sensor as a falsification/calibration consumer with units and uncertainties and PR #1235 for principal U1 cocycles.

## Acceptance
```sh
python3 scripts/check_cl31_full_multivector_product.py
```
Script checks are executable finite verification, not Agda kernel. No external physical sector promoted here.
