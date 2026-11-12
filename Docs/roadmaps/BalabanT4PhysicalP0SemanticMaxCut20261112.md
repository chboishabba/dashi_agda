# Bałaban T4 physical P0 — semantic four-orbit max-cut (2026-11-12)

## Source owners

- DASHI/Physics/YangMills/BalabanClayT4LiteralOneLoopBoxEvaluatorExact.agda: actual DiagramExpression, TrigAtom, LiteralScalarIntegrandExpression, BoxTrigEnvironment, RationalIntervalArithmetic, and LiteralGeneratedBoxEvaluator
- BalabanClayT4WilsonOneLoopJointMomentumEquivarianceExact.agda: actual signed-permutation action on atoms and expressions
- BalabanClayT4WilsonOneLoopOrbitEvaluationTransportExact.agda: pre-existing structural expression evaluation covariance
- BalabanClayT4HypercubicOrbitGeometryExact.agda and BalabanClayT4HyperoctahedralGridOrbitExact.agda: pre-existing 256-cell grid, infrared 16, regular orbit sizes 64+96+64+16=240
- BalabanClayT4LiteralEvaluatorFourRepresentativeReductionExact.agda: pre-existing syntax-based conditional orbit transport

## Implemented on this branch (source-written, kernel-unverified)

1. BalabanClayT4LiteralSemanticSevenGeneratorTransportExact.agda:
   ConcreteAtomGeneratorCovariance exhausts the original five TrigAtom forms: sineHalf, cosineFull, hatMomentumSquared, colorCasimir and gaugeParameter. The original sign-sensitive Joint.transformAtom is used throughout. The new seven-generator semantic certificate gives same-box evaluation equalities for the *actual selected* regularIntegrand, not syntactic equality of ASTs. It compiles atom covariance to the original GeneratorEnvironmentCompatibility and transports the source evaluator along the existing generated orbit paths.

2. BalabanClayT4SemanticFourRepresentativeQuadratureExact.agda:
   Extracts four literal CertifiedBoxQuadrature values from the SAME LiteralGeneratedBoxEvaluator and exposes their exact recursive expression values and the 240-cell-to-four-representative evaluator equality. This does not create four numerical quadrature receipts or assume their analytic soundness.

3. BalabanClayT4OuterRankTwoPerAxisExact.agda:
   Proves the exact finite outer-axis tally 2m on the genuine generated box codes. The physical scaled sine-squared denominator inequality is still a separate analytic gate.

4. scripts/check_balaban_t4_semantic_p0_exact.py:
   Supplemental deterministic exact-rational geometry and sign-aware interval-division regression; Agda remains the golden proof authority.

## Corrections to the attached four-gate proposal

- An individual signed coordinate projection is not flip-invariant as a scalar; a sineHalf atom is ODD under a flip. Coordinate covariance must carry the corresponding expression action and environment.
- cos(q_mu-q_nu) becomes cos(q_mu+q_nu) under flipping q_mu; evenness of cosine alone does NOT prove invariance of the original full Wilson/ghost/Haar scalar under individual coordinate flips.
- For numerator [-2,1], strictly positive denominator [2,4], the true interval division hull is [-1,1/2], while the proposed sign-blind formula gives [-1/2,1/2] and is unsound. A verified quotient needs all four corner quotients or a proven numerator sign.
- Four pointwise expression enclosures are not four certified integrals: real quadrature receipts require volume, midpoint/Hessian/error and enclosure soundness on the exact source integrand.
- Full B4 orbit reduction requires joint external-momentum equivariance. If the external momentum stays fixed on axis 0, the source has a conservative seven-class stabilizer route rather than four classes.

## Unpaid physical max-cut

| Gate | Exact remaining lemma or evidence | Status |
| --- | --- | --- |
| P0.0 | Inhabit the genuine LiteralDiagramExpressions, LiteralWardExpressionProofs and LiteralScalarIntegrandExpression with selected physical Wilson, ghost and Haar terms, fixing external momentum convention | OPEN |
| P0.1 | Prove transformed atom intervals for each actual BoxTrigEnvironment, all selected B4 generators | OPEN |
| P0.2 | Prove the seven target-box *semantic* equalities for the exact literal regularIntegrand, not a similarly named proxy | OPEN |
| P0.3 | Prove physical q=pi*x scaling and 4 sin^2(q_mu/2)>=2 on outer coordinate cells; connect the sum to the actual hatMomentumSquared atom and finite rank 2m | OPEN (finite tally source-written) |
| P0.4 | Prove positive denominator and sound sign-aware interval quotient, with numerator bounds on original source | OPEN |
| P0.5 | Construct actual four quadrature/error/volume enclosures and fold into the certified 240-cell integral; use seven classes if axis-fixed | OPEN |
| P0.6 | Local pinned Agda kernel acceptance and first-error repair of the three new source modules | OPEN |

The source search did not find a constructed physical LiteralScalarIntegrandExpression inhabitant; an abstract record signature is not such an inhabitant. This is the highest-information remaining gate. Do not promote P0 or the Yang–Mills E1/D1/D2/N1/G1 physical gates from source-written interfaces.

## Local verification

Run python scripts/check_balaban_t4_semantic_p0_exact.py. Check the three Agda modules with the pinned local Agda 2.9 checker and their transitive imports. CI is not required.

Attribution: original lattice gauge theory source remains with Wilson, Faddeev-Popov, Bałaban and the cited method authors. DASHI owns the new finite semantic proof compilation and four-orbit transport wiring. No new finite orbit theorem substitutes for a physical one-loop integrand or continuum mass-gap proof.


## Adversarial follow-up on the source API

- The exact original flip counterexample, `originalSineHalfFlip0NotSyntacticallyInvariant`, now proves in Agda syntax that the literal sineHalf(loopMomentum,axis0) atom becomes a different constructor (negate rather than atom) under flip0. This does not refute possible full-integrand symmetry; it shows why atom covariance and full-scalar invariance must be different obligations.
- The source TrigAtom grammar has three momentum roles: loopMomentum, externalMomentum and shiftedMomentum. The rank lower bound for the unshifted \\hat{q}^2 is **not** automatically a positive bound for every shifted propagator denominator \\hat{q+p}^2. Each literal denominator appearing in gauge and ghost terms needs its own positivity certificate, and the fixed-axis versus joint external-momentum convention must be tracked.
- A pointwise functional equality under B4 need not imply propositional equality of the two RationalInterval evaluations: interval dependency and expression-tree shape can change enclosures. The new seven-generator record asks for the stronger *evaluated interval equality* at the selected boxes. If a literal expression proves only enclosure inclusion, the correct remedy is a separate sound-inclusion transport using the selected interval backend, not an assumed equality.
- Therefore neither the new semantic certificate TYPE nor the four receipt selectors is evidence that the physical P0 gate is already inhabited. The next highest-information action is constructing the exact literal scalar-source instance and checking which of seven semantic equalities is actually true for its momentum convention, before trying to certify the four quadratures.
