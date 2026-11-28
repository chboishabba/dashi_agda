# Paper 9 — recovered original Hecke owners and actual cusp pole removal

25 November 2026. Starting Agda PR #1546 head 98be906d665c0456949bb5212fca49c72c1b0969; Lean companion start ff8f49d720b84a5ceab63ae1e92fdb40e29b1b13. This cut corrects incomplete reuse of the repo's original Hecke programme. Source-written proof terms UNCOMPILED; no CI/kernel/benchmark. Local SymPy exact row-geometry checks only. No new arithmetic backend or separate research branch.

## Original source recovery (not new Hecke machinery)

Actual older PR #580 (closed, head 554c127e3727013d0698846eb2a88bde011c5efa, branch agent/brandt-frobenius-fricke-joint-system) has the following original source files. The identical copies also survive in the Lean repo's output-final_aristotle upstream snapshot. They were missing from the active Paper 9 branch, not missing from the research programme. Restored verbatim, including source attribution:
- DASHI/Moonshine/ClassicalFiniteHeckeCorrespondenceCore.agda, donor blob 30dd0003fe7cfbcd3e382a4440835708b2f60720, recovery 0ce2e39d12414948f0dc46e983f78dedeee4357b.
- DASHI/Moonshine/PositiveFiniteNeighbourSystemExact.agda, donor blob 22332c7e234c2a3540c09d975e8518fbfbff0f78, recovery 5a62d43606e07f598c7a5aec5ed759d02d7e6b2d.
- DASHI/Moonshine/PrimeRegularHeckeLocalGeometryExact.agda, donor blob 298e50c2ac281cf875f3d265e451ef9acfdf04a3, recovery 7a7789f77c81bfe3760888891b0cb1a69d789b37.
- DASHI/Moonshine/ClassicalCharacteristicHeckeFamilyCore.agda, donor blob 4001863ae12ddd092f68962fa703d8a932a1d8d8, recovery 511d7854aa5ff1a09087953e61f77eb9e42cd493.

The original carrier ClassicalPrimeDegreeCorrespondence uses neighbour : Class -> Fin (suc degreePrime) -> Class; foldFin implements the finite readout, not merely sum. PositiveFiniteNeighbourSystemExact.fromClassicalPrime and PrimeRegularHeckeLocalGeometryExact.asPositiveNeighbourSystem preserve this carrier. The original ClassicalCharacteristicHeckeFamily separates characteristic and isogeny degree. No identification of characteristic 41, Monster prime 41 or a fixed SSP Vec15 with this characteristic-zero degree-41 cyclic correspondence.

Other actual source read:
- ClassicalHeckeWeightKSmallWordExact (blob 661651cfd252ec0647a20a86be1a66b72f75610e) normalizes the classical additive Hecke divisor-sum law, not the multiplicative modular polynomial.
- AristotleHeckeWordsSourceParityExact (98bf68d576058102ec69136b5e63a21467e8a391) and AristotleHeckeGeneralPrimePowerDecompositionExact (4934ffd4658c6d6f9e77b6af8e90156d790dc186) preserve Aristotle (Harmonic) source ownership, exact algebraic recurrence and prime-power grouping. They do not establish the actual characteristic-zero Phi41.
- DeltaAnalyticHeckeObservationSameObjectExact (5d8cca44b7420feb81fc9a3758950818af83185f) transports concrete tau(3^e) observations on the same Delta object; its native coefficient extraction seam is explicitly unpaid, despite external Lean Delta identity.
- P11Phi4CyclicVsFullHeckeExact (a53a0eeb9a8f3a51230535dc945f535be1a65ff7, #580) distinguishes cyclic degree-4 six-neighbour correspondence from full seven-contribution Hecke operator; P11Level2DoubleCosetHeckeBasisExact (8c0d3f4bbe1717bf2ee476c881a493fa55926156) is actual finite deck-orbital basis, not characteristic-zero analytic Laurent theorem. Keep their source domains.
- Ontology/Hecke/CorrespondenceRepresentation (2e6fea20798d1632cb6aa93e4264e4046081fdbc) fixed Vec15 and ReverseRepresentation (3825d886c27d998d8eb7fe491699dd258f810736) are separate ontology observers. ConwayNortonTheorem (9f2dd937ebf558ba49337aa560a6df4a835bc238) has a ReplicabilityPackage interface, not an inhabited classical Faber polynomial identity. IbrahimMonster6BCompleteReplicabilityPowerSnowballExact (1c93bcd8c9e9c686b67a2cdb9c756b1cd00f3b1d) has source-level complete replicability attribution/receipt, not literal j normalized-cusp identity.
- TriadicEisensteinTransformationTheorem owns LatticePoint, SL2Z determinant-one and forward/inverse lattice maps. Existing JInvariant369BraidModularGeneratorWeldExact (ab1c1e8367a62ce11345937bf8fa7a7672b6837c) is signed modular generator arithmetic; no new matrix geometry needed.

## Actual degree-41 specialization on original lattice carrier

New CM163ClassicalHecke41LatticeSpecializationExact.agda at 97d41dd786dc43e68f1b4e8e4bbe651e41564de6 uses the restored ClassicalPrimeDegreeCorrespondence and PrimeRegularHeckeLocalGeometry, original LatticePoint rows, and their positive operator/fold. Ordered rows (u,v) encode an actual basis before quotient:
  A_k(u,v)=(u+k v,41 v), 0<=k<41;
  A_inf(u,v)=(41u,v).
The exact reverse chart is A_inf after A_k, followed by subtracting k times second row from first; it yields (41u,41v). A_0 after A_inf likewise yields (41u,41v). The common positive scale is retained, and the chart and correction are not replaced by a j-value. Only the later projective upper-half-plane readout forgets scale. Source terms finiteReverseCoordinate, finiteReverse, infinityReverse, dualReconstruction and actualArity are intended proof terms. characteristicProduct uses the original foldFin with multiplication and identity rather than confusing it with the additive Hecke operator. The native row-basis analytic same-object map remains separate from this algebra.

Local SymPy independently derived the projective line action over F_41, checked 84 S/T row-lattice corrections and inverse chart reconstruction, and 42 dual corrections applied to an arbitrary symbolic 2x2 row basis. 126/126 exact checks PASS. The literal Lean S permutation table matches negative modular inverses at all finite nonzero indices. Exact normalized cusp exponent and sign checks also PASS (sum 0..40=820 divisible by 41, (-1)^42=1). No native decide or kernel executed.

## A3: reuse actual pinned full modular group generation and rigidity

Pinned Mathlib v4.28.0 Mathlib/LinearAlgebra/Matrix/FixedDetMatrices.lean contains SpecialLinearGroup.SL2Z_generators : Subgroup.closure {S,T}=top, via its integral FixedDetMatrix Euclidean induction. No bespoke group generation. Pinned Mathlib NumberTheory/ModularForms/NormTrace.lean also contains SlashInvariantForm.norm/trace and ModularForm.norm; these require finite relative index and, for ModularForm.norm, bounded cusp forms. They do not directly make the pole-bearing j a holomorphic-at-cusp modular form. Paper 9's actual chart product already has the concrete finite coset owner. Reuse pinned closure plus existing MoonshineLevelOneWeightZeroPinned.levelOne_weight_zero_const (blob d793d042cddfc6362b6b28c28da4a587a47b8937) rather than introducing a second rigidity theorem.

Lean Integration/Paper9HeckePoleRemoval.lean (1bfa61fc3cb3cdf4570f65b215548e13e9eadab4, then 1cccf93c0887c653da168b17a7beaa3bb40a9906) writes invarianceFromST, productInvariant consuming actual S/T transport, jExtAnalytic/jHolo (no E4 nonzero hypothesis, since elliptic j=0 is allowed), actual chartAffine and chartHolo, productHolo and polynomialHolo. invariantZero packages a holomorphic invariant residual with zero cusp as the actual level-one weight-zero CuspForm, then consumes existing constancy and zero limit. These terms are uncompiled. No claim that the prior new proof chain has been accepted.

### Stronger reverse cut: A4 diagonal does not need the full bivariate symmetry

Let F_tau(Y)=actualProduct tau Y, J=qj. For the original degree-82 P and degree-42 fixed target slice S, set
  R_d(tau)=F_tau(j(tau))-P(j(tau)),
  R_s(tau)=F_tau(K)-S(j(tau)).
Both residuals are holomorphic on H and invariant under S,T (hence SL2Z). If the original finite replay is reflected into actual vanishing cusp limit, invariantZero proves each residual is zero. No entire bivariate Phi construction or symmetry needed for either of these two identities. In particular actualCMDiagonalRoot consumes cmProductZero and gives P(j(cmTau))=0 directly. A4 root isolation can run in parallel with full symmetric Taylor A5; do NOT make root isolation wait for symmetry.

Use the actual ramified t=exp(2pi i tau/41), t^41=q, zeta=exp(2pi i/41). Actual tParam never zero on H, tends to zero at cusp. New normalizedResidualZero consumes the analytic residual order factorization
  t^m R(tau)=t^(m+1) G(t), G continuous at 0.
Cancel the retained nonzero t^m to get R=t G(t)->0. Only this exact source order factorization is needed. New diagonalFromRamifiedReplay uses m=3362=41*82; sliceFromRamifiedReplay uses m=1722=41*42.

Original normalized factors (new Lean denominator-cleared consumers diagonalFiniteFactor, diagonalInfinityFactor, fixedFiniteFactor, fixedInfinityFactor):
  q(j(q)-j(zeta^a t))=J(q)-(zeta^a t)^40 J(zeta^a t);
  q^41(j(q)-j(q^41))=q^40 J(q)-J(q^41);
  -(zeta^a t)(K-j(zeta^a t))=J(zeta^a t)-K zeta^a t;
  -q^41(K-j(q^41))=J(q^41)-K q^41.
Multiplying 41 finite factors plus infinity gives original normalized analytic diagonal and slice. Keep the 42 factors and phase product: prod_a zeta^a=zeta^820=1, (-1)^42=1. The source producer's cyclotomic norm descends to q by cyclic root rotation; its formal log recurrence from previous cut has exact coefficients. Once actual analytic normalized factor identity and actual analytic/formal J/H/N coefficient equality are proved, prior forward Laurent coefficient replay through q^82/q^42 implies normalized t residual vanishes through degree 3362/1722 respectively. Analytic Taylor factorization then gives G. No need to check additional coefficients beyond these frontiers. The actual coefficient reflection is still open; finite receipts/hash parity are not analytic order evidence.

For A5 alone recover the full bivariate polynomial, without materializing all coefficients: for any fixed Y, the product has pole at most 42, and T-invariance eliminates fractional q exponents. Subtract its Laurent principal part/constant in the monic j^d basis, then consume invariantZero. Each fixed Y thus gives a polynomial in j of degree <=42. Interpolate at 43 distinct Y values (actual product is monic degree42 in Y) to get Phi(X,Y), with X-degree <=42. Leading coefficient in X^42 is +1 independent Y, by actual normalized product t^1722 limit. ReverseRoot + generic 42 distinct leading chart values yield symmetry by monic root count and infinitely many X. This is the same prior rigidity route, now on existing finite Hecke carrier and actual pinned group generator/rigidity owners. Remaining precise lemmas: analytic ramified product formula, actual Taylor and formal coefficient bridge, finite replay reflection/order, root enclosure; for A5 also general fixed-target Laurent pole/zero remainder, interpolation, dual monicity/symmetry and actual translated Taylor equations. No new Faber/interface layer.

## Remaining cut and attribution

A3 actual cusp coefficient/order reflection is now isolated; A4 can use diagonal-only rigidity independently of symmetry; A5 actual symmetric Taylor still needs bivariate analytic theorem. A7 prior period source consumes actual K and transverse kappa. F1-F5 original rational source binding remains; use existing Bishop interval/width/cross consumers and no new downstream adapter. No prior solvedness claim changed. See previous register Paper9ReverseSolvedActualHeckeDiscriminantPeriod20261125.md for complete A1-A7/F1-F9.

Classical Hecke/isogeny geometry: Diamond--Shurman, Broker--Lauter--Sutherland, Serre, Miyake; prior finite carrier and row/observer work remains original DASHI work in #580 and corresponding previous source owners, original Aristotle (Harmonic) formal source remains attributed; Mathlib Euclidean and rigidity ingredients retained. JMD donor contributions remain distinguished from DASHI extension. New work here: restore lost files verbatim, specialize actual ordered row basis, consume pinned full SL2 generation and zero-cusp rigidity, isolate direct ramified residual consumers. No new classical identity or native proof acceptance asserted.
