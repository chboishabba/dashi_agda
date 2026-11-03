## Subsequent exact nonvacuous admissibility and true projective-completeness payment

The concrete original TSVF Q.ProjectiveMeasurement now also has theorem terms projectorsSumToIdentity, rightAfterWrongZero and wrongAfterRightZero: the right/wrong coordinate projectors **sum to the identity on the entire coordinate carrier** and are mutually orthogonal, in addition to being idempotent.

To prevent the selected admissibility relation from being the trivially true predicate, the finite source was strengthened from a permissive two-outcome fixture to a **three-history predicate** on the original BidirectionallyAdmissibleHistoryFibre owner: admittedRightHistory and admittedWrongHistory carry explicit proofs for the same selected initial/final boundary, while excludedHistory is impossible by a source-written excludedCannotBeJointlyAdmissible no-go. Only admitted histories can be mapped to the physical coordinate projector; the excluded case has no constructor. The original Q.TSVF selected projectors still match, and the original ABL normalization/Born-overlap calculations remain source-written against this tighter fibre. This *remains* a finite constructed admissibility model, not a law selecting real cosmic histories.

A further static proof-typing risk was reduced by expanding the Nat left-unit multiplication step explicitly in rightOriginalABLDenominator and wrongOriginalABLDenominator. All changes remain unverified by an actual Agda compiler; declarations and local proof terms are not a kernel receipt.

# TSVF admissible-from-both → quantum ABL → environmental overlap: maximum-cut implementation

**3 November 2026. SOURCE-WRITTEN; Agda kernel and full physical quantum construction pending.** This is the quantitative continuation of [TSVF macroscopic reversibility and multiverse audit](TSVFMacroscopicReversibilityMultiverseBidiSourceAudit20261103.md).

## The correct source-owned mathematical claim

The original module DASHI/Physics/Foundations/BidirectionallyAdmissibleHistoryFibreExact.agda defines a History and two boundary sets with admissibleFromBoth(initial, final, history). It means that a history is compatible with BOTH boundary sides. It does **not** mean a unique forward path, strong path amplitude, nonzero overlap, or observed world.

DASHI/Foundations/TwoBoundarySystem.agda has the generic initial/final compatibility and forward/backward legs. DASHI/Quantum/TSVF.agda already has the quantum data of forwardState, backwardState, transitionAmplitude, transitionWeight, ABLContext, and original ablProbability:

\[
A_h=\langle\phi_t|P_h|\psi_t\rangle,\quad w_h=|A_h|^2,
\qquad P(h|B_\pm,\mathcal M)=w_h/\sum_{h'\in\mathcal M} w_{h'}
\]
for a genuine positive denominator and valid projective outcome family.

**Crucial distinction:** membership in a bidirectionally admissible history fibre is a logical predicate; the surviving environment overlap q = |〈epsilon_1(N-n)|epsilon_2(N-n)〉|² is a quantitative Hilbert inner product between two environmental branch records. Admissibility does not supply an amplitude or guarantee it is nonzero. A countermodel in the new module proves precisely that negative result. This also distinguishes unobserved histories from many physically existing universes.

## Two new Golden source modules, with real original-owner instantiation

### A. TSVFAdmissibleQuantumOverlapRobustnessExact.agda

- Imports and reuses the actual ORIGINAL BidirectionallyAdmissibleHistoryFibreExact and DASHI.Quantum.TSVF, rather than inventing another two-boundary interface.
- AdmissibleTSVFQuantumSource carries two right/wrong histories from ONE selected boundary pair and maps allowed histories into actual original Q.QuantumSurface projectors.
- The right and wrong amplitudes are defined by original TSVF.transitionAmplitude; their Born weights by the original normSquared.
- SourceMatchedABLMeasurement constructs an identification with the original Q.ProjectiveMeasurement, and sourceMatchedOriginalABLNormalizes proves a binary normalization law from matched total, positivity and the scalar quotient-additivity laws. Its generic theorem is CONDITIONAL; its physical projector and complex scalar algebra inputs are not yet inhabited.
- Constructs explicit rational real site vectors epsRight=(5,0)/5 and epsWrong=(3,4)/5, with unit norm and inner product 3/5. All k independent tensor factors are represented with length-indexed Vec; tensorDot, tensorPowerMultiplicative, and actualTensorSquaredOverlapIsNineOverTwentyFivePower prove EXACTLY
  \[
  \frac{|\langle \epsilon_R^{\otimes k}|\epsilon_W^{\otimes k}\rangle|^2}
       {\|\epsilon_R^{\otimes k}\|^2\|\epsilon_W^{\otimes k}\|^2}
  = (9/25)^k.
  \]
- BinaryRationalMass represents exact normalized rational probabilities by two numerators over one common positive denominator. selectedBornMass(k) has right=25^k, wrong=9^k, total=25^k+9^k, denominator positivity, exact sum law, right≥wrong and wrong-branch tail bound
  \[
  P_W=\frac{9^k}{25^k+9^k}\le(9/25)^k.
  \]
- weightedBornMass treats nonnegative **effective Born-weight** disturbed factors Gamma_R/Gamma_W and proves positive normalized total for Gamma_R>0. It has a genuine adversarial witness at k=2: Gamma_R=1 gives right=625, Gamma_W=100 gives wrong=8100, so *a large number of surviving records alone is not sufficient*.
- A zero wrong factor has an explicit zero-wrong-mass case, NOT division by zero. Original admissible left history may have zero weight in a valid countermodel.

### B. DASHI/Quantum/TSVFConcreteAdmissibleQubitABLExact.agda

This module is the crucial stronger step: it **constructs** the original Q.QuantumSurface, Q.TSVFEnsemble, Q.ProjectiveMeasurement, Q.ABLContext, and Q.ablProbability on the same chosen finite real-amplitude two-level source.

Its actual selected forward ket is (1,1), backward bra is (5^k,3^k), and the two coordinate idempotent projectors have transition amplitudes 5^k and 3^k. Their norm-square weights are 25^k and 9^k. The selected ABL denominator is *proved strictly positive* for all k. The exact original ABL probability return values have numerators 25^k and 9^k, the **same common denominator**, and finiteOriginalABLNormalization proves that their numerator sum equals the denominator.

Both outcomes are actual inhabitants of one explicitly selected original bidirectional admissibility record instance, via selectedJointTSVFSource. The selected source projectors equal the original Q measurement projectors.

**Same-source commuting proof:** selectedABLMatchesActualTensorOverlap connects the independently constructed original Q.ablProbability Born masses to the genuine tensor-environment squared-overlap identity by exact Nat cross multiplication, with no assumed same-weight Bool or fabricated equality. This is substantially stronger than finite majority-code robustness. It is still a finite real/nonnegative quantum submodel, NOT the physical complex Hilbert model of the actual 2017 apparatus.

The original Q.QuantumSurface needs a total divideWeight operation; this finite realization represents fractions as raw numerator/denominator pairs. Only the *selected* positive-denominator ABLContext is claimed a valid conditional probability. The unnormalized initial/final vectors differ from normalized representatives only by common positive factors that cancel in ratios. Projectors are actual coordinate idempotents; no arbitrary selected-result flag is supplied.

## C. Original rational-complex gamma amplitude and Born-product theorem

The highest-alpha *phase-sensitive* improvement is now SOURCE-WRITTEN as DASHI/Quantum/TSVFComplexGammaProductBornExact.agda. It reuses **the existing original** DASHI/Mathematics/Algebra/CayleyDicksonRationalComplexQuaternionExact.agda RationalComplex, complex multiplication, conjugation, norm-square and the existing complexNormMultiplicative theorem. That original owner now carries a --safe header after a local no-postulate audit; no Agda kernel has run.

For an arbitrary finite list of **complex** disturbance amplitudes gamma_j, the exact theorem complexGammaBornWeightIsNormOfProduct proves
[
left|prod_{j=1}^{n}gamma_jight|^2
=prod_{j=1}^{n}|gamma_j|^2.
]
The equalities are literal rational-complex norm-square polynomial identities, not a postulated bridge between amplitude and Born weight. The separate theorems complexConjugateBornNormInvariant, gammaBornProductConjugationInvariant and complexGammaProductConjugationBornInvariant prove that conjugating *all* gamma factors leaves the combined Born weight unchanged. imaginaryUnitGammaDoesNotChangeBornWeight proves inserting the exact i-phase factor does not change the probability weight. These are **finite algebraic** conjugation/phase invariants, not a physical antiunitary time reversal or dynamical environment theorem.

This resolves the earlier ambiguous notation **at the algebraic carrier level**: the 2017 paper's gamma_j are complex overlaps, whereas the earlier comparison model's Gamma_R/Gamma_W were nonnegative already-squared effective weights. Their connection is now the exact norm-of-product theorem once a physical source supplies gamma_j. The remaining hard source is to prove those literal gamma_j equal the physical postselected environment overlaps, to connect their norm-product with the chosen source's right/wrong projection probabilities and to pay the corresponding uniform N−n overlap bound. The published paper Eq.(25) is not simply re-labelled as our own result.

## The exact 2017 physics still missing

Original source: Aharonov, Cohen, Landsberger (2017), Entropy 19(3), 111, Eq.(25), https://doi.org/10.3390/e19030111. The published gamma_j are complex overlaps/amplitudes in a specific disturbed-environment evolution, not necessarily the **effective nonnegative Born weights** Gamma_R/Gamma_W of our comparison. Do not conflate the two; retain complex conjugation, squared amplitude and joint normalization where appropriate.

The full physical max-cut is (i) a chosen common complex Hilbert/environment/measurement source, including actual N pointer copies and n disturbed factors; (ii) actual initial/final boundary physical states and nonzero ABL denominator; (iii) physical pointer projector completeness, true unitary evolution and nonorthogonal/environmental-state source; (iv) gamma_j factor and environment overlap in the source's exact Eq.(25) conventions; (v) a uniform quantitative robustness bound valid under specified disturbance assumptions, with zero-wrong case; and (vi) **same physical observer/metric clock** and OS reflection/Hamiltonian identification under P07, without claiming backward signalling, global entropy reversal, a second time axis, a multiverse ontology or a Clay mass-gap theorem.

Existing owner maps to revisit before adding new: DASHI/Physics/Foundations/BidirectionalAdmissibleActionRealizationExact.agda, DASHI/Foundations/BidirectionalAdmissibilityGalois.agda, DASHI/Physics/Closure/QuantumDecoherenceAdmissibilityConcentration.agda, DASHI/Crypto/ShorFiniteVectorBornWeightsExact.agda, DASHI/Crypto/ShorFiniteVectorBornNormalizationExact.agda, and DASHI/Cognition/PNF/RationalProbabilityFutureKernelExact.agda. These have separate proper theorem owners and are NOT copied/re-attributed into the new modules.

## Tests, assumptions and attribution

Local equivalent Python exact-rational checks passed k=0..50 for overlap and normalized probabilities, 960 unequal disturbed-weight combinations including zero wrong weight, and a high-k tiny right-weight negative control. The pushed script scripts/check_tsvf_admissible_tensor_overlap_born.py was **not itself run** in the repository. Golden source imports were re-exported from DASHI/Unified/BalabanRGTOERegression.agda. The original TwoBoundarySystem, BidirectionallyAdmissibleHistoryFibreExact and Quantum.TSVF original files now declare --safe after local no-postulate inspection, but **no actual Agda kernel/transitive trust check was executed**, so all new theorems are SOURCE-WRITTEN and CONDITIONAL/FINITELY INSTANTIATED.

Original physics: Aharonov–Bergmann–Lebowitz (1964); Aharonov–Vaidman TSVF; Aharonov–Cohen–Gruss–Landsberger (2014) https://arxiv.org/abs/1406.6382; Aharonov–Cohen–Landsberger (2017) https://doi.org/10.3390/e19030111. Original DASHI owners remain unchanged as proof owners. This work contributes an explicit source-admissible finite quantum-Born overlap construction and a falsifiable next physical seam, not a published time-reversal discovery.
