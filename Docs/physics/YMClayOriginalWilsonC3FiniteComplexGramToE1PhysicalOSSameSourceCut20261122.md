# YM P0 — original Wilson C3 full finite complex-coefficient Gram to same E1/OS

**22 November 2026. Status: source-written Agda consumer / kernel NOT run.** This is a finite original-Wilson algebraic weld, not a physical continuum mass-gap theorem.

## Source identity and proven conditional implication

The new source [YMClayOriginalC3FullFiniteComplexCoefficientGramBidiExact.agda](../../DASHI/Physics/YangMills/YMClayOriginalC3FullFiniteComplexCoefficientGramBidiExact.agda) imports and uses **unchanged**:
1. `YMClayOriginalWilsonC3WeightedHaarTransferExact.actualOriginalFineNormalized`, the same n=3 1,024-bond original SUN Wilson/Gibbs normalized expectation (not an independent probability measure);
2. `YMClayOriginalC3WeightedOSGramBidiExact.originalReflectedGramEntry`, with the actual native C3 permutation, same selected full-density C3-invariance and exact original time-reflection commutation as visible premises;
3. `BalabanClayT5PhysicalMeasureGramContinuityExact.PhysicalOSOperations`, `physicalReflectedGramEntry`, `sumList` and `physicalReflectedGramQuadraticForm`, the previously present *full double sum*, including off-diagonal cross terms and complex coefficient conjugation.

For any finite family of **real-valued original Wilson insertions** `F_i` with coefficients `c_i` in a selected scalar carrier, the existing full Gram computes

```
Q(F,c) = SUM_i SUM_j conjugate(c_i) * c_j *
         embedReal(E_original[F_i(theta U) F_j(U)]) .
```

The `originalFiniteFullGramC3` source theorem proves that **if** the original selected label canonicalization, full weighted Gibbs action-invariance and reflection/C3 compatibility are inhabited, rotating every original insertion by its existing native spatial C3 leaves the entire finite quadratic form invariant. This is proved **term-by-term, including i != j**, by original source-gram invariance and the pre-existing Gram list double sum; no duplicated Wilson action, new covariance record or Hamiltonian is introduced. Coefficient operations are parameters and must be instantiated by the actual complex scalar algebra.

This advances the previous full-*row* observational equivalence from individual real Gram entries to complete finite complex-**coefficient** families. It does not prove genuine complex-*valued* positive-time Wilson cylinder closure: star-conjugation of an observable itself and the analytic complex Hilbert inner-product properties are still source obligations. The existing `PositiveTimeSupported` and `GaugeInvariantObservable` fields on physical test metadata have type `Set`, **not an automatically populated proof of source support or gauge invariance**. `rotateTest` transfers those labels structurally, not their meaning.

## Exact diagnostic and failure mode

The new [SymPy regression](../../scripts/check_ym_original_c3_full_complex_coefficient_gram_20261122.py) uses the **previous** finite original-Q8 diagnostic covariance eigenvalues
`64519815/238733401` and `2910/15451` (twice). It tests C3 invariance for arbitrary selected complex coefficients, all 9 Hermitian cross entries, three complete/orthogonal character projections, nonzero mixed entries, the need for coefficient conjugation, a separately adjoined null Gram row, and the artificial `diag(0,2,1/n,1/n)` H-family no-go.

An independent local SymPy 1.14 reproduction of the committed test's algebra passed **55/55** exact checks. The **exact checked-out GitHub script was not executed** in the local environment, and the Q8 reference is not full SU(2) Haar. Therefore do not claim a bytewise executable Git-head or Agda acceptance receipt, physical RP, a common physical rate, or D2.

## Next original E1/OS producer attachment — BIDI order

1. **Finite physical admissibility:** use `YMClaySide4SpatialC3WilsonNaturalityExact` (time axis fixed), `YMClayNativeSideFourC3VectorWeldExact`, original selected R445 time reflection, and `YMClayOriginalR445PublishedWilsonRPWordWeldExact` to prove actual positive-time *Wilson-word* and gauge-invariant test-domain preservation under spatial C3. Prove the original reflection action matches the published positive-time star map. Do not use metadata as evidence.
2. **Original full complex OS form:** instantiate real basis/complex coefficients by source-owned actual conjugation, scalar embedding, and real-/imaginary-Wilson closure, with full RP **at every original cutoff**, not merely n=3. Bind density C3 invariance to the actual CMP119 E/R/B/V selected Gibbs action and finish the native canonical C3 label goal.
3. **Same E1 continuum:** consume `YMClayE1OriginalSUNFiniteCylinderLawsExact` and the *existing* `BalabanClayT5PhysicalMeasureGramContinuityExact` and `BalabanClayT5OSGramTopologyExact` convergence of every complete finite reflected Gram. Obtain **one** indexed original-family C3 action at all cutoffs, prove convergence/C3 commute by the selected scalar-topology uniqueness, and preserve the same positive-time OS quotient. No separate continuum C3 measure may be created.
4. **Same H:** consume the existing `YangMillsClayPinnedCMP119OSReconstructionExact` pre-gap Hilbert/vacuum/Hamiltonian and original OS1 R332 Euclidean-time translations. Show the induced C3 unitary is well-defined after null quotient, fixes vacuum and commutes with **the same** `T(t)=exp(-t H_OS)`. Complex Fourier projectors can then split all three sectors; density of their images follows from density of one C3-stable original nonvacuum test domain, not by three unrelated postulates.
5. **Physical uniform rate:** produce the remaining **same-original-source** good-conditioned/CMP116 response and globally marked renormalized W1/W3 rooted-shell charges with an absolute common rate; direct unrenormalized Wilson marked-Mayer activities fail the source KP bound. Apply existing full-spectrum D2 to all three sectors; selected-sector decay alone cannot close the gap. E1 noncollapse, N1 and all compact-simple G1 still require their original proofs.

**Negative controls:** scalar 0 != phase exponent 0 (unity); a vanishing character sum != a zero state; finite Gram radical != a gauge zero != physical OS null != spectral vacuum; arithmetic BSD E32 Gaussian and E36 Eisenstein isogenies are not Wilson H eigenvector maps. H05 requires its own signed-trit 27-state and indexed six-face geometry, not merely the binary 8-corner Wilson address.

**Attribution/trust:** Wilson/Haar/Osterwalder-Schrader/Menotti-Pelissetto/Balaban original analytic sources retain ownership; the new source is a DASHI composition. Agda/Nix not present locally; no GitHub CI was used. E1, D1, D2, N1, G1 remain OPEN.
