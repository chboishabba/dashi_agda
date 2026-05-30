# Clay Yang-Mills Proof Roadmap

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
Jaffe-Witten Yang-Mills existence and mass-gap problem would have to prove.
It is not a proof, and it does not promote any Clay, Wightman, Standard Model,
or terminal claim.

The current tower names the blockers through receipts such as
`ClayMillenniumClosureTargetReceipt`, `CarrierFactorVecInjectivityOSPositivity`,
`RGOperatorNormReceipt`, `RGBanachFixedPointReceipt`,
`OSPositivityFromRGFixedPoint`, `ScalarOSTransferMatrixReceipt`, and
`ClayBlockerUpdateReceipt`. Newer finite-lattice receipts add a Wilson
carrier lattice, strong-coupling expansion, carrier string-tension estimate,
finite transfer-matrix gap, and an L2 status receipt. Those receipts give a
blocker map. The roadmap below decomposes the blocker into lemmas.

## Dependency Graph

```text
L1 lattice YM measure
  -> L2 uniform correlator bounds
  -> L3 tightness of cutoff measures
  -> L4 continuum weak limit
  -> L5 OS axioms for the gauge theory
  -> L6 OS/Wightman reconstruction

L1, L2, L5
  -> L7 uniform transfer-matrix spectral gap
  -> L8 gap survives the continuum limit
  -> L9 physical mass gap in the reconstructed QFT
```

The existence block is `L1-L6`. The mass-gap block is `L7-L9`. A Clay-level
result requires both blocks.

## Lemma Status

| Lemma | Required mathematical content | Current carrier status | Existing receipt surface | Gap |
|---|---|---|---|---|
| L1 | Construct a lattice Yang-Mills measure at each cutoff/lattice spacing for compact gauge group `G`. | Partial target only. The carrier has finite FactorVec/RG scaffolding and finite gauge candidates, but no selected continuum YM gauge measure. | `CarrierRenormalizationGroupScaleReceipt`, `RGContractionReceipt`, `FactorVecAverageVsSumReceipt`, `RGOperatorNormFormalProof` | Need a genuine lattice YM action/measure tied to a carrier-derived compact gauge group. |
| L2 | Prove uniform cutoff-independent bounds on Schwinger/correlation functions, including reflection positivity and exponential decay where needed. | Partially inhabited only in the finite carrier strong-coupling regime. A corrected two-plaquette strong-coupling bound, carrier string tension `sigma ~= 5.27`, exponential plaquette decay at `beta = alpha1`, and a finite lattice gap are recorded. | `StrongCouplingExpansionReceipt`, `UniformBoundStrongCouplingReceipt`, `StringTensionCarrierReceipt`, `LatticeMassGapFromTransferMatrixReceipt`, `YML2StatusReceipt` | Need continuum beta running, weak-coupling/continuum uniform bounds, tightness as depth/cutoff is removed, dimensionful scale anchoring, and gap survival. |
| L3 | Prove tightness/compactness of the cutoff measure family as the cutoff is removed. | Uninhabited. RG contraction and Banach fixed-point receipts are finite/conditional and do not give continuum measure tightness. | `RGBanachFixedPointReceipt`, `OSPositivityFromRGFixedPoint`, `ClayBlockerUpdateReceipt` | Need compactness in the continuum constructive-QFT topology. |
| L4 | Extract a weak continuum limit and prove the limit is nontrivial. | Uninhabited. Continuum RG convergence is named open. | `ContinuumClayMassGapReceiptObligation`, `ClayBlockerUpdateReceipt` | Need interacting continuum YM, not just finite carrier limits or scalar transfer positivity. |
| L5 | Prove the continuum limit satisfies OS axioms: OS positivity, Euclidean covariance, symmetry, clustering, and regularity. | Partially inhabited only for the finite scalar sector. Full gauge OS and covariance remain open. | `ScalarOSTransferMatrixReceipt`, `OSAxiomsContinuumStatus`, `WightmanReconstructionCandidateReceipt` | Need gauge-sector reflection positivity and restoration of full Euclidean covariance. |
| L6 | Apply OS reconstruction to obtain a Hilbert space, fields, and Hamiltonian satisfying Wightman axioms. | Uninhabited. Reconstruction is a target/citation boundary only. | `ClayMillenniumClosureTargetReceipt`, `WightmanReconstructionCandidateReceipt` | Need L5 first, plus authority binding for all reconstruction hypotheses. |
| L7 | Prove the transfer matrix has a positive spectral gap uniformly in cutoff. | Uninhabited. Finite candidate gaps and selected finite PSD diagnostics do not give a uniform gauge gap. | `H0OSPositivityBaseCase`, `H0ExplicitMatrixReceipt`, `NormalisedH0OSPositivity`, `BalabanRGMassGapReceiptSurface` | Need a depth/cutoff-independent lower bound for the physical gauge Hamiltonian. |
| L8 | Prove the spectral gap survives the continuum limit. | Uninhabited. Requires L3/L4 and L7. | `ColimitGapLiftOnHamiltonian`, `ContinuumClayMassGapReceiptObligation` | Need semicontinuity or a stronger spectral-convergence theorem for the Hamiltonians. |
| L9 | Identify the limiting spectral gap with the physical Yang-Mills mass gap. | Uninhabited. The physical Hamiltonian/gauge group identification remains open. | `YangMillsMassGapBoundary`, `ClayMillenniumClosureTargetReceipt`, `Paper8UnificationBlockerMap` | Need a reconstructed physical Hilbert space and gauge-invariant one-particle/mass spectrum. |

## Current Honest Position

Update after the second roadmap-execution tranche: YM L1 is inhabited only at
finite carrier-lattice scope, and YM L2 is now partially inhabited only in a
finite strong-coupling scope. The tower has receipts for a three-site carrier
spatial lattice, depth as Euclidean time, a Wilson action with spatial and
spatial-temporal plaquettes, finite-lattice Wilson reflection positivity, a
strong-coupling plaquette expansion, a corrected connected two-plaquette
bound in the strong phase, a carrier string-tension estimate `sigma ~= 5.27`,
and a finite transfer-matrix gap.

This is not continuum Yang-Mills. The strong-coupling result is at carrier
`beta = alpha1` and records exponential decay in carrier units; it does not
construct the beta-to-infinity Wilson continuum trajectory, a dimensionful
physical mass scale, a Wightman theory, or Clay mass-gap promotion.

The carrier still does not have continuum beta running, continuum tightness,
continuum OS axioms, Wightman reconstruction, a weak-coupling/continuum
uniform correlator theorem, or a uniform continuum spectral gap.

The next admissible YM tranche should not aim vaguely at "Clay YM." It should
target the L2-to-L3 interface: make explicit which strong-coupling constants
are uniform in carrier depth, then isolate the missing running-coupling and
tightness hypotheses required before any continuum limit can be discussed.

Phase 2 update: `StrongCouplingExpansionReceipt`,
`StringTensionCarrierReceipt`, `UniformBoundStrongCouplingReceipt`,
`BetaCriticalReceipt`, `CarrierRGTrajectoryYMReceipt`, and
`YML2StatusReceipt` record a partial L2 result only in the finite
strong-coupling regime `beta=alpha1`.  This gives a carrier-unit
string-tension/area-law diagnostic and exponential plaquette-correlator decay,
but it is not the Wilson continuum trajectory because fixed `alpha1` is not
`beta -> infinity`.  `Phase2ProgrammeReceipt` therefore treats the next YM
work as continuum beta-running, tightness, scale anchoring, and gap-survival
work, not as Clay closure.

Corrected coupling update: `CarrierScaleFromHeegnerReceipt`,
`QCDRunningFromCarrierScaleReceipt`,
`CarrierGaugeCouplingFromCSLevelReceipt`,
`WilsonBetaFromCSLevelReceipt`, `YML2CorrectedStatusReceipt`, and
`YML3TightnessFromKRunningReceipt` separate `alpha1` from the Wilson beta
and record a CS-level candidate: `alpha_s=1/3`, `beta_SU2=3/pi`, finite
string tension `2.125`, and a `2.33 GeV` mass-gap diagnostic.  The candidate
L3 family is `{mu_k}` as `k -> infinity`; tightness, continuum weak limit,
Wightman reconstruction, and Clay Yang-Mills remain open.

The same Phase 2 programme also records the CS-level gauge-coupling frontier:
`SMGaugeGroupFromCS3LanesReceipt`, `LevelRankDecouplingReceipt`, and
`WBosonMassFromCSReceipt` give candidate gauge-factor origins and expose the
SU(2)-SU(3) level-rank decoupling and W-mass RG/scale-matching blockers.  This
is Gate 6/Gate 7 gauge-coupling context for the YM programme, not a proof of
direct-product gauge independence, physical coupling normalisation, exact
Standard Model reconstruction, or a Yang-Mills mass gap.

## Promotion Boundary

The following must remain false until all nine lemmas and the required
authority boundaries are discharged:

- Clay Yang-Mills mass-gap promotion
- Wightman reconstruction promotion
- full gauge-sector OS positivity
- continuum interacting Yang-Mills construction
- treating finite/strong-coupling carrier YM as continuum Clay YM
- terminal/unification promotion
