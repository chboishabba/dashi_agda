# Clay Yang-Mills Proof Roadmap

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
Jaffe-Witten Yang-Mills existence and mass-gap problem would have to prove.
It is not a proof, and it does not promote any Clay, Wightman, Standard Model,
or terminal claim.

Audit boundary: finite carrier spectral gaps, finite transfer-matrix gaps,
carrier string-tension diagnostics, and finite strong-coupling estimates are
evidence only.  They are not the Clay Yang-Mills theorem.  A Clay-level result
still requires a continuum Yang-Mills construction, Osterwalder-Schrader
axioms for the continuum gauge theory, reflection positivity at the right
continuum/infinite-volume object, an infinite-volume limit, and operator or
Hamiltonian convergence identifying a positive physical mass gap.  None of
those Clay-level obligations is proved in the current repository.

Feshbach-Schur / fiber-gap boundary: the finite carrier fiber gap is only an
ingredient.  It may be used as local spectral evidence, but it does not by
itself establish a gap for the full tensor-product Hamiltonian.  The full
tensor-product route now has an explicit receipt,
`YMFeshbachSchurFiberGapBridgeReceipt`, which keeps promotion false until all
of the following are supplied: Gate 3 density of the selected carrier core in
the target Hilbert space, a Feshbach projection decomposition, invertibility
and lower control of the Schur complement on the complement, off-diagonal
relative bounds, and domain/core compatibility for the tensor Hamiltonian.
The existing `FiniteCarrierSpectralGapZ7Receipt` product-spectrum calculation
is therefore read as finite Cartesian-product evidence only, not as a physical
tensor-product Yang-Mills gap.

Balaban/RG induction gap: the current competitive YM contribution target is
not "Clay YM" as a solved claim.  It is the concrete KP/uniform-volume
obligation needed for a Balaban-style induction step:

`H_k -> H_{k+1}` with Kotecky-Preiss polymer local-sum constants, small-field
bounds, large-field tail bounds, counterterm control, and block-averaging
error terms all uniform in lattice volume and stable under cutoff/depth
removal.

The repository now records this obligation explicitly in the Balaban,
polymer/KP, and carrier area-law receipts.  It is not proved or imported.
Finite MDL/Fejer descent, finite strong-coupling bounds, and finite polymer
bookkeeping are only support surfaces.  The large/small field split is also
open: the ultrametric small-field sector is the carrier ball controlled by
existing finite estimates, while the large-field sector still needs a
tail-suppression estimate strong enough to feed the volume-independent RG
induction.

The current tower names the blockers through receipts such as
`ClayMillenniumClosureTargetReceipt`, `CarrierFactorVecInjectivityOSPositivity`,
`RGOperatorNormReceipt`, `RGBanachFixedPointReceipt`,
`OSPositivityFromRGFixedPoint`, `ScalarOSTransferMatrixReceipt`, and
`ClayBlockerUpdateReceipt`. `GribovFreeCarrierReceipt` is also available as a
carrier-only canonical-representative receipt: it consumes the concrete
`FactorVec` identity quotient, records uniqueness of the selected
representative in that identity fiber, and points at the existing
`factorVecQCoordinate` / p2-Lorentz coordinate-law primitives. It is not a
continuum Gribov theorem and it does not assert a smooth global gauge-fixing
slice. Newer finite-lattice receipts add a Wilson carrier lattice,
strong-coupling expansion, carrier string-tension estimate, finite
transfer-matrix gap, and an L2 status receipt. Those receipts give a blocker
map. The roadmap below decomposes the blocker into lemmas.

## Corrected Competitive Path

The current competitive route is not "finite carrier pressure is below the
canonical dimension, therefore Yang-Mills has a mass gap."  In particular,
the local fact recorded by the pressure-below-15 surfaces,
`pressureBound = 14`, `canonicalDim = 15`, and `14 < 15`, is only a bounded
carrier diagnostic.  It is not a continuum spectral theorem and it cannot be
consumed as a Clay mass-gap proof.

Any credible DASHI-facing Clay YM path has to solve three hard problems as
mathematical theorems, in this dependency shape:

```text
H1 Balaban volume-independent induction
  -> H2 BRST reflection positivity
  -> H3 operator-valued spectral gap
  -> Clay YM existence and mass gap
```

`H1` means a genuine volume-independent constructive RG/cluster induction,
not a fixed finite-depth contraction receipt.  It must supply bounds uniform
enough for infinite volume and cutoff removal.

`H2` means reflection positivity for the gauge-fixed/BRST-compatible
continuum object, with the unphysical degrees of freedom controlled so that
OS/Wightman reconstruction is applicable to the physical sector.  Finite
Wilson reflection positivity or scalar-sector transfer positivity does not
discharge this step.

`H3` means a positive lower bound for the physical, operator-valued continuum
Hamiltonian or transfer generator, stable under the limiting process and
identified with the reconstructed gauge-invariant spectrum.  A scalar
inequality, finite carrier eigenvalue, transfer-matrix gap at fixed lattice
scope, or `14 < 15` pressure diagnostic is not this theorem.

The old `L1-L9` lemma map below remains useful as a decomposition of
existence and mass-gap obligations.  The governance rule is that no L7-L9
promotion may be recorded unless the H1/H2/H3 chain is explicitly discharged
or replaced by an equally strong theorem with the same continuum, positivity,
and operator-spectrum content.

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
| L2 | Prove uniform cutoff-independent bounds on Schwinger/correlation functions, including reflection positivity and exponential decay where needed. | Partially inhabited only in the finite carrier strong-coupling regime. A corrected two-plaquette strong-coupling bound, carrier string tension `sigma ~= 5.27`, exponential plaquette decay at `beta = alpha1`, and a finite lattice gap are recorded as finite evidence only. | `StrongCouplingExpansionReceipt`, `UniformBoundStrongCouplingReceipt`, `StringTensionCarrierReceipt`, `LatticeMassGapFromTransferMatrixReceipt`, `YML2StatusReceipt`, `PolymerKPAsMDLReceipt`, `CarrierAreaLawBalabanSeedReceipt` | Need the KP/uniform-volume polymer obligation: volume-independent local-sum constants, small-field bounds, large-field tail bounds, counterterm control, continuum beta running, tightness as depth/cutoff is removed, dimensionful scale anchoring, infinite-volume control, and gap survival. |
| L3 | Prove tightness/compactness of the cutoff measure family as the cutoff is removed. | Uninhabited. RG contraction and Banach fixed-point receipts are finite/conditional and do not give continuum measure tightness. | `RGBanachFixedPointReceipt`, `OSPositivityFromRGFixedPoint`, `ClayBlockerUpdateReceipt` | Need compactness in the continuum constructive-QFT topology. |
| L4 | Extract a weak continuum limit and prove the limit is nontrivial. | Uninhabited. Continuum RG convergence is named open. | `ContinuumClayMassGapReceiptObligation`, `ClayBlockerUpdateReceipt` | Need interacting continuum YM, not just finite carrier limits or scalar transfer positivity. |
| L5 | Prove the continuum limit satisfies OS axioms: OS positivity, Euclidean covariance, symmetry, clustering, and regularity. | Partially inhabited only for finite scalar and finite ungauge-fixed Wilson-loop carrier inputs. The OS3 boundary is now explicit: ungauge-fixed Wilson positivity is finite-lattice evidence; BRST/Faddeev-Popov gauge fixing is not a positive-Hilbert OS3 proof because of the indefinite/Krein sector; ghost time reflection requires a graded sign/involution; carrier Gribov-free wording is only a representative choice, not a continuum Gribov-copy theorem. Full gauge OS, continuum reflection positivity, covariance, and infinite-volume OS control remain open. | `ScalarOSTransferMatrixReceipt`, `OSAxiomsContinuumStatus`, `WightmanReconstructionCandidateReceipt`, `YML5OSAxiomsForGaugeSectorReceipt`, `GribovFreeCarrierReceipt` | Need gauge-sector reflection positivity at the continuum/infinite-volume object, a gauge-invariant or quotient-compatible OS3 construction, ghost/BRST handling that lands in a positive physical Hilbert space, a real continuum Gribov-copy boundary, and restoration of full Euclidean covariance. |
| Gribov carrier guardrail | For any gauge-fixed route, distinguish carrier representative choice from a continuum Gribov-copy theorem. | Inhabited only for the local `FactorVec` identity quotient: the canonical representative is unique in the identity fiber and the coordinate projection primitive is recorded. | `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need an accepted continuum theorem for smooth YM connections before making any global gauge-fixing or Gribov-free continuum claim. |
| L6 | Apply OS reconstruction to obtain a Hilbert space, fields, and Hamiltonian satisfying Wightman axioms. | Uninhabited. Reconstruction is a target/citation boundary only. | `ClayMillenniumClosureTargetReceipt`, `WightmanReconstructionCandidateReceipt` | Need L5 first, plus authority binding for all reconstruction hypotheses. |
| L7 | Prove the transfer matrix has a positive spectral gap uniformly in cutoff. | Uninhabited. Finite candidate gaps and selected finite PSD diagnostics do not give a uniform gauge gap. | `H0OSPositivityBaseCase`, `H0ExplicitMatrixReceipt`, `NormalisedH0OSPositivity`, `BalabanRGMassGapReceiptSurface` | Need a depth/cutoff-independent lower bound for the physical gauge Hamiltonian. |
| L8 | Prove the spectral gap survives the continuum limit. | Uninhabited. Requires L3/L4 and L7. Finite carrier gaps are evidence only. | `ColimitGapLiftOnHamiltonian`, `ContinuumClayMassGapReceiptObligation` | Need semicontinuity or a stronger operator/Hamiltonian convergence theorem for the infinite-volume continuum Hamiltonians. |
| L9 | Identify the limiting spectral gap with the physical Yang-Mills mass gap. | Uninhabited. The physical Hamiltonian/gauge group identification remains open. | `YangMillsMassGapBoundary`, `ClayMillenniumClosureTargetReceipt`, `Paper8UnificationBlockerMap` | Need a reconstructed physical Hilbert space and gauge-invariant one-particle/mass spectrum. |

## Feshbach-Schur Fiber-Gap Route

The admissible finite-to-full-gap route is now:

1. Record a carrier fiber spectral gap as evidence.  This is currently
   available for selected finite carriers, including the Z/7 cycle receipt and
   its finite product-spectrum caveat.
2. Prove Gate 3 density for the selected carrier core inside the target
   Hilbert space.  The current `Gate3NormDictionary` reaches a finite
   limit-71 inequality surface, but density remains false.
3. Supply the Feshbach-Schur operator hypotheses: projection decomposition,
   Schur complement invertibility, off-diagonal relative bounds, and domain
   compatibility for the full tensor Hamiltonian.
4. Only after those hypotheses can a tensor-product spectral lower bound be
   stated.  The current repository has no such bound and no Clay promotion.

This route is deliberately narrower than a Clay claim.  It is a local bridge
obligation for turning finite fiber evidence into a candidate operator theorem;
it still sits below L7/L8/L9 and below the continuum construction and
authority requirements.

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
continuum OS axioms, continuum reflection positivity, a BRST gauge-fixed
positive-Hilbert OS3 construction, a ghost time-reflection graded-sign theorem,
a continuum Gribov-copy resolution, an infinite-volume limit, Wightman
reconstruction, operator/Hamiltonian convergence, a weak-coupling/continuum
uniform correlator theorem, or a uniform continuum spectral gap.

The next admissible YM tranche should not aim vaguely at "Clay YM." It should
target the H1/L2-to-L3 interface: prove or refute a Balaban-style
volume-independent induction with constants independent of carrier depth and
volume, then isolate the BRST reflection-positivity and operator-valued
spectral-gap hypotheses required before any continuum limit can be consumed
as Clay evidence.

More concretely, the target is the KP/uniform-volume induction obligation:
prove the Kotecky-Preiss polymer bound with constants independent of the
spatial volume, prove an ultrametric large/small field split with the
large-field tail suppressed uniformly enough for `H_k -> H_{k+1}`, and show
that the resulting counterterm and block-averaging errors remain controlled
through cutoff/depth removal.  This would be a competitive Yang-Mills
contribution if proved; it is currently only an open obligation.

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
- continuum reflection positivity and infinite-volume OS limit
- continuum Gribov-free/global gauge-fixing promotion from the carrier
  representative receipt
- continuum interacting Yang-Mills construction
- operator/Hamiltonian convergence from finite carriers to the continuum
- Balaban volume-independent induction for the continuum constructive route
- KP/uniform-volume Balaban induction
- ultrametric large/small field split with large-field tail suppression
- BRST-compatible reflection positivity for the physical gauge sector
- an operator-valued physical spectral-gap theorem
- any inference of the form "`14 < 15`; therefore Yang-Mills mass gap"
- treating finite/strong-coupling carrier YM as continuum Clay YM
- terminal/unification promotion
