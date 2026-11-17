# Clay Yang-Mills Proof Roadmap

Status: lemma roadmap; non-promoting.

This document is a dependency graph for what a DASHI-based proof of the
Jaffe-Witten Yang-Mills existence and mass-gap problem would have to prove.
It is not a proof, and it does not promote any Clay, Wightman, Standard Model,
or terminal claim.

Current corpus correction: the live Clay-facing manuscript is now
`Docs/papers/live/Paper3YangMillsClayDraft.md`, and it sharpens the real
frontier. The finite self-adjointness and domination steps are internal to the
current draft. The older `H3a -> H3b -> no-spectral-pollution ->
thermodynamic/OS/Wightman -> mass-gap/uniqueness` continuum theorem chain is
now recorded internally at its owning theorem surfaces. The remaining live YM
frontier is therefore narrower: Clay-promotion authority, physical
Hamiltonian/mass-gap identification, statement-formulation equivalence, and
external acceptance/review. Read the roadmap below as a wider dependency
ledger, not as a more current statement than the live paper.

Current packaging correction: the repo now records the exact theorem-shape
authority chain `H3a -> H3b -> no-spectral-pollution -> RP/OS -> Wightman ->
continuum mass-gap transfer` in the proof-facing Agda boundaries. This is a
governance improvement, not a theorem promotion: the Yang-Mills frontier
remains authority-backed unless the full Balaban multiscale package is
internalized.

Current governance correction: YM is now the only major lane whose remaining
burden is still naturally missing-content-shaped rather than merely
promotion-evidence-shaped. The continuum theorem chain is explicit and wired;
the remaining load-bearing in-repo burden is the final Clay boundary rather
than H3a/H3b themselves, unless the repo stays authority-backed by design.

Reviewer-packet correction: the repo now also carries an explicit final
authority-packet layer for the same chain. The finite self-adjointness,
domination, and finite spectral-margin story is internal; `H3a`, RP/OS,
Wightman, and the final continuum transfer remain explicit external or
authority-backed steps. This improves submission grammar only and does not
change theorem ownership.

## Sprint 79 Current Fork

The live in-repo YM fork now has two ordered lanes. The UV-continuum lane comes
from Eriksson 2602.0077:

```text
Eriksson26020077Theorem16Conditional
-> BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
-> SquaredOscillationSummabilityForHalfPlaneBlocking
-> FixedFiniteVolumeBlockedObservableContinuumLimit
```

The open DASHI target in this lane is `AnisotropicAssumptionA`: the
squared-oscillation summability bound for the half-plane/spatial Balaban
blocking map `Q_hp`. The favorable spatial link count `3*L^(3k)` is only an
arithmetic balance until that bound is proved. This lane does not prove OS
reflection positivity, the thermodynamic limit, or a mass gap.

Sprint 80 narrows the immediate proof target to:

```text
BalabanCMP98LocalOscillationBoundForQhp
-> LipschitzToSquaredOscillationForQhp
-> AnisotropicAssumptionA
```

The conditional product is
`3*L^(3k)*C_local^2*L^(-4k)=3*C_local^2*L^(-k)<=3*C_local^2`. At `L=2,k=9`,
the anisotropic factor is `0.005859375` relative to `C_local^2`, and
`0.00146484375` relative to the isotropic `4*C^2` baseline.

Sprint 81 attempts the first item above from in-repo material and keeps it
fail-closed. Before `BalabanCMP98LocalOscillationBoundForQhp` can become a
proof object, the repo must define or import:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
```

Sprint 81A adds a conditional authority branch. Relative to an explicit
Balaban CMP 98 local-oscillation authority input, the in-repo arithmetic closes
`LipschitzToSquaredOscillationForQhp` and `AnisotropicAssumptionA`. The CMP 98
locality theorem itself remains an external authority input, so this does not
promote Clay/YM or a mass gap.

Sprint 81B records the support-interface blocker for the KP lane, and Sprint
81C defines the typed carriers for
`BalabanEffectiveAction`, `Polymer`, `PolymerIn`, `LinkKind`, `TemporalLink`,
`SpatialLink`, `PolymerSupport`, `SpatialSupport`,
`ResidualEffectiveActionTerm`, `ActivityDependsOnlyOnLinksInsidePolymer`,
`TemporalMeasureFactorizationLambdaOneReconciled`, and
`DefinedOnBlockedL2SpatialGraph`. The next theorem is
`EffectiveActionPolymersSpatialOnlyForA1`; only after that can the blocked
`eta=4` count be earned.

The separate KP/mass-gap lane has moved to the strong Gate-B carrier path.
The legacy weak `PolymerIn` bridge is refuted for the current carrier and is
kept only as a diagnostic guardrail.  The proof-critical lane is now:

```text
StrongActionTermTransferResidualDisjointness
-> StrongResidualPolymerMembership
-> StrongGateBToKPTheorem
-> KPEntropyAtBlockedScaleL2
-> AnisotropicL2WeightedKPCloses
-> AllDiameterWeightedKP
-> SmallFieldBoundsSurviveAnisotropicBlocking
-> BalabanPartitionIdentityCompatibleWithTemporalTransferMatrix
-> LatticeMassGapFromAnisotropicKP
-> ContinuumMassGapTransfer
-> OSWightmanReconstruction
-> ClayYangMills
```

The current route decisions are:

```text
UV: ANISOTROPIC_ASSUMPTION_A_PROVED_IN_REPO; NEXT_BLOCKER_FIXED_FINITE_VOLUME_BLOCKED_OBSERVABLE_CONTINUUM_LIMIT_CONDITIONAL
KP: STRONG_GATE_B_TO_KP_CLOSED; NEXT_BLOCKER_SMALL_FIELD_SURVIVAL
```

```text
q  = 0.23178189475262734
4q = 0.9271275790105094   closes on the strong blocked L=2 eta=4 lane
6q = 1.390691368515764    blocks fine-lattice spatial eta=6
8q = 1.8542551580210187   blocks generic 4D eta=8
```

`YMSmallFieldSurvivalAuthority` now splits the next gate into three in-repo
structural inputs, six imported analytic theorem slots, and one native
spatial-orbit slot.  Spatial-only blocking
compatibility, temporal-transfer compatibility, and polymer-activity
preservation are derived from the strong sector/KP stack.  The remaining
small-field blockers are `BalabanSmallFieldRegionStability`,
`BalabanFluctuationCovarianceBound`,
`BalabanPolymerActivityExponentialDecay`, `BalabanScaleUniformConstants`,
`GaugeFixingJacobianBound`, and `GaugeOrbitVolumeUniform`; the
`SpatialBlockingPreservesGaugeOrbit` slot is native/derived. Clay/YM promotion
remains false.

The downstream authority lane is decomposed rather than opaque:
`YMLatticeMassGapAuthority` now exposes four transfer/spectral-gap theorem
slots, `YMThermodynamicLimitAuthority` exposes five volume/continuum theorem
slots, `YMOSAxiomsAuthority` exposes five OS axiom theorem slots, and
`YMContinuumMassGapTransferAuthority` exposes four continuum spectral-transfer
slots.  These slots are the current authority lane; they are not internal
analytic proofs.

The immediate UV tranche is to prove or falsify:

```text
FormalOscillationSeminormForGaugeLinks
FormalQhpBlockingMapDefinition
BalabanCMP98AveragingLocalityImported
QhpPerLinkInfluenceConeLMinus2k
BalabanCMP98LocalOscillationBoundForQhp
LipschitzToSquaredOscillationForQhp
AnisotropicAssumptionA
SquaredOscillationSummabilityForHalfPlaneBlocking
```

The immediate KP tranche is to prove or falsify:

```text
EffectiveActionPolymersSpatialOnlyForA1
PolymerDefinedOnBlockedLattice
KPEntropyAtBlockedScaleL2
```

All later Balaban, small-field, lattice, continuum, OS/Wightman, and Clay
endpoint obligations remain open.

Weak-coupling bookkeeping correction for `2026-06-13`: the repo now has a
typed fail-closed polymer convergence package for the Paper 3 YM lane:

```text
YMLatticeAnimalCountingBoundReceipt
-> YMWeakCouplingRatioBoundReceipt
-> YMGeometricTailHalfBoundReceipt
-> YMPolymerWeakCouplingSumBoundReceipt
-> YMP7WeakCouplingPolymerConvergenceReceipt
```

This package records the `d=4` lattice-animal count surface `N_n <= (8e)^n`,
the tuned weak-coupling ratio surface `a = c_K / (4 g^2)`, the corrected
same-prime `p=7` threshold `c_K >= (4/3) log(24e)`, the geometric-tail
`<= 1/2` surface, the grouped origin-containing weighted polymer sum surface,
and the bridge back into the same-prime `p=7` Wilson activity lane. The repo
now uses that package to close the exact lane-local `p=7` local KP theorem
surface, then records lane-local strict absorption, uniform-volume KP, and
Balaban RG transfer as true in their owning receipts. It still does not prove
continuum Yang-Mills, mass gap, or Clay Yang-Mills.

Audit boundary: finite carrier spectral gaps, finite transfer-matrix gaps,
carrier string-tension diagnostics, and finite strong-coupling estimates are
evidence only.  They are not the Clay Yang-Mills theorem.  A Clay-level result
still requires a continuum Yang-Mills construction, Osterwalder-Schrader
axioms for the continuum gauge theory, reflection positivity at the right
continuum/infinite-volume object, an infinite-volume limit, and operator or
Hamiltonian convergence identifying a positive physical mass gap.  None of
those Clay-level obligations is proved in the current repository.

KP/RG/atom receipt boundary: `KPCouplingObstruction`,
`BruhatTitsBraidKPReduction`, and `AtomExtendedCarrierFrame` are governance
receipts, not Clay progress.  `KPCouplingObstruction` corrects the physical
`p=7` threshold to `beta_min ~= 10.13`, so the physical Wilson beta route fails
unless a separate RG bridge is supplied.  `BruhatTitsBraidKPReduction` may keep
the carrier RG beta branch conditionally passable under carrier hypotheses, but
that is not physical beta running, continuum tightness, OS/Wightman
reconstruction, or a mass-gap theorem.  `AtomExtendedCarrierFrame` is blocked by
an explicit `A > 0` positivity obligation before it can be consumed as analytic
input.

Spectral tower tranche boundary: the current tower distinguishes five
authority levels.  A0 is diagnostic/prose, A1 is finite diagonal
spectralizable evidence, A2 is a typed theorem target, A3 is calibrated
subclass decidability, and A4 is runtime/semantic/continuum/Clay promotion.
The PNF residual finite diagonal spectral severity receipt is A1 only: its
proof is spectralizable finite diagonal evidence, not runtime behavior or
semantic truth.  `SpectralTowerTheoremTarget` is A2, not theorem closure.  NS
FRACTRAN admissibility is A3 only for the Kolmogorov-calibrated subclass.  No
A4 continuum, Clay, runtime-semantic, or terminal claim is promoted here.
`YMContinuumGapFromCarrierConditionalReceipt` and
`YMFourStepsConditionalReceipt` record the Gate-3 reduction and four analytic
steps as conditional ledgers.  They do not construct self-adjoint continuum
YM, strict Mourre positivity, QFT ground-state uniqueness, weak spectral
measure survival, or a Clay mass gap.

Corrected math boundary: no current roadmap step may say that a gap
strengthens to `3.0`.  Where the CM/infinite-depth spectral comparison is
discussed, the honest Selberg-style lower-bound target is
`lambda1 >= 3/16`, still below Clay promotion.  Gate 3 remains the hard lift
from the carrier dictionary to `S'`, Chern-character compatibility, and the
real norm theorem.  K-theory/Bott language is a framing target only, not a
proof.  The PNF spectral-severity surface is finite diagonal evidence, and
any PNF-to-Z7 arrow remains open/lossy.  The two Clay reductions are
conditional ledgers only.

Spectral/Mosco receipt boundary: the new spectral receipt set must be read as
route organization and finite evidence, not as a continuum operator theorem.
For Gate 3, the blocking bridge is not merely "more spectral data."  It has
three named obligations: Mosco upper/density control for the selected carrier
core, a no-spectral-pollution theorem through the cutoff/depth limiting
process, and a mass-shell bridge that identifies the limiting operator
spectrum with the physical gauge-invariant mass surface.  Until all three are
proved, finite carrier spectral gaps, PNF spectral severity, and tower targets
cannot be promoted to L7/L8/L9, Wightman reconstruction, or Clay Yang-Mills.

NS two-phase diagnostic boundary: the current two-phase trace is empirical
diagnostic evidence only.  It falsifies the combined `Q_log` lane2+lane7
reading.  Scalar EV5 Lyapunov is rejected as the live criterion.  The current
candidate is vector-valued EV5, with lane7 read only as the dissipation
witness and lane2 read only as the bounded migration witness.  Those witnesses
are not an actual-flow Navier-Stokes transfer theorem, not a Serrin/BKM
estimate, not smooth regularity, and not Clay NS.  They may motivate future
projection and comparison tests, but they cannot discharge any YM Gate 3 or NS
Clay obligation.

Wave-pool/Gate3 boundary: the caisson/standing-wave picture is now recorded
only as a proof-search dictionary.  `CarrierMoscoConvergenceFromPhysicsReceipt`
keeps Mosco as a strong-resolvent/density route, not norm-resolvent
convergence.  `GreensFunctionConvergenceRateReceipt` records the finite
caisson convergence heuristic and the NS critical-index boundary, but leaves
the analytic bound open.  `CarrierPhaseStructureReceipt` records that YM can
quotient gauge phase in the physical Hilbert-space reading while NS cannot
treat high-prime phase loss as gauge.  These receipts explain why Gate 3 may
be easier for YM than NS; they do not prove Gate 3, OS/Wightman
reconstruction, or a Clay mass gap.

Codec atom / phase boundary: `CanonicalCodecAtomReceipt` records the common
codec form as coarse field plus sparse signed anisotropic atoms plus an MDL
residual budget.  This is a useful bridge because it identifies random-phase
residual synthesis as the implementation-level symptom of the same phase loss
that Gate 3 must control.  The receipt keeps the atom phase, orientation,
anisotropy, and twist fields visible, but it does not implement the runtime
codec, prove MDL matching pursuit, prove phase-aware decode stability, prove
Gate 3 density, or promote any NS/YM/Clay result.

Carrier phase/Gribov/BT-tree boundary: carrier gauge fixing is a
BT-tree/discrete-resolution statement inside the non-Archimedean carrier.  It
selects canonical representatives only at that finite/discrete carrier
authority.  Singer's continuum obstruction and the continuum Gribov-copy
problem remain open.  The `p=7` amplitude sector has a `Z/7` gap, while the
phase-unit sector is `Z/6`; these are different, incommensurable sectors and
must not be identified, divided through each other, or consumed as a single
phase/gap theorem.  Gate 3 must first prove trivial-sector density and the
continuum lift before any carrier representative, phase quotient, or finite
gap can be consumed by the continuum YM route.

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

Balaban/RG induction gap: the preferred carrier-side YM attack is now the
KP/Balaban route.  This is not "Clay YM" as a solved claim.  It is the
concrete KP/uniform-volume obligation needed for a Balaban-style induction
step:

`H_k -> H_{k+1}` with Kotecky-Preiss polymer local-sum constants, small-field
bounds, large-field tail bounds, counterterm control, and block-averaging
error terms all uniform in lattice volume and stable under cutoff/depth
removal.

The repository now records this obligation explicitly in the Balaban,
polymer/KP, and carrier area-law receipts.  It is not proved or imported, and
`exactDecorrelation` must remain open unless supplied by a separate proof.
The naive 15-prime KP series fails; the admissible proof candidate must first
use a single-prime overlap reduction and then rebuild the KP local-sum bounds
from that reduced overlap surface.  The corrected reduction is only an
overlap-set statement: polymer activity is not multiplicative for
disjoint-prime polymers.  The cross term produced by the overlap split must
be bounded or recorded as an explicit obstruction before any KP/Balaban
local-sum estimate consumes the reduction.
Finite MDL/Fejer descent, finite strong-coupling bounds, and finite polymer
bookkeeping are only support surfaces.  The large/small field split is also
open: the ultrametric small-field sector is the carrier ball controlled by
existing finite estimates, while the large-field sector still needs a
tail-suppression estimate strong enough to feed the volume-independent RG
induction.

Braid boundary: there is no braiding inside one BT tree.  A product of
distinct commuting prime lanes is abelian bookkeeping, not a nonabelian braid
theorem.  Same-prime braid/Yang-Baxter remains an open target and cannot be
used as a proved input to the YM roadmap.

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

Historical broad roadmap context: the current competitive route is not "finite carrier pressure is below the
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

After Sprint 79, the immediate H1 subproblem is narrower: prove the residual
KP graph is blocked-spatial, not fine-lattice spatial. `H1` still means a
genuine volume-independent constructive RG/cluster induction,
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
| Phase/BT-tree guardrail | Keep carrier phase fixing, finite amplitude gaps, and continuum gauge fixing in separate sectors. | Inhabited only as non-Archimedean BT-tree/discrete-resolution bookkeeping.  The `p=7` amplitude `Z/7` gap is not the `Z/6` phase-unit sector. | `CarrierPhaseStructureReceipt`, `GribovFreeCarrierReceipt`, `GribovResolutionAuthorityReceipt` | Need Gate 3 trivial-sector density, a continuum lift, and an independent continuum Gribov/Singer resolution before consuming this data in L5-L9. |
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
spatial volume, prove the corrected single-prime overlap-set reduction and
its cross-term bound, prove `exactDecorrelation` if that route consumes it, prove an
ultrametric large/small field split with the large-field tail suppressed
uniformly enough for `H_k -> H_{k+1}`, and show that the resulting counterterm
and block-averaging errors remain controlled through cutoff/depth removal.
This would be a competitive Yang-Mills contribution if proved; it is currently
only an open obligation.

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
- consuming BT-tree/discrete carrier gauge fixing as a continuum Gribov or
  Singer theorem
- identifying the `p=7` amplitude `Z/7` gap with the phase-unit `Z/6` sector
- consuming carrier phase quotients, carrier representatives, or finite gaps
  before Gate 3 proves trivial-sector density and the continuum lift
- continuum interacting Yang-Mills construction
- operator/Hamiltonian convergence from finite carriers to the continuum
- Balaban volume-independent induction for the continuum constructive route
- KP/uniform-volume Balaban induction
- single-prime overlap-set reduction and its cross-term bound for any KP proof
  after the failed naive 15-prime series
- `exactDecorrelation` as a consumed KP/Balaban input
- ultrametric large/small field split with large-field tail suppression
- same-prime braid/Yang-Baxter theorem, or any nonabelian braid claim from one
  BT tree or from distinct commuting prime lanes
- BRST-compatible reflection positivity for the physical gauge sector
- an operator-valued physical spectral-gap theorem
- any inference of the form "`14 < 15`; therefore Yang-Mills mass gap"
- treating finite/strong-coupling carrier YM as continuum Clay YM
- terminal/unification promotion
