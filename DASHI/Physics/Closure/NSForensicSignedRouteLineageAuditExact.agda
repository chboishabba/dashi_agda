module DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact where

------------------------------------------------------------------------
-- NAVIER--STOKES SIGNED-ROUTE FORENSIC LINEAGE AUDIT
--
-- Direction: EARLIEST RECOVERABLE FORMULATION -> FORWARD SNOWBALL.
--
-- This single file is the audit ledger.  It records dated repository receipts,
-- source attribution, relationship strength, exact formal descendants, and the
-- surviving analytic boundary.  Chronology is evidence of source existence;
-- chronology alone is NOT evidence of mathematical correctness, third-party
-- access, copying, model-training ingestion, or reward hacking.
--
-- Current historical hypothesis, kept typed rather than silently promoted:
-- by 2026-07-26 the repository had assembled the FINAL PROBLEM SPECIFICATION
-- in distributed form: exact signed physical coefficient + cancellation-aware
-- signed-gap route + cutoff-uniform target + arbitrary-data/global consumer.
-- Later tranches progressively instantiate/rewrite that problem on stronger
-- same-object carriers.  This does not assert that every later theorem was
-- already proved on 2026-07-26.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

-- Early and middle formal owners are imported so the ledger records the
-- forward maturation of the problem, not only the newest round-number names.
import DASHI.Physics.Closure.NSWall1CanonicalResolventGap as JulyResolvent
import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient as JulySigned
import DASHI.Physics.Closure.NSTriadKNSignedUniformGapProgram as JulyGap
import DASHI.Physics.Closure.NSTriadKNSignedGapAprioriComposition as JulyApriori
import DASHI.Physics.Closure.NSTriadKNExactCoefficientToPhysicalWeight as JulyPhysical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadFrontierProgram as JulyStage3
import DASHI.Physics.Closure.NSTriadKNLuoNearWindowCommutatorDissipationClosureExact as AugCritical
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalSignedShellCellRound26Exact as AugShell
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorBonyWeldRound123Exact as R123
import DASHI.Physics.Closure.NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact as R228
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNHeatWeightedCommutatorSchurRound301Exact as R301
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact as R351

-- Newest formal descendants are imported transitively so this ledger is also
-- one focused source/type surface for the currently audited formal chain.
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as Weld541x573
import DASHI.Physics.Closure.NSTriadKNSpectatorNestedRowFactorizationBidiExact as NestedRow
import DASHI.Physics.Closure.NSTriadKNDirectCompanionSpectatorNestedRowBidiExact as DirectRow
import DASHI.Physics.Closure.NSTriadKNNestedFactoredFullToDirectFibreBidiExact as NestedFibre
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact as Weighted584
import DASHI.Physics.Closure.NSTriadKNExactBonyClassNormSelfBudgetBidiExact as ExactClassBudget
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact as Exact584Payment

------------------------------------------------------------------------
-- Typed forensic vocabulary.
------------------------------------------------------------------------

data Repository : Set where
  dashiCFD : Repository
  dashiAgda : Repository

data ArtefactRole : Set where
  structuralAncestor : ArtefactRole
  signedCoherencePrecursor : ArtefactRole
  empiricalBarrier : ArtefactRole
  empiricalSignedResidual : ArtefactRole
  signedMajorantBoundary : ArtefactRole
  canonicalResolventBaseline : ArtefactRole
  analyticTrancheAssembly : ArtefactRole
  exactSignedCoefficient : ArtefactRole
  signedUniformGapSpecification : ArtefactRole
  globalAprioriConsumer : ArtefactRole
  physicalSignedAssembly : ArtefactRole
  criticalCommutatorDissipation : ArtefactRole
  signedPhysicalShellLedger : ArtefactRole
  formalCommutator : ArtefactRole
  exactCarrierBonyWeld : ArtefactRole
  spacetimeFrontier : ArtefactRole
  resolventTemporalFlux : ArtefactRole
  formalWeightedCancellation : ArtefactRole
  sameObjectSchurFrontier : ArtefactRole
  resolventAbsorptionAdapter : ArtefactRole
  liveSignedCarrier : ArtefactRole
  directResolventRepresentation : ArtefactRole
  terminalSignedConsumer : ArtefactRole
  spectatorResolventWeight : ArtefactRole
  nestedSignedRepresentation : ArtefactRole
  liveNestedClassNormCarrier : ArtefactRole
  compositionWeld : ArtefactRole
  exactClassPaymentCompiler : ArtefactRole
  survivingAnalyticBoundary : ArtefactRole

data RelationshipStrength : Set where
  broadStructuralAncestry : RelationshipStrength
  empiricalMethodPrecursor : RelationshipStrength
  representationBoundary : RelationshipStrength
  architectureAssembly : RelationshipStrength
  problemSpecification : RelationshipStrength
  physicalInstantiation : RelationshipStrength
  formalRefinement : RelationshipStrength
  exactSameObject : RelationshipStrength
  exactSpecialization : RelationshipStrength
  compositionInput : RelationshipStrength
  canonicalConsumer : RelationshipStrength
  analyticFrontier : RelationshipStrength

record ForensicReceipt : Set where
  constructor forensic-receipt
  field
    repository : Repository
    artefact : String
    path : String
    firstCommit : String
    firstImplementedUTC : String
    firstImplementedBrisbane : String
    author : String
    role : ArtefactRole
    forensicRelationship : String

open ForensicReceipt public

record SnowballEdge : Set where
  constructor snowball-edge
  field
    fromArtefact : String
    toArtefact : String
    strength : RelationshipStrength
    rationale : String
    exactSameCarrierProved : Bool

open SnowballEdge public

------------------------------------------------------------------------
-- EARLIEST-FIRST CHRONOLOGY.
------------------------------------------------------------------------

jan24StructuralCarrier : ForensicReceipt
jan24StructuralCarrier = forensic-receipt
  dashiCFD
  "initial signed/ternary CFD structural carrier"
  "COMPACTIFIED_CONTEXT.md; dashi_les_vorticity_codec_v2.py; dashi_signed_branchedflow_codec.npz"
  "1cb1bb612c4061676a06e615f69bf282462c25cc"
  "2026-01-24T09:06:14Z"
  "2026-01-24T19:06:14+10:00"
  "Johl Brown"
  structuralAncestor
  "spectral LES/residual codec and signed anomaly -> ternary state -> support -> residual; broad methodological ancestor only"

jan27SignedFilament : ForensicReceipt
jan27SignedFilament = forensic-receipt
  dashiCFD
  "signed filament annihilation / coherence note"
  "docs/signed_filament_annihilation.md"
  "7938f8282541b142e93cb2a7dadf32d83ca553b3"
  "2026-01-27T14:33:22Z"
  "2026-01-28T00:33:22+10:00"
  "Johl Brown"
  signedCoherencePrecursor
  "factorises F_k into support x sign, separates interpretation from operator, and requires coarse-graining/annihilation not to create new support; conceptual precursor only"

jun03ThetaBarrier : ForensicReceipt
jun03ThetaBarrier = forensic-receipt
  dashiCFD
  "full NS theta flux/dissipation sweep"
  "scripts/ns_theta_full_sweep.py"
  "125e52e04bed4042890d95db5d5371104ba1aafe"
  "2026-06-03T14:15:39Z"
  "2026-06-04T00:15:39+10:00"
  "Johl Brown"
  empiricalBarrier
  "empirical high-frequency theta barrier using |Flux_{>k}| / Diss_{>k}; promotion explicitly disabled"

jun04SignedFlip : ForensicReceipt
jun04SignedFlip = forensic-receipt
  dashiCFD
  "signed ternary cross-shell flip audit"
  "scripts/ns_signed_ternary_flip_audit.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z"
  "2026-06-04T14:13:12+10:00"
  "Johl Brown"
  empiricalSignedResidual
  "cross-shell minus/plus flow treated as an involutive signed channel; signed imbalance and net residue precede magnitude diagnostics"

jun04MaterialParent : ForensicReceipt
jun04MaterialParent = forensic-receipt
  dashiCFD
  "material-parent cross-shell provenance carrier"
  "scripts/ns_material_parent_summary.py; scripts/ns_ternary_cross_shell_matrix.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z"
  "2026-06-04T14:13:12+10:00"
  "Johl Brown"
  empiricalSignedResidual
  "material-parent/cross-shell carrier consumed by the signed-flip audit"

jul20MajorantSeparation : ForensicReceipt
jul20MajorantSeparation = forensic-receipt
  dashiAgda
  "signed response separated from pair-majorant kernel"
  "compact-Gamma off-packet Schur/pair-incidence tranche; commit message: fix(ns): separate signed response from pair-majorant kernel"
  "723bf33bd9bf1947eb5bbda6dd3df700b5b05e39"
  "2026-07-20T00:00:00Z"
  "2026-07-20T10:00:00+10:00"
  "Johl Brown"
  signedMajorantBoundary
  "signed compact-Gamma response is not definitionally the nonnegative pair-incidence majorant; the required relation is majorization, preserving the representation-loss boundary"

jul20CanonicalResolvent : ForensicReceipt
jul20CanonicalResolvent = forensic-receipt
  dashiAgda
  "fail-closed canonical finite resolvent and strict gap baseline"
  "DASHI/Physics/Closure/NSWall1CanonicalResolventGap.agda"
  "d10569457f09993174e1b921935dadb1eebced05"
  "2026-07-20T01:43:20Z"
  "2026-07-20T11:43:20+10:00"
  "Johl Brown"
  canonicalResolventBaseline
  "resolvent/gap coordinate exists, but the six-mode baseline is explicitly not identified with the physical low block without a representation theorem"

jul20PR145 : ForensicReceipt
jul20PR145 = forensic-receipt
  dashiAgda
  "PR #145 rational six-mode Wall1 Schur/resolvent/gap packet"
  "pull/145: Close rational six-mode Wall1 Schur packet"
  "8905dc5c4c3389f18698f1669040dcf5923af0c6"
  "2026-07-20T03:02:06Z"
  "2026-07-20T13:02:06+10:00"
  "Johl Brown"
  analyticTrancheAssembly
  "finite Schur certificates + baseline low resolvent + strict packet gap assembled while physical representation remains fail-closed"

jul20PR140 : ForensicReceipt
jul20PR140 = forensic-receipt
  dashiAgda
  "PR #140 compact-Gamma signed-response / Schur / tail architecture"
  "pull/140: feat(ns): audit off-packet compact-Gamma Schur-tail control"
  "e64a38ab617cf88035555a07a223afe46480df0e"
  "2026-07-20T06:17:05Z"
  "2026-07-20T16:17:05+10:00"
  "Johl Brown"
  analyticTrancheAssembly
  "signed near response, exact pair-incidence majorant, row/column Schur target, explicit far tail and D-log-E consumer are assembled; signed response remains distinct from nonnegative majorant"

jul20PR227 : ForensicReceipt
jul20PR227 = forensic-receipt
  dashiAgda
  "PR #227 cross-pollinated compact-Gamma analytic closure stack"
  "pull/227: Cross-pollinate the compact-Gamma analytic closure stack"
  "c2b313a0878b0281781dd7a1bf3ae851d24af8d9"
  "2026-07-20T09:42:15Z"
  "2026-07-20T19:42:15+10:00"
  "Johl Brown"
  analyticTrancheAssembly
  "differentiated triads + exact full-shell pair incidence + quantitative tail + Galerkin passage + invariant region + BKM continuation are integrated into one proof-relevant closure architecture"

jul20PR255 : ForensicReceipt
jul20PR255 = forensic-receipt
  dashiAgda
  "PR #255 concrete far-tail commutator decay"
  "pull/255: feat(ns): expose concrete far-tail commutator decay"
  "bc9a627985cf4140ee10260f6399050aacf5cba4"
  "2026-07-20T15:09:40Z"
  "2026-07-21T01:09:40+10:00"
  "Johl Brown"
  analyticTrancheAssembly
  "far-low Fourier cancellation + multiplier commutator + dyadic gain + far-high Sobolev tail + cutoff-uniform epsilon(R) endpoint fill the explicit tail coordinate"

jul25PR336 : ForensicReceipt
jul25PR336 = forensic-receipt
  dashiAgda
  "PR #336 exact signed multiplier-difference commutator frontier"
  "pull/336: Add exact Wall-I commutator and cube-Bernstein frontier"
  "68ab8ffbcf5c0aa791720a454dbeb1631ea933b2"
  "2026-07-25T07:09:05Z"
  "2026-07-25T17:09:05+10:00"
  "Johl Brown"
  signedMajorantBoundary
  "owns K_raw, signed K_diff and K_absdiff separately; exact commutator identity precedes norms; absolute l1 Schur failure points explicitly toward sign-sensitive estimates"

jul26ExactSignedCoefficient : ForensicReceipt
jul26ExactSignedCoefficient = forensic-receipt
  dashiAgda
  "exact signed velocity-form Galerkin coefficient"
  "DASHI/Physics/Closure/NSTriadKNExactSignedGalerkinCoefficient.agda"
  "466c9cdea3336fb3b27fbf578887d6e619bf5953"
  "2026-07-26T02:44:07Z"
  "2026-07-26T12:44:07+10:00"
  "Johl Brown"
  exactSignedCoefficient
  "literal tested -i P_k[(u_p.q)u_q] and ordered pair; no positive part, absolute value, phase ansatz or hidden half factor"

jul26PhysicalMajorantBridge : ForensicReceipt
jul26PhysicalMajorantBridge = forensic-receipt
  dashiAgda
  "exact signed coefficient connected to retained physical triads and named majorant"
  "DASHI/Physics/Closure/NSTriadKNExactCoefficientToPhysicalWeight.agda"
  "a4f38a003e74cfb31d8dc452a0e1eb7c6fc565ca"
  "2026-07-26T02:46:25Z"
  "2026-07-26T12:46:25+10:00"
  "Johl Brown"
  physicalSignedAssembly
  "raw retained coefficient remains exact and signed; Nat kernel weight is explicitly only coefficientMajorant(raw coefficient)"

jul26PhysicalStage3 : ForensicReceipt
jul26PhysicalStage3 = forensic-receipt
  dashiAgda
  "signed physical Stage-3 frontier aggregate"
  "DASHI/Physics/Closure/NSTriadKNPhysicalTriadFrontierProgram.agda"
  "5e1ae9dc413a9447bfa515a784bdeb08dab53f2e"
  "2026-07-26T02:51:51Z"
  "2026-07-26T12:51:51+10:00"
  "Johl Brown"
  physicalSignedAssembly
  "aggregates exact signed coefficient, positive-part cancellation no-go, physical fibres, classwise envelope bookkeeping, finite-to-uniform no-go and Galerkin-to-arbitrary-data global cutset"

jul26SignedGapProgram : ForensicReceipt
jul26SignedGapProgram = forensic-receipt
  dashiAgda
  "signed cutoff-uniform gap program"
  "DASHI/Physics/Closure/NSTriadKNSignedUniformGapProgram.agda"
  "e8d8781781f825f3b27fbf578887d6e619bf5953"
  "2026-07-26T03:25:40Z"
  "2026-07-26T13:25:40+10:00"
  "Johl Brown"
  signedUniformGapSpecification
  "Route B explicitly preserves signed blocks and asks for permutation, reality-orbit and complete-triad cancellation plus a cutoff-uniform symmetric numerical-range bound"

jul26GapApriori : ForensicReceipt
jul26GapApriori = forensic-receipt
  dashiAgda
  "strict signed gap to arbitrary-data uniform a-priori composition"
  "DASHI/Physics/Closure/NSTriadKNSignedGapAprioriComposition.agda"
  "a872ad2a4249e2d6f1056595df980000fe7472aa"
  "2026-07-26T04:17:22Z"
  "2026-07-26T14:17:22+10:00"
  "Johl Brown"
  globalAprioriConsumer
  "strict signed nonlinearity<=dissipation plus exact energy identity feeds cutoff-independent arbitrary-data a-priori control; no smallness, symmetry, phase or helicity restriction"

aug05CriticalDissipation : ForensicReceipt
aug05CriticalDissipation = forensic-receipt
  dashiAgda
  "commutator criticality composed with terminal dissipation"
  "DASHI/Physics/Closure/NSTriadKNLuoNearWindowCommutatorDissipationClosureExact.agda"
  "8d5c3436b6fde86719b54d323113a69360adbc2d"
  "2026-08-05T11:13:30Z"
  "2026-08-05T21:13:30+10:00"
  "Johl Brown"
  criticalCommutatorDissipation
  "critical commutator factor and independently owned terminal dissipation smallness are composed; continuum PDE estimate remains the genuine leaf"

aug08SignedShell : ForensicReceipt
aug08SignedShell = forensic-receipt
  dashiAgda
  "literal physical five-source fibre to signed critical shell cell"
  "DASHI/Physics/Closure/NSTriadKNLuoPhysicalSignedShellCellRound26Exact.agda"
  "19aa8cb1d7b373fdf74ac0674832477a94d98f5a"
  "2026-08-08T06:50:21Z"
  "2026-08-08T16:50:21+10:00"
  "Johl Brown"
  signedPhysicalShellLedger
  "forces HH+LH+HL+CC+commutator source coordinates from the literal physical output fibre and the genuine shell energy balance"

aug27R120 : ForensicReceipt
aug27R120 = forensic-receipt
  dashiAgda "R120 physical shared-output pure commutator partner"
  "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorPartnerRound120Exact.agda"
  "7ba2a203e355f4cbb2b4888f6ae408f4c17ef58b"
  "2026-08-27T13:51:37Z" "2026-08-27T23:51:37+10:00"
  "Johl Brown" formalCommutator
  "formal shared-output commutator identity; not retroactively equated to the empirical or July objects"

aug27R123 : ForensicReceipt
aug27R123 = forensic-receipt
  dashiAgda
  "R123 full physical quartic fold to signed pure-commutator Bony sums"
  "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorBonyWeldRound123Exact.agda"
  "1ccc381d7d2b71e6add0110d1575a8d35242496c"
  "2026-08-27T14:06:10Z"
  "2026-08-28T00:06:10+10:00"
  "Johl Brown"
  exactCarrierBonyWeld
  "end-to-end exact carrier weld: twice full physical quartic fold equals four signed Bony commutator folds with no cellwise absolute value/cardinality tax"

aug29R228 : ForensicReceipt
aug29R228 = forensic-receipt
  dashiAgda
  "R228 final mixed-helicity spacetime Package-A leaf"
  "DASHI/Physics/Closure/NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact.agda"
  "2b18f2f747863c67a9274463891774a4170d8fa0"
  "2026-08-29T13:01:57Z"
  "2026-08-29T23:01:57+10:00"
  "Johl Brown"
  spacetimeFrontier
  "after exact mixed-helicity collapse, names one remaining PDE theorem: cutoff-uniform spacetime bound for the physical mixed-helicity convolution mass"

aug30R290 : ForensicReceipt
aug30R290 = forensic-receipt
  dashiAgda
  "R290 resolvent-weighted temporal Gram flux compiler"
  "DASHI/Physics/Closure/NSTriadKNWeightedGramFluxCompilerRound290Exact.agda"
  "9bc61ac8e9b046c7bcb781fb5badba5654d1acf0"
  "2026-08-30T11:08:41Z"
  "2026-08-30T21:08:41+10:00"
  "Johl Brown"
  resolventTemporalFlux
  "uses viscous pair-rate resolvent w*lambda=1 to rewrite coherent Gram debt as endpoint flux plus weighted nonlinear remainder"

aug30R294 : ForensicReceipt
aug30R294 = forensic-receipt
  dashiAgda "R294 swap-invariant weighted commutator collapse"
  "DASHI/Physics/Closure/NSTriadKNResolventWeightedMixedCommutatorRound294Exact.agda"
  "64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "2026-08-30T11:19:48Z" "2026-08-30T21:19:48+10:00"
  "Johl Brown" formalWeightedCancellation
  "generic swap-invariant weight preserves mixed-commutator cancellation before absolute values"

aug31R301 : ForensicReceipt
aug31R301 = forensic-receipt
  dashiAgda
  "R301 same-object heat-weighted R294 spacetime/Schur frontier"
  "DASHI/Physics/Closure/NSTriadKNHeatWeightedCommutatorSchurRound301Exact.agda"
  "489f48fac67b7effe1ffd6200c7f614ff4d60a0d"
  "2026-08-31T10:04:17Z"
  "2026-08-31T20:04:17+10:00"
  "Johl Brown"
  sameObjectSchurFrontier
  "requires the literal heat-weighted R294 commutator remain on the SAME carrier; row/column budgets and spacetime integrability are the explicit leaves"

aug31R351 : ForensicReceipt
aug31R351 = forensic-receipt
  dashiAgda
  "R351 nested spacetime payment to existing resolvent absorption consumer"
  "DASHI/Physics/Closure/NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact.agda"
  "523909ea07409de82e225153572bfbc8f91b7e35"
  "2026-08-31T14:58:10Z"
  "2026-09-01T00:58:10+10:00"
  "Johl Brown"
  resolventAbsorptionAdapter
  "paid R301 spacetime forcing mass feeds the already-owned R300 integrated resolvent Young-absorption consumer by order monotonicity only"

sep01R406 : ForensicReceipt
sep01R406 = forensic-receipt
  dashiAgda "R406 fixed-output live global flux"
  "DASHI/Physics/Closure/NSTriadKNFixedOutputLiveGlobalFluxRound406Exact.agda"
  "341747bff0c977aadc89f8f55b05225b1c9ce15c"
  "2026-09-01T05:21:27Z" "2026-09-01T15:21:27+10:00"
  "Johl Brown" liveSignedCarrier
  "puts the live R378/R406 flux on a fixed canonical output list"

sep07R496 : ForensicReceipt
sep07R496 = forensic-receipt
  dashiAgda "R496 direct nonseparable resolvent pair companion"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventPairCompanionRound496Exact.agda"
  "9be2933f265e95ccc9f2dca5204b21bc528fc393"
  "2026-09-07T18:53:49Z" "2026-09-08T04:53:49+10:00"
  "Johl Brown" directResolventRepresentation
  "literal weighted remainder represented by the canonical direct Cauchy-resolvent pair companion"

sep07R503 : ForensicReceipt
sep07R503 = forensic-receipt
  dashiAgda "R503 direct off-diagonal signed resolvent budget consumer"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda"
  "984eaa83d988b0292ead61cfef8e9db463cbb425"
  "2026-09-07T19:02:43Z" "2026-09-08T05:02:43+10:00"
  "Johl Brown" terminalSignedConsumer
  "canonical terminal consumer preserves sign and asks for a cutoff-uniform one-sided direct-companion bound"

sep09R541 : ForensicReceipt
sep09R541 = forensic-receipt
  dashiAgda "R541 spectator Cauchy resolvent as R294 weight"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventR294WeightRound541Exact.agda"
  "350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "2026-09-09T04:56:22Z" "2026-09-09T14:56:22+10:00"
  "Johl Brown" spectatorResolventWeight
  "fixed beta turns the literal nonseparable Cauchy pair kernel into an exact swap-invariant R294 weight in alpha"

sep09R573 : ForensicReceipt
sep09R573 = forensic-receipt
  dashiAgda "R573 weighted nested four-sign commutator"
  "DASHI/Physics/Closure/NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact.agda"
  "8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "2026-09-09T09:17:38Z" "2026-09-09T19:17:38+10:00"
  "Johl Brown" nestedSignedRepresentation
  "actual weighted outer commutator represented by the nested four-sign inner carrier before norms"

sep09R584 : ForensicReceipt
sep09R584 = forensic-receipt
  dashiAgda "R584 live nested-slot Bony class-norm carrier"
  "DASHI/Physics/Closure/NSTriadKNNestedSlotBonyClassNormBidiRound584Exact.agda"
  "b42b6510c4025d835192d1d84d188ed87426abc9"
  "2026-09-09T14:49:15Z" "2026-09-10T00:49:15+10:00"
  "Johl Brown" liveNestedClassNormCarrier
  "class norms attached to the actual R573 slot-transformed cells; outer weight/spacetime remained open at first implementation"

sep10R541xR573 : ForensicReceipt
sep10R541xR573 = forensic-receipt
  dashiAgda "first explicit R541 x R573 spectator-resolvent nested composition"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventNestedCommutatorBidiExact.agda"
  "b06ec702a45c595449c044a19ad14d5b37327ace"
  "2026-09-10T05:01:10Z" "2026-09-10T15:01:10+10:00"
  "Johl Brown" compositionWeld
  "instantiates R573 directly with R541.spectatorWeight beta before norm/absolute value/Schur/Laplace"

sep10NestedRow : ForensicReceipt
sep10NestedRow = forensic-receipt
  dashiAgda "spectator force row through nested signed fold"
  "DASHI/Physics/Closure/NSTriadKNSpectatorNestedRowFactorizationBidiExact.agda"
  "739db0214023c5c6150022af27c2f40d0ccf2c3a"
  "2026-09-10T05:58:00Z" "2026-09-10T15:58:00+10:00"
  "Johl Brown" compositionWeld
  "force half of the R545 row reaches the R573 nested signed fold before norm/absolute value"

sep10DirectRow : ForensicReceipt
sep10DirectRow = forensic-receipt
  dashiAgda "direct companion to nested spectator row"
  "DASHI/Physics/Closure/NSTriadKNDirectCompanionSpectatorNestedRowBidiExact.agda"
  "f8318253e070dd4400756be36e465f04f9cb68c3"
  "2026-09-10T06:02:34Z" "2026-09-10T16:02:34+10:00"
  "Johl Brown" compositionWeld
  "same spectator pair scalar is four times the canonical R496 direct companion, lifted over finite rows"

sep10NestedFibre : ForensicReceipt
sep10NestedFibre = forensic-receipt
  dashiAgda "nested factored-full to canonical direct fibre"
  "DASHI/Physics/Closure/NSTriadKNNestedFactoredFullToDirectFibreBidiExact.agda"
  "68767078ec9158752189af8273192f1c227e97fc"
  "2026-09-10T06:05:32Z" "2026-09-10T16:05:32+10:00"
  "Johl Brown" compositionWeld
  "nested factored-full lands on diagonal + 2*(4*R497 direct fibre companion) without erasing the diagonal"

sep10Weighted584 : ForensicReceipt
sep10Weighted584 = forensic-receipt
  dashiAgda "R541 spectator weight instantiated into live R584 class norms"
  "DASHI/Physics/Closure/NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact.agda"
  "6bdbb7df8cd0e65d7d0f782b016bd928ede07b15"
  "2026-09-10T06:16:58Z" "2026-09-10T16:16:58+10:00"
  "Johl Brown" compositionWeld
  "removes abstract-outer-weight debt by specializing R584 to the literal R541 spectator resolvent"

sep10ExactClassBudgets : ForensicReceipt
sep10ExactClassBudgets = forensic-receipt
  dashiAgda "exact R582/R583 class-norm self budgets"
  "DASHI/Physics/Closure/NSTriadKNExactBonyClassNormSelfBudgetBidiExact.agda"
  "d53ad93f79f625e0677b9ce2b92ce473ea55eeff"
  "2026-09-10T06:20:22Z" "2026-09-10T16:20:22+10:00"
  "Johl Brown" exactClassPaymentCompiler
  "closes mere existence of class-norm budgets by exact self ceilings; useful uniform envelope remains open"

sep10Exact584Payments : ForensicReceipt
sep10Exact584Payments = forensic-receipt
  dashiAgda "exact class-budget payments on live spectator R584 carrier"
  "DASHI/Physics/Closure/NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact.agda"
  "ac898d515c3e9f2882c3b2102eaa5fc75fa2a2c3"
  "2026-09-10T06:20:48Z" "2026-09-10T16:20:48+10:00"
  "Johl Brown" exactClassPaymentCompiler
  "constructs live R584 class-norm payment witnesses; useful cutoff-uniform envelope and spacetime transport remain open"

------------------------------------------------------------------------
-- Attribution atlas. Repository commits/artefacts have no DOI.
------------------------------------------------------------------------

repoSource : String → String → String → String → Source.AttributedSource
repoSource title context url relationship =
  Source.mkNoDOISource "Johl Brown" title context "2026" url
    (Source.namedSourceKind "GitHub repository source/commit/PR")
    relationship Source.publicAttribution

jan24Source : Source.AttributedSource
jan24Source = repoSource
  "dashiCFD initial signed/ternary structural carrier"
  "chboishabba/dashiCFD commit 1cb1bb612c4061676a06e615f69bf282462c25cc"
  "https://github.com/chboishabba/dashiCFD/commit/1cb1bb612c4061676a06e615f69bf282462c25cc"
  "broad methodological ancestor only; not a Navier-Stokes proof receipt"

jan27Source : Source.AttributedSource
jan27Source = repoSource
  "Signed Filament Annihilation"
  "chboishabba/dashiCFD commit 7938f8282541b142e93cb2a7dadf32d83ca553b3"
  "https://github.com/chboishabba/dashiCFD/commit/7938f8282541b142e93cb2a7dadf32d83ca553b3"
  "signed support/coherence/annihilation conceptual precursor; not promoted to an NS theorem"

jun03Source : Source.AttributedSource
jun03Source = repoSource
  "ns_theta_full_sweep.py"
  "chboishabba/dashiCFD commit 125e52e04bed4042890d95db5d5371104ba1aafe"
  "https://github.com/chboishabba/dashiCFD/commit/125e52e04bed4042890d95db5d5371104ba1aafe"
  "empirical flux/dissipation barrier precursor; absolute value occurs before ratio"

jun04Source : Source.AttributedSource
jun04Source = repoSource
  "ns_signed_ternary_flip_audit.py and material-parent carrier"
  "chboishabba/dashiCFD commit 1c9ca183515e3a26988ae21785de9a45481e37d2"
  "https://github.com/chboishabba/dashiCFD/commit/1c9ca183515e3a26988ae21785de9a45481e37d2"
  "empirical signed cross-shell/net-residue precursor"

july26Source : Source.AttributedSource
july26Source = repoSource
  "Exact signed coefficient + signed uniform gap + arbitrary-data consumer"
  "chboishabba/dashi_agda 2026-07-26 distributed tranche"
  "https://github.com/chboishabba/dashi_agda/commit/e8d8781781f825f3b27fbf578887d6e619bf5953"
  "earliest currently recovered assembled final-problem specification; not an assertion that the missing uniform signed estimate was proved"

r123Source : Source.AttributedSource
r123Source = repoSource
  "R123 full physical quartic to signed commutator Bony weld"
  "chboishabba/dashi_agda commit 1ccc381d7d2b71e6add0110d1575a8d35242496c"
  "https://github.com/chboishabba/dashi_agda/commit/1ccc381d7d2b71e6add0110d1575a8d35242496c"
  "exact physical-carrier signed Bony weld without pre-norm absolute values"

r294Source : Source.AttributedSource
r294Source = repoSource
  "R294 swap-invariant weighted commutator collapse"
  "chboishabba/dashi_agda commit 64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "https://github.com/chboishabba/dashi_agda/commit/64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "formal weighted cancellation before absolute values"

r301Source : Source.AttributedSource
r301Source = repoSource
  "R301 same-object heat-weighted commutator spacetime frontier"
  "chboishabba/dashi_agda commit 489f48fac67b7effe1ffd6200c7f614ff4d60a0d"
  "https://github.com/chboishabba/dashi_agda/commit/489f48fac67b7effe1ffd6200c7f614ff4d60a0d"
  "requires the literal R294 carrier for Schur/spacetime payment rather than an analogous proxy"

r503Source : Source.AttributedSource
r503Source = repoSource
  "R503 direct off-diagonal signed resolvent consumer"
  "chboishabba/dashi_agda commit 984eaa83d988b0292ead61cfef8e9db463cbb425"
  "https://github.com/chboishabba/dashi_agda/commit/984eaa83d988b0292ead61cfef8e9db463cbb425"
  "canonical signed cutoff-uniform terminal consumer; does not pay its own analytic field"

r541Source : Source.AttributedSource
r541Source = repoSource
  "R541 spectator Cauchy resolvent weight"
  "chboishabba/dashi_agda commit 350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "https://github.com/chboishabba/dashi_agda/commit/350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "exact spectator specialization of the pair resolvent into the R294 weight interface"

r573Source : Source.AttributedSource
r573Source = repoSource
  "R573 weighted nested componentwise commutator"
  "chboishabba/dashi_agda commit 8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "https://github.com/chboishabba/dashi_agda/commit/8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "exact nested four-sign same-object representation of the weighted outer commutator"

r584Source : Source.AttributedSource
r584Source = repoSource
  "R584 live nested-slot Bony class-norm carrier"
  "chboishabba/dashi_agda commit b42b6510c4025d835192d1d84d188ed87426abc9"
  "https://github.com/chboishabba/dashi_agda/commit/b42b6510c4025d835192d1d84d188ed87426abc9"
  "same slot-transformed carrier for class-norm proof search"

weldSource : Source.AttributedSource
weldSource = repoSource
  "R541 x R573 spectator-resolvent nested composition"
  "chboishabba/dashi_agda commit b06ec702a45c595449c044a19ad14d5b37327ace"
  "https://github.com/chboishabba/dashi_agda/commit/b06ec702a45c595449c044a19ad14d5b37327ace"
  "first audited explicit named specialization of R573 by R541.spectatorWeight beta"

forensicSourceAtlas : Source.AttributedSourceAtlas
forensicSourceAtlas = Source.mkSourceAtlas
  "NS signed-route earliest-forward forensic source atlas"
  "DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact"
  (jan24Source ∷ jan27Source ∷ jun03Source ∷ jun04Source ∷ july26Source
    ∷ r123Source ∷ r294Source ∷ r301Source ∷ r503Source ∷ r541Source
    ∷ r573Source ∷ r584Source ∷ weldSource ∷ [])
  "public Git repository chronology and formalisation relationships; citation does not import correctness, external access, influence or authority"

------------------------------------------------------------------------
-- Earliest-forward snowball.
------------------------------------------------------------------------

edgeJan24ToJan27 : SnowballEdge
edgeJan24ToJan27 = snowball-edge
  "2026-01-24 signed/ternary structural codec"
  "2026-01-27 signed filament annihilation"
  broadStructuralAncestry
  "generic sign/support/residual codec is refined into an explicit signed field, support/sign factorisation and non-support-creating coarse-graining rule"
  false

edgeJan27ToSignedFlip : SnowballEdge
edgeJan27ToSignedFlip = snowball-edge
  "2026-01-27 signed filament annihilation"
  "2026-06-04 signed cross-shell flip audit"
  empiricalMethodPrecursor
  "sign-first/coherence-first residual language becomes a concrete signed cross-shell transfer audit"
  false

edgeJan24ToTheta : SnowballEdge
edgeJan24ToTheta = snowball-edge
  "2026-01-24 signed/ternary structural codec"
  "2026-06-03 theta flux/dissipation sweep"
  broadStructuralAncestry
  "same multiscale residual programme, but no same-object theorem claim"
  false

edgeJuneToJulyMajorantBoundary : SnowballEdge
edgeJuneToJulyMajorantBoundary = snowball-edge
  "June signed transfer + theta barrier experiments"
  "2026-07-20 signed-response / majorant separation"
  representationBoundary
  "the formal programme explicitly distinguishes the signed response from the positive pair-majorant rather than treating magnitude as the operator"
  false

edgeJulyArchitecture : SnowballEdge
edgeJulyArchitecture = snowball-edge
  "2026-07-20 compact-Gamma Schur/tail tranches"
  "2026-07-26 signed physical final-problem specification"
  architectureAssembly
  "near response, tail, exact pair incidence, Galerkin/BKM consumer architecture is combined with an exact signed coefficient and cutoff-uniform signed-gap target"
  false

edgeJuly26FinalProblemSpecification : SnowballEdge
edgeJuly26FinalProblemSpecification = snowball-edge
  "2026-07-26 exact signed physical coefficient"
  "2026-07-26 signed uniform gap -> arbitrary-data a-priori consumer"
  problemSpecification
  "all principal coordinates of the later final problem are simultaneously named: exact signed physical operator, cancellation-aware gap, cutoff uniformity, dissipation comparator and global consumer; the quantitative signed estimate remains open"
  false

edgeJulyPhysicalToAugShell : SnowballEdge
edgeJulyPhysicalToAugShell = snowball-edge
  "2026-07-26 signed physical Stage-3 aggregate"
  "2026-08-08 literal physical signed shell ledger"
  physicalInstantiation
  "abstract signed physical frontier is instantiated onto a genuine energy balance whose five source coordinates are forced by the literal physical output fibre"
  true

edgeAugShellToR123 : SnowballEdge
edgeAugShellToR123 = snowball-edge
  "2026-08-08 physical signed shell carrier"
  "2026-08-27 R123 exact signed commutator/Bony carrier"
  formalRefinement
  "physical signed bookkeeping matures into a complete physical quartic-to-pure-commutator Bony equality before cellwise absolute value"
  false

edgeR123ToR228 : SnowballEdge
edgeR123ToR228 = snowball-edge
  "R123 exact signed commutator/Bony carrier"
  "R228 mixed-helicity spacetime frontier"
  formalRefinement
  "finite signed cancellations and helicity decomposition reduce Package A to one cutoff-uniform physical spacetime theorem"
  false

edgeR228ToR290 : SnowballEdge
edgeR228ToR290 = snowball-edge
  "R228 cutoff-uniform mixed-helicity spacetime frontier"
  "R290 resolvent-weighted temporal Gram flux"
  formalRefinement
  "the spacetime problem is re-expressed through viscous pair damping and a literal resolvent weight, moving Gram debt to endpoint flux plus weighted nonlinear remainder"
  false

edgeR290ToR294 : SnowballEdge
edgeR290ToR294 = snowball-edge
  "R290 resolvent-weighted nonlinear remainder"
  "R294 swap-invariant weighted mixed commutator"
  formalRefinement
  "the weighted nonlinear remainder acquires an exact cancellation-preserving commutator carrier"
  false

edgeR294ToR301 : SnowballEdge
edgeR294ToR301 = snowball-edge
  "R294 weighted commutator"
  "R301 same-object heat-weighted Schur/spacetime leaf"
  canonicalConsumer
  "R301 explicitly requires the actual R294 carrier and rejects analogous commutator proxies; row/column/spacetime estimates become the named payment"
  true

edgeR301ToR351 : SnowballEdge
edgeR301ToR351 = snowball-edge
  "R301 paid nested/commutator spacetime mass"
  "R351 existing resolvent absorption consumer"
  canonicalConsumer
  "the payment plugs directly into the already-owned R300 resolvent absorption leaf by monotonicity; no new consumer architecture is introduced"
  true

edgeR351ToR503 : SnowballEdge
edgeR351ToR503 = snowball-edge
  "R351 resolvent-spacetime producer/consumer path"
  "R503 direct signed resolvent terminal consumer"
  formalRefinement
  "later rounds replace/re-express the same overall signed-resolvent spacetime obligation on a more literal direct companion carrier"
  false

edgeSignedFlipToR294 : SnowballEdge
edgeSignedFlipToR294 = snowball-edge
  "2026-06-04 signed flip/net residue"
  "2026-08-30 R294 weighted commutator"
  empiricalMethodPrecursor
  "signed cancellation before positive majorization survives as formal design language; objects are not identified"
  false

edgeR120ToR294 : SnowballEdge
edgeR120ToR294 = snowball-edge
  "R120 physical commutator partner" "R294 swap-invariant weighted commutator"
  formalRefinement
  "formal commutator carrier is preserved under a generic swap-invariant weight"
  true

edgeR294ToR541 : SnowballEdge
edgeR294ToR541 = snowball-edge
  "R294 generic swap-invariant weight" "R541 literal spectator Cauchy weight"
  exactSpecialization
  "R541 constructs the literal spectator resolvent as an R294 SwapInvariantCellWeight"
  true

edgeR294ToR573 : SnowballEdge
edgeR294ToR573 = snowball-edge
  "R294 weighted commutator" "R573 nested weighted four-sign carrier"
  exactSameObject
  "R573 proves the actual weighted outer carrier equals its nested four-sign representation before norms"
  true

edgeR541ToWeld : SnowballEdge
edgeR541ToWeld = snowball-edge
  "R541 spectator resolvent" "R541 x R573 explicit composition"
  compositionInput "R541.spectatorWeight beta is instantiated directly into R573" true

edgeR573ToWeld : SnowballEdge
edgeR573ToWeld = snowball-edge
  "R573 nested weighted commutator" "R541 x R573 explicit composition"
  compositionInput "generic R573 receives the literal R541 spectator weight" true

edgeWeldToDirect : SnowballEdge
edgeWeldToDirect = snowball-edge
  "R541 x R573 nested spectator weld" "R496/R497 direct resolvent companion route"
  exactSameObject
  "nested spectator row composes through the literal pair scalar to four times the canonical direct companion"
  true

edgeDirectToR503 : SnowballEdge
edgeDirectToR503 = snowball-edge
  "R496/R497/R500 direct companion" "R503 terminal signed consumer"
  canonicalConsumer "R503 consumes the exact integrated direct companion and preserves sign" true

edgeR584ToWeighted584 : SnowballEdge
edgeR584ToWeighted584 = snowball-edge
  "R584 live nested-slot class norm carrier" "R541-weighted live R584 carrier"
  exactSpecialization
  "R584 generic outer weight is instantiated by the literal R541 spectator Cauchy weight"
  true

edgeWeighted584ToCurrentWall : SnowballEdge
edgeWeighted584ToCurrentWall = snowball-edge
  "R541-weighted live R584 exact class payments"
  "cutoff-uniform spectator-weighted class-norm/spacetime envelope"
  analyticFrontier
  "exact payment witnesses now exist; useful cutoff-uniform majorant and spacetime transport remain theorem-bearing"
  false

forensicSnowball : List SnowballEdge
forensicSnowball =
  edgeJan24ToJan27 ∷ edgeJan27ToSignedFlip ∷ edgeJan24ToTheta ∷
  edgeJuneToJulyMajorantBoundary ∷ edgeJulyArchitecture ∷
  edgeJuly26FinalProblemSpecification ∷ edgeJulyPhysicalToAugShell ∷
  edgeAugShellToR123 ∷ edgeR123ToR228 ∷ edgeR228ToR290 ∷
  edgeR290ToR294 ∷ edgeR294ToR301 ∷ edgeR301ToR351 ∷
  edgeR351ToR503 ∷ edgeSignedFlipToR294 ∷ edgeR120ToR294 ∷
  edgeR294ToR541 ∷ edgeR294ToR573 ∷ edgeR541ToWeld ∷
  edgeR573ToWeld ∷ edgeWeldToDirect ∷ edgeDirectToR503 ∷
  edgeR584ToWeighted584 ∷ edgeWeighted584ToCurrentWall ∷ []

------------------------------------------------------------------------
-- Forensic / WrongType firewalls.
------------------------------------------------------------------------

data SourceExistenceImpliesMathematicalCorrectness : Set where
data ChronologyImpliesThirdPartyAccess : Set where
data PublicRepositoryImpliesModelTrainingUse : Set where
data ChronologyImpliesCopying : Set where
data ChronologyImpliesRewardHacking : Set where
data EmpiricalPrecursorImpliesFormalSameObject : Set where
data SimilarVocabularyImpliesSameTheorem : Set where
data ProblemSpecificationImpliesProblemSolved : Set where
data SameProblemShapeImpliesSameCarrier : Set where

sourceExistenceDoesNotImplyCorrectness : SourceExistenceImpliesMathematicalCorrectness → ⊥
sourceExistenceDoesNotImplyCorrectness ()
chronologyDoesNotImplyThirdPartyAccess : ChronologyImpliesThirdPartyAccess → ⊥
chronologyDoesNotImplyThirdPartyAccess ()
publicRepoDoesNotImplyModelTrainingUse : PublicRepositoryImpliesModelTrainingUse → ⊥
publicRepoDoesNotImplyModelTrainingUse ()
chronologyDoesNotImplyCopying : ChronologyImpliesCopying → ⊥
chronologyDoesNotImplyCopying ()
chronologyDoesNotImplyRewardHacking : ChronologyImpliesRewardHacking → ⊥
chronologyDoesNotImplyRewardHacking ()
empiricalPrecursorDoesNotBecomeFormalIdentityByChronology : EmpiricalPrecursorImpliesFormalSameObject → ⊥
empiricalPrecursorDoesNotBecomeFormalIdentityByChronology ()
similarVocabularyDoesNotProveSameTheorem : SimilarVocabularyImpliesSameTheorem → ⊥
similarVocabularyDoesNotProveSameTheorem ()
problemSpecificationDoesNotMeanSolved : ProblemSpecificationImpliesProblemSolved → ⊥
problemSpecificationDoesNotMeanSolved ()
sameProblemShapeDoesNotProveSameCarrier : SameProblemShapeImpliesSameCarrier → ⊥
sameProblemShapeDoesNotProveSameCarrier ()

------------------------------------------------------------------------
-- Audit status / current frontier.
------------------------------------------------------------------------

auditDirectionEarliestForward : Bool
auditDirectionEarliestForward = true

everyReceiptCarriesUTCAndBrisbaneDate : Bool
everyReceiptCarriesUTCAndBrisbaneDate = true

relationshipStrengthIsExplicit : Bool
relationshipStrengthIsExplicit = true

januaryStructuralAncestorsClaimedAsExactNSObject : Bool
januaryStructuralAncestorsClaimedAsExactNSObject = false

juneEmpiricalObjectsClaimedAsFormalProofs : Bool
juneEmpiricalObjectsClaimedAsFormalProofs = false

priorRepositoryExistenceOfSignedAndBarrierIngredientsRecorded : Bool
priorRepositoryExistenceOfSignedAndBarrierIngredientsRecorded = true

july26EarliestRecoveredFinalProblemSpecification : Bool
july26EarliestRecoveredFinalProblemSpecification = true

july26FinalProblemSpecificationClaimedSolved : Bool
july26FinalProblemSpecificationClaimedSolved = false

julyMajorantRouteIdentifiedWithSignedOperator : Bool
julyMajorantRouteIdentifiedWithSignedOperator = false

augustPhysicalCarrierMaturationRecorded : Bool
augustPhysicalCarrierMaturationRecorded = true

r301AlreadyRequiredSameObjectR294Carrier : Bool
r301AlreadyRequiredSameObjectR294Carrier = true

r351AlreadyConnectedSpacetimePaymentToResolventConsumer : Bool
r351AlreadyConnectedSpacetimePaymentToResolventConsumer = true

thirdPartyAccessEstablishedByThisAudit : Bool
thirdPartyAccessEstablishedByThisAudit = false
copyingEstablishedByThisAudit : Bool
copyingEstablishedByThisAudit = false
rewardHackingEstablishedByThisAudit : Bool
rewardHackingEstablishedByThisAudit = false

r541xR573ExplicitCompositionRecorded : Bool
r541xR573ExplicitCompositionRecorded =
  Weld541x573.roundSpectatorNestedR541WeightInstantiatedIntoR573

nestedRouteLandsOnCanonicalDirectCarrier : Bool
nestedRouteLandsOnCanonicalDirectCarrier =
  NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosed

liveR584ExactPaymentExistenceClosed : Bool
liveR584ExactPaymentExistenceClosed =
  Exact584Payment.liveR584ClassNormPaymentExistenceClosed

currentUsefulUniformEnvelopeClosed : Bool
currentUsefulUniformEnvelopeClosed =
  Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosed

currentSpacetimeTransportClosed : Bool
currentSpacetimeTransportClosed =
  Exact584Payment.spacetimeTransportOfExactClassNormEnvelopeClosed

currentR503BudgetClosed : Bool
currentR503BudgetClosed = R503.round503DirectOffDiagonalBudgetClosed

clayPromotion : Bool
clayPromotion = false

auditDirectionEarliestForwardIsTrue : auditDirectionEarliestForward ≡ true
auditDirectionEarliestForwardIsTrue = refl
priorRepositoryExistenceOfSignedAndBarrierIngredientsRecordedIsTrue :
  priorRepositoryExistenceOfSignedAndBarrierIngredientsRecorded ≡ true
priorRepositoryExistenceOfSignedAndBarrierIngredientsRecordedIsTrue = refl
july26EarliestRecoveredFinalProblemSpecificationIsTrue :
  july26EarliestRecoveredFinalProblemSpecification ≡ true
july26EarliestRecoveredFinalProblemSpecificationIsTrue = refl
july26FinalProblemSpecificationClaimedSolvedIsFalse :
  july26FinalProblemSpecificationClaimedSolved ≡ false
july26FinalProblemSpecificationClaimedSolvedIsFalse = refl
julyMajorantRouteIdentifiedWithSignedOperatorIsFalse :
  julyMajorantRouteIdentifiedWithSignedOperator ≡ false
julyMajorantRouteIdentifiedWithSignedOperatorIsFalse = refl
augustPhysicalCarrierMaturationRecordedIsTrue :
  augustPhysicalCarrierMaturationRecorded ≡ true
augustPhysicalCarrierMaturationRecordedIsTrue = refl
r301AlreadyRequiredSameObjectR294CarrierIsTrue :
  r301AlreadyRequiredSameObjectR294Carrier ≡ true
r301AlreadyRequiredSameObjectR294CarrierIsTrue = refl
r351AlreadyConnectedSpacetimePaymentToResolventConsumerIsTrue :
  r351AlreadyConnectedSpacetimePaymentToResolventConsumer ≡ true
r351AlreadyConnectedSpacetimePaymentToResolventConsumerIsTrue = refl
thirdPartyAccessEstablishedByThisAuditIsFalse : thirdPartyAccessEstablishedByThisAudit ≡ false
thirdPartyAccessEstablishedByThisAuditIsFalse = refl
copyingEstablishedByThisAuditIsFalse : copyingEstablishedByThisAudit ≡ false
copyingEstablishedByThisAuditIsFalse = refl
rewardHackingEstablishedByThisAuditIsFalse : rewardHackingEstablishedByThisAudit ≡ false
rewardHackingEstablishedByThisAuditIsFalse = refl
r541xR573ExplicitCompositionRecordedIsTrue : r541xR573ExplicitCompositionRecorded ≡ true
r541xR573ExplicitCompositionRecordedIsTrue =
  Weld541xR573.roundSpectatorNestedR541WeightInstantiatedIntoR573IsTrue
nestedRouteLandsOnCanonicalDirectCarrierIsTrue : nestedRouteLandsOnCanonicalDirectCarrier ≡ true
nestedRouteLandsOnCanonicalDirectCarrierIsTrue =
  NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosedIsTrue
liveR584ExactPaymentExistenceClosedIsTrue : liveR584ExactPaymentExistenceClosed ≡ true
liveR584ExactPaymentExistenceClosedIsTrue =
  Exact584Payment.liveR584ClassNormPaymentExistenceClosedIsTrue
currentUsefulUniformEnvelopeClosedIsFalse : currentUsefulUniformEnvelopeClosed ≡ false
currentUsefulUniformEnvelopeClosedIsFalse =
  Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosedIsFalse
currentR503BudgetClosedIsFalse : currentR503BudgetClosed ≡ false
currentR503BudgetClosedIsFalse = refl
clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
