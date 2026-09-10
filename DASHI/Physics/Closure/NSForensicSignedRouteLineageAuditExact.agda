module DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact where

------------------------------------------------------------------------
-- NS SIGNED-ROUTE FORENSIC LINEAGE: EARLIEST -> FORWARD
--
-- Chronology proves repository existence/provenance only.  It does not prove
-- correctness, external access, copying, training ingestion, reward hacking,
-- or same-object identity unless an exact formal edge below says so.
--
-- Current historical result:
--   2026-07-26 is the earliest RECOVERED point at which the repository had
--   all principal coordinates of the later final problem simultaneously:
--
--     exact signed physical coefficient
--       + cancellation-aware signed-gap route
--       + cutoff-uniform quantitative target
--       + dissipation comparator
--       + arbitrary-data/global consumer.
--
-- This is a problem-specification/architecture claim, NOT a solved-theorem
-- claim. Later tranches progressively strengthen the carrier and composition.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

-- Historical owners needed to make the forward path explicit.
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

-- Current formal descendants.
import DASHI.Physics.Closure.NSTriadKNExternalPureCommutatorPartnerRound120Exact as R120
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairCompanionRound496Exact as R496
import DASHI.Physics.Closure.NSTriadKNDirectResolventSignedCrossToR415Round503Exact as R503
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventR294WeightRound541Exact as R541
import DASHI.Physics.Closure.NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact as R573
import DASHI.Physics.Closure.NSTriadKNNestedSlotBonyClassNormBidiRound584Exact as R584
import DASHI.Physics.Closure.NSTriadKNSpectatorResolventNestedCommutatorBidiExact as Weld541x573
import DASHI.Physics.Closure.NSTriadKNNestedFactoredFullToDirectFibreBidiExact as NestedFibre
import DASHI.Physics.Closure.NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact as Exact584Payment

data Repository : Set where dashiCFD dashiAgda : Repository

data ArtefactRole : Set where
  structuralAncestor signedCoherencePrecursor empiricalBarrier empiricalSignedResidual : ArtefactRole
  signedMajorantBoundary canonicalResolventBaseline analyticTrancheAssembly : ArtefactRole
  exactSignedCoefficient signedUniformGapSpecification globalAprioriConsumer : ArtefactRole
  physicalSignedAssembly criticalCommutatorDissipation signedPhysicalShellLedger : ArtefactRole
  formalCommutator exactCarrierBonyWeld spacetimeFrontier resolventTemporalFlux : ArtefactRole
  formalWeightedCancellation sameObjectSchurFrontier resolventAbsorptionAdapter : ArtefactRole
  liveSignedCarrier directResolventRepresentation terminalSignedConsumer : ArtefactRole
  spectatorResolventWeight nestedSignedRepresentation liveNestedClassNormCarrier : ArtefactRole
  compositionWeld exactClassPaymentCompiler survivingAnalyticBoundary : ArtefactRole

data RelationshipStrength : Set where
  broadStructuralAncestry empiricalMethodPrecursor representationBoundary : RelationshipStrength
  architectureAssembly problemSpecification physicalInstantiation formalRefinement : RelationshipStrength
  exactSameObject exactSpecialization compositionInput canonicalConsumer analyticFrontier : RelationshipStrength

record ForensicReceipt : Set where
  constructor forensic-receipt
  field
    repository : Repository
    artefact path firstCommit firstImplementedUTC firstImplementedBrisbane author : String
    role : ArtefactRole
    forensicRelationship : String
open ForensicReceipt public

record SnowballEdge : Set where
  constructor snowball-edge
  field
    fromArtefact toArtefact : String
    strength : RelationshipStrength
    rationale : String
    exactSameCarrierProved : Bool
open SnowballEdge public

R : Repository → String → String → String → String → String → ArtefactRole → String → ForensicReceipt
R repo name p sha utc brisbane role relation =
  forensic-receipt repo name p sha utc brisbane "Johl Brown" role relation

------------------------------------------------------------------------
-- DATED RECEIPTS
------------------------------------------------------------------------

jan24StructuralCarrier = R dashiCFD
  "initial signed/ternary CFD structural carrier"
  "COMPACTIFIED_CONTEXT.md; dashi_les_vorticity_codec_v2.py; dashi_signed_branchedflow_codec.npz"
  "1cb1bb612c4061676a06e615f69bf282462c25cc"
  "2026-01-24T09:06:14Z" "2026-01-24T19:06:14+10:00" structuralAncestor
  "signed anomaly -> ternary state -> support -> residual; methodological ancestor only"

jan27SignedFilament = R dashiCFD
  "signed filament annihilation / coherence note" "docs/signed_filament_annihilation.md"
  "7938f8282541b142e93cb2a7dadf32d83ca553b3"
  "2026-01-27T14:33:22Z" "2026-01-28T00:33:22+10:00" signedCoherencePrecursor
  "F_k=sigma_k*s_k; support/sign separated; coarse-graining must not create support"

jun03ThetaBarrier = R dashiCFD
  "NS theta flux/dissipation sweep" "scripts/ns_theta_full_sweep.py"
  "125e52e04bed4042890d95db5d5371104ba1aafe"
  "2026-06-03T14:15:39Z" "2026-06-04T00:15:39+10:00" empiricalBarrier
  "empirical |Flux|/Diss high-frequency barrier; early absolute-value loss retained as historical fact"

jun04SignedFlip = R dashiCFD
  "signed ternary cross-shell flip audit" "scripts/ns_signed_ternary_flip_audit.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z" "2026-06-04T14:13:12+10:00" empiricalSignedResidual
  "signed +/- cross-shell imbalance/net residue is formed before magnitude diagnostics"

jun04MaterialParent = R dashiCFD
  "material-parent cross-shell provenance carrier"
  "scripts/ns_material_parent_summary.py; scripts/ns_ternary_cross_shell_matrix.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z" "2026-06-04T14:13:12+10:00" empiricalSignedResidual
  "material-parent/cross-shell carrier consumed by the signed-flip audit"

jul20CanonicalResolvent = R dashiAgda
  "canonical finite resolvent / strict gap baseline" "DASHI/Physics/Closure/NSWall1CanonicalResolventGap.agda"
  "d10569457f09993174e1b921935dadb1eebced05"
  "2026-07-20T01:43:20Z" "2026-07-20T11:43:20+10:00" canonicalResolventBaseline
  "resolvent/gap coordinate exists; six-mode baseline explicitly not the physical low block without representation"

jul20MajorantSeparation = R dashiAgda
  "signed response separated from pair-majorant kernel"
  "DASHI/Physics/Closure/NSCompactGammaOffPacketPairIncidenceKernelBridge.agda"
  "723bf33bd9bf1947eb5bbda6dd3df700b5b05e39"
  "2026-07-20T01:57:40Z" "2026-07-20T11:57:40+10:00" signedMajorantBoundary
  "signed near response <= nonnegative majorant action; pair-majorant cannot reproduce signed response entrywise"

jul20PR145 = R dashiAgda
  "PR #145 rational six-mode Wall1 Schur/resolvent/gap packet" "pull/145"
  "8905dc5c4c3389f18698f1669040dcf5923af0c6"
  "2026-07-20T03:02:06Z" "2026-07-20T13:02:06+10:00" analyticTrancheAssembly
  "finite Schur certificates + low resolvent + strict packet gap; physical representation remains guarded"

jul20PR140 = R dashiAgda
  "PR #140 compact-Gamma signed-response/Schur/tail architecture" "pull/140"
  "e64a38ab617cf88035555a07a223afe46480df0e"
  "2026-07-20T06:17:05Z" "2026-07-20T16:17:05+10:00" analyticTrancheAssembly
  "signed near response + pair-incidence majorant + Schur target + far tail + D-log-E consumer assembled"

jul20PR227 = R dashiAgda
  "PR #227 cross-pollinated compact-Gamma closure stack" "pull/227"
  "c2b313a0878b0281781dd7a1bf3ae851d24af8d9"
  "2026-07-20T09:42:15Z" "2026-07-20T19:42:15+10:00" analyticTrancheAssembly
  "differentiated triads + full-shell pair incidence + tail + Galerkin passage + invariant region + BKM"

jul20PR255 = R dashiAgda
  "PR #255 concrete far-tail commutator decay" "pull/255"
  "bc9a627985cf4140ee10260f6399050aacf5cba4"
  "2026-07-20T15:09:40Z" "2026-07-21T01:09:40+10:00" analyticTrancheAssembly
  "far-low cancellation/commutator gain + far-high Sobolev tail + cutoff-uniform epsilon(R) endpoint"

jul25PR336 = R dashiAgda
  "PR #336 exact signed multiplier-difference commutator frontier" "pull/336"
  "68ab8ffbcf5c0aa791720a454dbeb1631ea933b2"
  "2026-07-25T07:09:05Z" "2026-07-25T17:09:05+10:00" signedMajorantBoundary
  "K_raw, signed K_diff, and K_absdiff separated; exact commutator identity before norm; absolute Schur empirically poor"

jul26ExactSignedCoefficient = R dashiAgda
  "exact signed velocity-form Galerkin coefficient" "DASHI/Physics/Closure/NSTriadKNExactSignedGalerkinCoefficient.agda"
  "466c9cdea3336fb3b0c727ee21900d008d90a00d"
  "2026-07-26T02:44:07Z" "2026-07-26T12:44:07+10:00" exactSignedCoefficient
  "literal -i P_k[(u_p.q)u_q]; no positive part, absolute value, phase ansatz, or hidden half"

jul26PhysicalMajorantBridge = R dashiAgda
  "exact signed coefficient -> retained physical triads + named majorant"
  "DASHI/Physics/Closure/NSTriadKNExactCoefficientToPhysicalWeight.agda"
  "a4f38a003e74cfb31d8dc452a0e1eb7c6fc565ca"
  "2026-07-26T02:46:25Z" "2026-07-26T12:46:25+10:00" physicalSignedAssembly
  "raw physical coefficient remains signed; Nat kernel is explicitly coefficientMajorant(raw coefficient)"

jul26PhysicalStage3 = R dashiAgda
  "signed physical Stage-3 frontier aggregate" "DASHI/Physics/Closure/NSTriadKNPhysicalTriadFrontierProgram.agda"
  "5e1ae9dc413a9447bfa515a784bdeb08dab53f2e"
  "2026-07-26T02:51:51Z" "2026-07-26T12:51:51+10:00" physicalSignedAssembly
  "signed coefficient + positive-part no-go + physical fibres + class envelopes + finite/uniform no-go + global cutset"

jul26SignedGapProgram = R dashiAgda
  "signed cutoff-uniform gap program" "DASHI/Physics/Closure/NSTriadKNSignedUniformGapProgram.agda"
  "e8d8781781f825f3b27fbf578887d6e619bf5953"
  "2026-07-26T03:25:40Z" "2026-07-26T13:25:40+10:00" signedUniformGapSpecification
  "Route B preserves signed blocks; asks permutation/reality-orbit/complete-triad cancellation + uniform numerical range"

jul26GapApriori = R dashiAgda
  "strict signed gap -> arbitrary-data uniform a-priori composition"
  "DASHI/Physics/Closure/NSTriadKNSignedGapAprioriComposition.agda"
  "a872ad2a4249e2d6f1056595df980000fe7472aa"
  "2026-07-26T04:17:22Z" "2026-07-26T14:17:22+10:00" globalAprioriConsumer
  "signed Nonlinear<=Dissipation + energy identity -> cutoff-independent arbitrary-data a-priori control"

aug05CriticalDissipation = R dashiAgda
  "commutator criticality + terminal dissipation" "DASHI/Physics/Closure/NSTriadKNLuoNearWindowCommutatorDissipationClosureExact.agda"
  "8d5c3436b6fde86719b54d323113a69360adbc2d"
  "2026-08-05T11:13:30Z" "2026-08-05T21:13:30+10:00" criticalCommutatorDissipation
  "critical commutator factor composed with independently owned terminal dissipation smallness; PDE estimate remains leaf"

aug08SignedShell = R dashiAgda
  "physical five-source fibre -> signed critical shell cell" "DASHI/Physics/Closure/NSTriadKNLuoPhysicalSignedShellCellRound26Exact.agda"
  "19aa8cb1d7b373fdf74ac0674832477a94d98f5a"
  "2026-08-08T06:50:21Z" "2026-08-08T16:50:21+10:00" signedPhysicalShellLedger
  "HH+LH+HL+CC+Com forced by literal output fibre and genuine shell energy balance"

aug27R120 = R dashiAgda
  "R120 physical shared-output pure commutator partner" "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorPartnerRound120Exact.agda"
  "7ba2a203e355f4cbb2b4888f6ae408f4c17ef58b"
  "2026-08-27T13:51:37Z" "2026-08-27T23:51:37+10:00" formalCommutator
  "formal physical commutator identity; no retroactive identity with empirical/July objects"

aug27R123 = R dashiAgda
  "R123 physical quartic -> signed pure-commutator Bony folds" "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorBonyWeldRound123Exact.agda"
  "1ccc381d7d2b71e6add0110d1575a8d35242496c"
  "2026-08-27T14:06:10Z" "2026-08-28T00:06:10+10:00" exactCarrierBonyWeld
  "2*full physical quartic fold = four signed Bony commutator folds; no cellwise abs/cardinality tax"

aug29R228 = R dashiAgda
  "R228 mixed-helicity spacetime Package-A leaf" "DASHI/Physics/Closure/NSTriadKNMixedHelicitySpacetimeFrontierRound228Exact.agda"
  "2b18f2f747863c67a9274463891774a4170d8fa0"
  "2026-08-29T13:01:57Z" "2026-08-29T23:01:57+10:00" spacetimeFrontier
  "one remaining PDE theorem named: cutoff-uniform spacetime bound for physical mixed-helicity convolution mass"

aug30R290 = R dashiAgda
  "R290 resolvent-weighted temporal Gram flux" "DASHI/Physics/Closure/NSTriadKNWeightedGramFluxCompilerRound290Exact.agda"
  "9bc61ac8e9b046c7bcb781fb5badba5654d1acf0"
  "2026-08-30T11:08:41Z" "2026-08-30T21:08:41+10:00" resolventTemporalFlux
  "w*lambda=1 turns Gram debt into endpoint flux + weighted nonlinear remainder"

aug30R294 = R dashiAgda
  "R294 swap-invariant weighted commutator" "DASHI/Physics/Closure/NSTriadKNResolventWeightedMixedCommutatorRound294Exact.agda"
  "64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "2026-08-30T11:19:48Z" "2026-08-30T21:19:48+10:00" formalWeightedCancellation
  "generic swap-invariant weight preserves mixed-commutator cancellation before absolute values"

aug31R301 = R dashiAgda
  "R301 same-object heat-weighted R294 spacetime/Schur frontier" "DASHI/Physics/Closure/NSTriadKNHeatWeightedCommutatorSchurRound301Exact.agda"
  "489f48fac67b7effe1ffd6200c7f614ff4d60a0d"
  "2026-08-31T10:04:17Z" "2026-08-31T20:04:17+10:00" sameObjectSchurFrontier
  "requires literal R294 carrier; row/column budgets + spacetime integrability are explicit leaves"

aug31R351 = R dashiAgda
  "R351 spacetime payment -> existing resolvent absorption consumer" "DASHI/Physics/Closure/NSTriadKNHeatWeightedNestedSpacetimeToResolventRound351Exact.agda"
  "523909ea07409de82e225153572bfbc8f91b7e35"
  "2026-08-31T14:58:10Z" "2026-09-01T00:58:10+10:00" resolventAbsorptionAdapter
  "R301 payment inhabits existing R300 resolvent absorption leaf by monotonicity only"

sep01R406 = R dashiAgda
  "R406 fixed-output live global flux" "DASHI/Physics/Closure/NSTriadKNFixedOutputLiveGlobalFluxRound406Exact.agda"
  "341747bff0c977aadc89f8f55b05225b1c9ce15c"
  "2026-09-01T05:21:27Z" "2026-09-01T15:21:27+10:00" liveSignedCarrier
  "live R378/R406 flux on fixed canonical output list"

sep07R496 = R dashiAgda
  "R496 direct nonseparable resolvent pair companion" "DASHI/Physics/Closure/NSTriadKNDirectResolventPairCompanionRound496Exact.agda"
  "9be2933f265e95ccc9f2dca5204b21bc528fc393"
  "2026-09-07T18:53:49Z" "2026-09-08T04:53:49+10:00" directResolventRepresentation
  "literal weighted remainder represented by canonical direct Cauchy-resolvent pair companion"

sep07R503 = R dashiAgda
  "R503 signed direct-resolvent terminal consumer" "DASHI/Physics/Closure/NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda"
  "984eaa83d988b0292ead61cfef8e9db463cbb425"
  "2026-09-07T19:02:43Z" "2026-09-08T05:02:43+10:00" terminalSignedConsumer
  "preserves sign; asks cutoff-uniform one-sided direct-companion bound"

sep09R541 = R dashiAgda
  "R541 spectator Cauchy resolvent as R294 weight" "DASHI/Physics/Closure/NSTriadKNSpectatorResolventR294WeightRound541Exact.agda"
  "350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "2026-09-09T04:56:22Z" "2026-09-09T14:56:22+10:00" spectatorResolventWeight
  "fixed beta makes literal Cauchy pair kernel an exact R294 swap-invariant weight in alpha"

sep09R573 = R dashiAgda
  "R573 weighted nested four-sign commutator" "DASHI/Physics/Closure/NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact.agda"
  "8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "2026-09-09T09:17:38Z" "2026-09-09T19:17:38+10:00" nestedSignedRepresentation
  "actual weighted outer commutator = nested four-sign inner carrier before norms"

sep09R584 = R dashiAgda
  "R584 live nested-slot Bony class-norm carrier" "DASHI/Physics/Closure/NSTriadKNNestedSlotBonyClassNormBidiRound584Exact.agda"
  "b42b6510c4025d835192d1d84d188ed87426abc9"
  "2026-09-09T14:49:15Z" "2026-09-10T00:49:15+10:00" liveNestedClassNormCarrier
  "class norms on actual R573 slot-transformed cells; outer weight/spacetime initially open"

sep10R541xR573 = R dashiAgda
  "explicit R541 x R573 spectator-resolvent nested composition" "DASHI/Physics/Closure/NSTriadKNSpectatorResolventNestedCommutatorBidiExact.agda"
  "b06ec702a45c595449c044a19ad14d5b37327ace"
  "2026-09-10T05:01:10Z" "2026-09-10T15:01:10+10:00" compositionWeld
  "R573 instantiated by R541.spectatorWeight beta before norm/abs/Schur/Laplace"

sep10NestedFibre = R dashiAgda
  "nested factored-full -> canonical direct fibre" "DASHI/Physics/Closure/NSTriadKNNestedFactoredFullToDirectFibreBidiExact.agda"
  "68767078ec9158752189af8273192f1c227e97fc"
  "2026-09-10T06:05:32Z" "2026-09-10T16:05:32+10:00" compositionWeld
  "nested factored-full lands on diagonal + 2*(4*R497 direct fibre) without erasing diagonal"

sep10Exact584Payments = R dashiAgda
  "exact class payments on live spectator R584 carrier" "DASHI/Physics/Closure/NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact.agda"
  "ac898d515c3e9f2882c3b2102eaa5fc75fa2a2c3"
  "2026-09-10T06:20:48Z" "2026-09-10T16:20:48+10:00" exactClassPaymentCompiler
  "mere class-budget existence closed; useful uniform envelope/spacetime transport remain open"

forensicChronology : List ForensicReceipt
forensicChronology =
  jan24StructuralCarrier ∷ jan27SignedFilament ∷ jun03ThetaBarrier ∷ jun04SignedFlip ∷
  jun04MaterialParent ∷ jul20CanonicalResolvent ∷ jul20MajorantSeparation ∷ jul20PR145 ∷
  jul20PR140 ∷ jul20PR227 ∷ jul20PR255 ∷ jul25PR336 ∷ jul26ExactSignedCoefficient ∷
  jul26PhysicalMajorantBridge ∷ jul26PhysicalStage3 ∷ jul26SignedGapProgram ∷
  jul26GapApriori ∷ aug05CriticalDissipation ∷ aug08SignedShell ∷ aug27R120 ∷
  aug27R123 ∷ aug29R228 ∷ aug30R290 ∷ aug30R294 ∷ aug31R301 ∷ aug31R351 ∷
  sep01R406 ∷ sep07R496 ∷ sep07R503 ∷ sep09R541 ∷ sep09R573 ∷ sep09R584 ∷
  sep10R541xR573 ∷ sep10NestedFibre ∷ sep10Exact584Payments ∷ []

------------------------------------------------------------------------
-- ATTRIBUTION ATLAS
------------------------------------------------------------------------

repoSource : String → String → String → String → Source.AttributedSource
repoSource title context url relationship = Source.mkNoDOISource
  "Johl Brown" title context "2026" url
  (Source.namedSourceKind "GitHub repository source/commit/PR") relationship Source.publicAttribution

januarySource = repoSource "dashiCFD signed structural origin"
  "commits 1cb1bb... and 7938f828..." "https://github.com/chboishabba/dashiCFD"
  "structural/signed-coherence provenance only"
juneSource = repoSource "dashiCFD NS theta + signed cross-shell experiments"
  "commits 125e52e... and 1c9ca183..." "https://github.com/chboishabba/dashiCFD"
  "empirical barrier/cancellation precursors only"
julySource = repoSource "July signed-response, resolvent, exact coefficient and uniform-gap tranches"
  "dashi_agda 2026-07-20 through 2026-07-26" "https://github.com/chboishabba/dashi_agda"
  "architecture and earliest recovered final-problem specification; no solved-theorem promotion"
augustSource = repoSource "August physical signed carrier -> resolvent/spacetime path"
  "dashi_agda 2026-08-05 through 2026-08-31" "https://github.com/chboishabba/dashi_agda"
  "physical instantiation and same-object analytic-frontier maturation"
septemberSource = repoSource "September direct-resolvent/nested same-object composition"
  "dashi_agda 2026-09-01 through 2026-09-10" "https://github.com/chboishabba/dashi_agda"
  "later exact specialization/composition on canonical direct consumer"

forensicSourceAtlas : Source.AttributedSourceAtlas
forensicSourceAtlas = Source.mkSourceAtlas
  "NS signed-route earliest-forward forensic source atlas"
  "DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact"
  (januarySource ∷ juneSource ∷ julySource ∷ augustSource ∷ septemberSource ∷ [])
  "repository chronology and formalisation relationships; citation imports neither correctness nor external influence"

------------------------------------------------------------------------
-- FORWARD SNOWBALL EDGES
------------------------------------------------------------------------

E : String → String → RelationshipStrength → String → Bool → SnowballEdge
E = snowball-edge

edgeJanToJune = E "Jan signed/support carrier" "June signed-transfer + theta experiments"
  empiricalMethodPrecursor "structural sign/support semantics becomes empirical cross-shell cancellation/barrier work" false
edgeJuneToJulyBoundary = E "June signed-transfer/barrier" "Jul-20 signed response vs majorant boundary"
  representationBoundary "formal lane records that nonnegative majorant is not the signed operator" false
edgeJulyArchitecture = E "Jul-20 resolvent/Schur/tail/Galerkin tranches" "Jul-26 signed physical problem specification"
  architectureAssembly "global closure architecture is combined with exact signed physical operator and signed-uniform-gap target" false
edgeJulyFinalProblem = E "Jul-26 exact signed physical coefficient" "Jul-26 signed uniform gap -> global a-priori consumer"
  problemSpecification "exact signed operator + cancellation + cutoff uniformity + dissipation + arbitrary-data consumer all simultaneously named" false
edgeJulyToAugShell = E "Jul-26 signed physical Stage3" "Aug-08 signed physical shell ledger"
  physicalInstantiation "abstract signed physical target lands on genuine HH/LH/HL/CC/Com energy balance" true
edgeAugShellToR123 = E "Aug-08 physical signed shell" "Aug-27 R123 physical signed Bony commutator"
  formalRefinement "carrier becomes exact quartic-to-signed-commutator Bony equality before abs" false
edgeR123ToR228 = E "R123 signed Bony carrier" "R228 one remaining spacetime theorem"
  formalRefinement "helicity cancellation reduces physical Package A to cutoff-uniform spacetime mass" false
edgeR228ToR290 = E "R228 spacetime mass" "R290 resolvent-weighted temporal flux"
  formalRefinement "viscous pair resolvent moves coherent Gram debt to endpoint + weighted remainder" false
edgeR290ToR294 = E "R290 weighted nonlinear remainder" "R294 weighted mixed commutator"
  formalRefinement "weighted remainder gains exact swap-cancellation carrier" false
edgeR294ToR301 = E "R294 literal weighted commutator" "R301 same-object Schur/spacetime payment"
  canonicalConsumer "R301 explicitly requires literal R294 carrier and rejects proxy carriers" true
edgeR301ToR351 = E "R301 spacetime payment" "R351 existing resolvent absorption consumer"
  canonicalConsumer "payment plugs into existing R300 consumer by monotonicity; no new consumer architecture" true
edgeR351ToR503 = E "R351 signed-resolvent spacetime path" "R503 direct signed-resolvent terminal consumer"
  formalRefinement "later rounds re-express same overall obligation on more literal direct companion carrier" false
edgeR120ToR294 = E "R120 physical commutator" "R294 swap-invariant weighted commutator"
  formalRefinement "commutator cancellation survives generic swap-invariant weight" true
edgeR294ToR541 = E "R294 generic weight" "R541 literal spectator Cauchy weight"
  exactSpecialization "R541 constructs literal spectator resolvent as R294 weight" true
edgeR294ToR573 = E "R294 weighted commutator" "R573 nested four-sign carrier"
  exactSameObject "R573 proves weighted outer carrier equals nested representation before norms" true
edgeR541R573 = E "R541 + R573" "explicit spectator-resolvent nested weld"
  compositionInput "literal spectator Cauchy weight directly instantiated into nested commutator" true
edgeNestedToDirect = E "nested spectator weld" "R496/R497/R503 canonical direct route"
  exactSameObject "nested scalar path is welded to canonical direct companion consumer" true
edgeR584Frontier = E "R541-weighted live R584 exact class payments" "uniform spectator-weighted class-norm/spacetime envelope"
  analyticFrontier "useful cutoff-uniform quantitative envelope remains theorem-bearing" false

forensicSnowball : List SnowballEdge
forensicSnowball =
  edgeJanToJune ∷ edgeJuneToJulyBoundary ∷ edgeJulyArchitecture ∷ edgeJulyFinalProblem ∷
  edgeJulyToAugShell ∷ edgeAugShellToR123 ∷ edgeR123ToR228 ∷ edgeR228ToR290 ∷
  edgeR290ToR294 ∷ edgeR294ToR301 ∷ edgeR301ToR351 ∷ edgeR351ToR503 ∷
  edgeR120ToR294 ∷ edgeR294ToR541 ∷ edgeR294ToR573 ∷ edgeR541R573 ∷
  edgeNestedToDirect ∷ edgeR584Frontier ∷ []

------------------------------------------------------------------------
-- WRONGTYPE / FORENSIC FIREWALLS
------------------------------------------------------------------------

data SourceExistenceImpliesCorrectness : Set where
data ChronologyImpliesThirdPartyAccess : Set where
data PublicRepoImpliesTrainingUse : Set where
data ChronologyImpliesCopying : Set where
data ChronologyImpliesRewardHacking : Set where
data PrecursorImpliesSameObject : Set where
data ProblemSpecificationImpliesSolved : Set where
data SameProblemShapeImpliesSameCarrier : Set where

noCorrectness : SourceExistenceImpliesCorrectness → ⊥
noCorrectness ()
noThirdPartyAccess : ChronologyImpliesThirdPartyAccess → ⊥
noThirdPartyAccess ()
noTrainingInference : PublicRepoImpliesTrainingUse → ⊥
noTrainingInference ()
noCopyingInference : ChronologyImpliesCopying → ⊥
noCopyingInference ()
noRewardHackingInference : ChronologyImpliesRewardHacking → ⊥
noRewardHackingInference ()
noPrecursorIdentity : PrecursorImpliesSameObject → ⊥
noPrecursorIdentity ()
problemSpecifiedDoesNotMeanSolved : ProblemSpecificationImpliesSolved → ⊥
problemSpecifiedDoesNotMeanSolved ()
sameShapeDoesNotMeanSameCarrier : SameProblemShapeImpliesSameCarrier → ⊥
sameShapeDoesNotMeanSameCarrier ()

------------------------------------------------------------------------
-- AUDIT STATUS
------------------------------------------------------------------------

auditDirectionEarliestForward = true
allReceiptsCarryUTCAndBrisbaneDates = true
july26EarliestRecoveredFinalProblemSpecification = true
july26ProblemClaimedSolved = false
julyMajorantIdentifiedWithSignedOperator = false
augustPhysicalCarrierMaturationRecorded = true
r301AlreadyRequiresSameObjectR294Carrier = true
r351AlreadyConnectsSpacetimePaymentToResolventConsumer = true
thirdPartyAccessEstablished = false
copyingEstablished = false
rewardHackingEstablished = false

r541xR573ExplicitCompositionRecorded : Bool
r541xR573ExplicitCompositionRecorded = Weld541x573.roundSpectatorNestedR541WeightInstantiatedIntoR573
nestedRouteLandsOnCanonicalDirectCarrier : Bool
nestedRouteLandsOnCanonicalDirectCarrier = NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosed
liveR584ExactPaymentExistenceClosed : Bool
liveR584ExactPaymentExistenceClosed = Exact584Payment.liveR584ClassNormPaymentExistenceClosed
currentUsefulUniformEnvelopeClosed : Bool
currentUsefulUniformEnvelopeClosed = Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosed
currentSpacetimeTransportClosed : Bool
currentSpacetimeTransportClosed = Exact584Payment.spacetimeTransportOfExactClassNormEnvelopeClosed
currentR503BudgetClosed : Bool
currentR503BudgetClosed = R503.round503DirectOffDiagonalBudgetClosed
clayPromotion = false

july26EarliestRecoveredFinalProblemSpecificationIsTrue : july26EarliestRecoveredFinalProblemSpecification ≡ true
july26EarliestRecoveredFinalProblemSpecificationIsTrue = refl
july26ProblemClaimedSolvedIsFalse : july26ProblemClaimedSolved ≡ false
july26ProblemClaimedSolvedIsFalse = refl
r541xR573ExplicitCompositionRecordedIsTrue : r541xR573ExplicitCompositionRecorded ≡ true
r541xR573ExplicitCompositionRecordedIsTrue = Weld541x573.roundSpectatorNestedR541WeightInstantiatedIntoR573IsTrue
nestedRouteLandsOnCanonicalDirectCarrierIsTrue : nestedRouteLandsOnCanonicalDirectCarrier ≡ true
nestedRouteLandsOnCanonicalDirectCarrierIsTrue = NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosedIsTrue
liveR584ExactPaymentExistenceClosedIsTrue : liveR584ExactPaymentExistenceClosed ≡ true
liveR584ExactPaymentExistenceClosedIsTrue = Exact584Payment.liveR584ClassNormPaymentExistenceClosedIsTrue
currentUsefulUniformEnvelopeClosedIsFalse : currentUsefulUniformEnvelopeClosed ≡ false
currentUsefulUniformEnvelopeClosedIsFalse = Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosedIsFalse
currentR503BudgetClosedIsFalse : currentR503BudgetClosed ≡ false
currentR503BudgetClosedIsFalse = refl
