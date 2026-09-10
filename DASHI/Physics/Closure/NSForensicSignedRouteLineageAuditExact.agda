module DASHI.Physics.Closure.NSForensicSignedRouteLineageAuditExact where

------------------------------------------------------------------------
-- NAVIER--STOKES SIGNED-ROUTE FORENSIC LINEAGE AUDIT
--
-- Audit direction: EARLIEST RECOVERABLE FORMULATION -> FORWARD SNOWBALL.
--
-- This is a provenance / dependency ledger, not a mathematical promotion
-- mechanism.  It distinguishes broad structural ancestry, empirical precursor
-- work, formal refinement, exact same-object theorems, composition inputs,
-- consumers and surviving analytic boundaries.
--
-- Forensic rule:
--   chronology can establish that an artefact existed in repository source;
--   it cannot by itself establish correctness, publication priority,
--   third-party access, copying, training ingestion, or reward hacking.
--
-- Snowball rule:
--   semantic adjacency is never silently upgraded to exactSameObject.
--   exactSameObject is used only where the formal repository supplies the
--   relevant same-carrier/equality owner.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

-- Import the audited formal descendants so this ONE file is also a transitive
-- source/type surface for the formal part of the lineage.
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
  empiricalBarrier : ArtefactRole
  empiricalSignedResidual : ArtefactRole
  formalCommutator : ArtefactRole
  formalWeightedCancellation : ArtefactRole
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
-- Earliest-first chronology receipts.
------------------------------------------------------------------------

-- Earliest recovered dashiCFD tree.  This is deliberately only a BROAD
-- structural ancestor: ternary sign/support/residual sequencing is present,
-- but this is not retroactively identified with the later NS theorem carrier.
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
  "spectral LES + residual codec; signed anomaly -> ternary state -> support -> residual is a methodological ancestor only"

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
  "empirical high-frequency theta barrier; computes |Flux_{>k}| / Diss_{>k}; promotion explicitly disabled"

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
  "cross-shell minus/plus flow is treated as an involutive signed channel; signed imbalance/net residue precedes absolute-value diagnostics"

jun04MaterialParent : ForensicReceipt
jun04MaterialParent = forensic-receipt
  dashiCFD
  "material-parent cross-shell carrier"
  "scripts/ns_material_parent_summary.py; scripts/ns_ternary_cross_shell_matrix.py"
  "1c9ca183515e3a26988ae21785de9a45481e37d2"
  "2026-06-04T04:13:12Z"
  "2026-06-04T14:13:12+10:00"
  "Johl Brown"
  empiricalSignedResidual
  "material parent/cross-shell provenance carrier consumed by the signed-flip audit"

aug27R120 : ForensicReceipt
aug27R120 = forensic-receipt
  dashiAgda
  "R120 physical shared-output pure commutator partner"
  "DASHI/Physics/Closure/NSTriadKNExternalPureCommutatorPartnerRound120Exact.agda"
  "7ba2a203e355f4cbb2b4888f6ae408f4c17ef58b"
  "2026-08-27T13:51:37Z"
  "2026-08-27T23:51:37+10:00"
  "Johl Brown"
  formalCommutator
  "formal shared-output commutator identity; not identified as the January/June empirical object"

aug30R294 : ForensicReceipt
aug30R294 = forensic-receipt
  dashiAgda
  "R294 swap-invariant weighted commutator collapse"
  "DASHI/Physics/Closure/NSTriadKNResolventWeightedMixedCommutatorRound294Exact.agda"
  "64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "2026-08-30T11:19:48Z"
  "2026-08-30T21:19:48+10:00"
  "Johl Brown"
  formalWeightedCancellation
  "generic swap-invariant weight preserves mixed-commutator cancellation before absolute values"

sep01R406 : ForensicReceipt
sep01R406 = forensic-receipt
  dashiAgda
  "R406 fixed-output live global flux"
  "DASHI/Physics/Closure/NSTriadKNFixedOutputLiveGlobalFluxRound406Exact.agda"
  "341747bff0c977aadc89f8f55b05225b1c9ce15c"
  "2026-09-01T05:21:27Z"
  "2026-09-01T15:21:27+10:00"
  "Johl Brown"
  liveSignedCarrier
  "puts the live flux on a fixed canonical output list"

sep07R496 : ForensicReceipt
sep07R496 = forensic-receipt
  dashiAgda
  "R496 direct nonseparable resolvent pair companion"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventPairCompanionRound496Exact.agda"
  "9be2933f265e95ccc9f2dca5204b21bc528fc393"
  "2026-09-07T18:53:49Z"
  "2026-09-08T04:53:49+10:00"
  "Johl Brown"
  directResolventRepresentation
  "literal R290 weighted remainder is represented on the canonical direct Cauchy-resolvent pair companion"

sep07R503 : ForensicReceipt
sep07R503 = forensic-receipt
  dashiAgda
  "R503 direct off-diagonal signed resolvent budget consumer"
  "DASHI/Physics/Closure/NSTriadKNDirectResolventSignedCrossToR415Round503Exact.agda"
  "984eaa83d988b0292ead61cfef8e9db463cbb425"
  "2026-09-07T19:02:43Z"
  "2026-09-08T05:02:43+10:00"
  "Johl Brown"
  terminalSignedConsumer
  "canonical terminal consumer preserves sign and asks for a cutoff-uniform one-sided direct-companion bound"

sep09R541 : ForensicReceipt
sep09R541 = forensic-receipt
  dashiAgda
  "R541 spectator Cauchy resolvent as R294 weight"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventR294WeightRound541Exact.agda"
  "350a5e27443ee05db7fbbf8359165ef5a10e672d"
  "2026-09-09T04:56:22Z"
  "2026-09-09T14:56:22+10:00"
  "Johl Brown"
  spectatorResolventWeight
  "for fixed beta, the literal nonseparable Cauchy pair kernel becomes an exact swap-invariant R294 weight in alpha"

sep09R573 : ForensicReceipt
sep09R573 = forensic-receipt
  dashiAgda
  "R573 weighted nested four-sign commutator"
  "DASHI/Physics/Closure/NSTriadKNWeightedNestedComponentwiseCommutatorRound573Exact.agda"
  "8c4c2411d3cc292cef93dd6fb307a18b402ff564"
  "2026-09-09T09:17:38Z"
  "2026-09-09T19:17:38+10:00"
  "Johl Brown"
  nestedSignedRepresentation
  "actual R438 weighted outer commutator is represented by the nested four-sign inner carrier before norms"

sep09R584 : ForensicReceipt
sep09R584 = forensic-receipt
  dashiAgda
  "R584 live nested-slot Bony class-norm carrier"
  "DASHI/Physics/Closure/NSTriadKNNestedSlotBonyClassNormBidiRound584Exact.agda"
  "b42b6510c4025d835192d1d84d188ed87426abc9"
  "2026-09-09T14:49:15Z"
  "2026-09-10T00:49:15+10:00"
  "Johl Brown"
  liveNestedClassNormCarrier
  "Bony class norms are attached to the actual R573 slot-transformed cells; outer weight/spacetime remained open at first implementation"

sep10R541xR573 : ForensicReceipt
sep10R541xR573 = forensic-receipt
  dashiAgda
  "first explicit R541 x R573 spectator-resolvent nested composition"
  "DASHI/Physics/Closure/NSTriadKNSpectatorResolventNestedCommutatorBidiExact.agda"
  "b06ec702a45c595449c044a19ad14d5b37327ace"
  "2026-09-10T05:01:10Z"
  "2026-09-10T15:01:10+10:00"
  "Johl Brown"
  compositionWeld
  "instantiates R573 directly with R541.spectatorWeight beta; no norm, absolute value, Schur/Cotlar or Laplace step"

sep10NestedRow : ForensicReceipt
sep10NestedRow = forensic-receipt
  dashiAgda
  "spectator force row through nested signed fold"
  "DASHI/Physics/Closure/NSTriadKNSpectatorNestedRowFactorizationBidiExact.agda"
  "739db0214023c5c6150022af27c2f40d0ccf2c3a"
  "2026-09-10T05:58:00Z"
  "2026-09-10T15:58:00+10:00"
  "Johl Brown"
  compositionWeld
  "rewrites the force half of the R545 spectator row onto the R573 nested signed fold before norm/absolute value"

sep10DirectRow : ForensicReceipt
sep10DirectRow = forensic-receipt
  dashiAgda
  "direct companion to nested spectator row"
  "DASHI/Physics/Closure/NSTriadKNDirectCompanionSpectatorNestedRowBidiExact.agda"
  "f8318253e070dd4400756be36e465f04f9cb68c3"
  "2026-09-10T06:02:34Z"
  "2026-09-10T16:02:34+10:00"
  "Johl Brown"
  compositionWeld
  "same spectator pair scalar is four times the canonical R496 direct companion, lifted over finite rows"

sep10NestedFibre : ForensicReceipt
sep10NestedFibre = forensic-receipt
  dashiAgda
  "nested factored-full to canonical direct fibre"
  "DASHI/Physics/Closure/NSTriadKNNestedFactoredFullToDirectFibreBidiExact.agda"
  "68767078ec9158752189af8273192f1c227e97fc"
  "2026-09-10T06:05:32Z"
  "2026-09-10T16:05:32+10:00"
  "Johl Brown"
  compositionWeld
  "lands nested factored-full on diagonal + 2*(4*R497 direct fibre companion) without erasing the diagonal"

sep10Weighted584 : ForensicReceipt
sep10Weighted584 = forensic-receipt
  dashiAgda
  "R541 spectator weight instantiated into live R584 class norms"
  "DASHI/Physics/Closure/NSTriadKNSpectatorWeightedNestedBonyClassNormBidiExact.agda"
  "6bdbb7df8cd0e65d7d0f782b016bd928ede07b15"
  "2026-09-10T06:16:58Z"
  "2026-09-10T16:16:58+10:00"
  "Johl Brown"
  compositionWeld
  "removes abstract-outer-weight debt by specializing R584 to the literal R541 spectator resolvent"

sep10ExactClassBudgets : ForensicReceipt
sep10ExactClassBudgets = forensic-receipt
  dashiAgda
  "exact R582/R583 class-norm self budgets"
  "DASHI/Physics/Closure/NSTriadKNExactBonyClassNormSelfBudgetBidiExact.agda"
  "d53ad93f79f625e0677b9ce2b92ce473ea55eeff"
  "2026-09-10T06:20:22Z"
  "2026-09-10T16:20:22+10:00"
  "Johl Brown"
  exactClassPaymentCompiler
  "closes mere existence of class-norm budgets by choosing exact norms themselves; useful uniform envelope remains open"

sep10Exact584Payments : ForensicReceipt
sep10Exact584Payments = forensic-receipt
  dashiAgda
  "exact class-budget payments on live spectator R584 carrier"
  "DASHI/Physics/Closure/NSTriadKNSpectatorWeightedExactClassNormPaymentBidiExact.agda"
  "ac898d515c3e9f2882c3b2102eaa5fc75fa2a2c3"
  "2026-09-10T06:20:48Z"
  "2026-09-10T16:20:48+10:00"
  "Johl Brown"
  exactClassPaymentCompiler
  "constructs live R584 class-norm payment witnesses; cutoff-uniform useful envelope and spacetime transport remain open"

------------------------------------------------------------------------
-- Public attribution atlas.  Git commits/repository artefacts have no DOI.
------------------------------------------------------------------------

repoSource : String → String → String → String → Source.AttributedSource
repoSource title context url relationship =
  Source.mkNoDOISource
    "Johl Brown"
    title
    context
    "2026"
    url
    (Source.namedSourceKind "GitHub repository source/commit")
    relationship
    Source.publicAttribution

jan24Source : Source.AttributedSource
jan24Source = repoSource
  "dashiCFD initial signed/ternary structural carrier"
  "chboishabba/dashiCFD commit 1cb1bb612c4061676a06e615f69bf282462c25cc"
  "https://github.com/chboishabba/dashiCFD/commit/1cb1bb612c4061676a06e615f69bf282462c25cc"
  "broad methodological ancestor only; not a Navier-Stokes proof receipt"

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

r294Source : Source.AttributedSource
r294Source = repoSource
  "R294 swap-invariant weighted commutator collapse"
  "chboishabba/dashi_agda commit 64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "https://github.com/chboishabba/dashi_agda/commit/64e2a4d2b067a05c0a8cf979ea3ed74f960c56dc"
  "formal weighted cancellation before absolute values"

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
  "exact spectator specialization of the nonseparable pair resolvent into the R294 weight interface"

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
  (jan24Source ∷ jun03Source ∷ jun04Source ∷ r294Source ∷ r503Source
    ∷ r541Source ∷ r573Source ∷ r584Source ∷ weldSource ∷ [])
  "public Git repository chronology and formalisation relationships; citations do not import correctness, external access, influence or authority"

------------------------------------------------------------------------
-- Earliest-forward snowball edges.
------------------------------------------------------------------------

edgeJanToTheta : SnowballEdge
edgeJanToTheta = snowball-edge
  "2026-01-24 signed/ternary structural codec"
  "2026-06-03 theta flux/dissipation sweep"
  broadStructuralAncestry
  "shared sign/support/residual design language, but no same-object NS theorem claim"
  false

edgeJanToSignedFlip : SnowballEdge
edgeJanToSignedFlip = snowball-edge
  "2026-01-24 signed/ternary structural codec"
  "2026-06-04 signed cross-shell flip audit"
  empiricalMethodPrecursor
  "sign classification and residual accounting become an explicitly cross-shell signed-flow diagnostic"
  false

edgeThetaToR503 : SnowballEdge
edgeThetaToR503 = snowball-edge
  "2026-06-03 theta barrier"
  "2026-09-07 R503 signed cutoff-uniform consumer"
  empiricalMethodPrecursor
  "both ask for a cutoff-uniform flux/production-vs-control barrier; R503 repairs the historical early-absolute-value loss"
  false

edgeSignedFlipToR294 : SnowballEdge
edgeSignedFlipToR294 = snowball-edge
  "2026-06-04 signed flip/net residue"
  "2026-08-30 R294 weighted commutator"
  empiricalMethodPrecursor
  "signed cancellation before positive majorization survives as a formal design principle; objects are not identified"
  false

edgeR120ToR294 : SnowballEdge
edgeR120ToR294 = snowball-edge
  "R120 physical commutator partner"
  "R294 swap-invariant weighted commutator"
  formalRefinement
  "formal commutator carrier is preserved under a generic swap-invariant weight"
  true

edgeR294ToR541 : SnowballEdge
edgeR294ToR541 = snowball-edge
  "R294 generic swap-invariant weight"
  "R541 literal spectator Cauchy weight"
  exactSpecialization
  "R541 constructs the literal spectator resolvent as an R294 SwapInvariantCellWeight"
  true

edgeR294ToR573 : SnowballEdge
edgeR294ToR573 = snowball-edge
  "R294 weighted commutator"
  "R573 nested weighted four-sign carrier"
  exactSameObject
  "R573 proves the actual weighted R438/R294 outer carrier equals its nested four-sign representation before norms"
  true

edgeR541ToWeld : SnowballEdge
edgeR541ToWeld = snowball-edge
  "R541 spectator resolvent"
  "R541 x R573 explicit composition"
  compositionInput
  "R541.spectatorWeight beta is instantiated directly into R573"
  true

edgeR573ToWeld : SnowballEdge
edgeR573ToWeld = snowball-edge
  "R573 nested weighted commutator"
  "R541 x R573 explicit composition"
  compositionInput
  "generic R573 weighted nested theorem receives the literal R541 spectator weight"
  true

edgeWeldToDirect : SnowballEdge
edgeWeldToDirect = snowball-edge
  "R541 x R573 nested spectator weld"
  "R496/R497 direct resolvent companion route"
  exactSameObject
  "the nested spectator row is composed through the literal pair scalar to four times the canonical direct companion"
  true

edgeDirectToR503 : SnowballEdge
edgeDirectToR503 = snowball-edge
  "R496/R497/R500 direct companion"
  "R503 terminal signed consumer"
  canonicalConsumer
  "R503 consumes the exact integrated direct companion and preserves sign"
  true

edgeR584ToWeighted584 : SnowballEdge
edgeR584ToWeighted584 = snowball-edge
  "R584 live nested-slot class norm carrier"
  "R541-weighted live R584 carrier"
  exactSpecialization
  "R584's generic outer weight is instantiated by the literal R541 spectator Cauchy weight"
  true

edgeWeighted584ToCurrentWall : SnowballEdge
edgeWeighted584ToCurrentWall = snowball-edge
  "R541-weighted live R584 exact class payments"
  "cutoff-uniform spectator-weighted class-norm/spacetime envelope"
  analyticFrontier
  "exact payment witnesses now exist; the useful cutoff-uniform majorant and spacetime transport remain theorem-bearing"
  false

forensicSnowball : List SnowballEdge
forensicSnowball =
  edgeJanToTheta ∷
  edgeJanToSignedFlip ∷
  edgeThetaToR503 ∷
  edgeSignedFlipToR294 ∷
  edgeR120ToR294 ∷
  edgeR294ToR541 ∷
  edgeR294ToR573 ∷
  edgeR541ToWeld ∷
  edgeR573ToWeld ∷
  edgeWeldToDirect ∷
  edgeDirectToR503 ∷
  edgeR584ToWeighted584 ∷
  edgeWeighted584ToCurrentWall ∷ []

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

sourceExistenceDoesNotImplyCorrectness :
  SourceExistenceImpliesMathematicalCorrectness → ⊥
sourceExistenceDoesNotImplyCorrectness ()

chronologyDoesNotImplyThirdPartyAccess : ChronologyImpliesThirdPartyAccess → ⊥
chronologyDoesNotImplyThirdPartyAccess ()

publicRepoDoesNotImplyModelTrainingUse : PublicRepositoryImpliesModelTrainingUse → ⊥
publicRepoDoesNotImplyModelTrainingUse ()

chronologyDoesNotImplyCopying : ChronologyImpliesCopying → ⊥
chronologyDoesNotImplyCopying ()

chronologyDoesNotImplyRewardHacking : ChronologyImpliesRewardHacking → ⊥
chronologyDoesNotImplyRewardHacking ()

empiricalPrecursorDoesNotBecomeFormalIdentityByChronology :
  EmpiricalPrecursorImpliesFormalSameObject → ⊥
empiricalPrecursorDoesNotBecomeFormalIdentityByChronology ()

similarVocabularyDoesNotProveSameTheorem : SimilarVocabularyImpliesSameTheorem → ⊥
similarVocabularyDoesNotProveSameTheorem ()

------------------------------------------------------------------------
-- Audit status.
------------------------------------------------------------------------

auditDirectionEarliestForward : Bool
auditDirectionEarliestForward = true

everyReceiptCarriesUTCAndBrisbaneDate : Bool
everyReceiptCarriesUTCAndBrisbaneDate = true

relationshipStrengthIsExplicit : Bool
relationshipStrengthIsExplicit = true

januaryStructuralAncestorIsClaimedAsExactNSObject : Bool
januaryStructuralAncestorIsClaimedAsExactNSObject = false

juneEmpiricalObjectsAreClaimedAsFormalProofs : Bool
juneEmpiricalObjectsAreClaimedAsFormalProofs = false

priorRepositoryExistenceOfSignedAndBarrierIngredientsRecorded : Bool
priorRepositoryExistenceOfSignedAndBarrierIngredientsRecorded = true

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

thirdPartyAccessEstablishedByThisAuditIsFalse :
  thirdPartyAccessEstablishedByThisAudit ≡ false
thirdPartyAccessEstablishedByThisAuditIsFalse = refl

copyingEstablishedByThisAuditIsFalse : copyingEstablishedByThisAudit ≡ false
copyingEstablishedByThisAuditIsFalse = refl

rewardHackingEstablishedByThisAuditIsFalse :
  rewardHackingEstablishedByThisAudit ≡ false
rewardHackingEstablishedByThisAuditIsFalse = refl

r541xR573ExplicitCompositionRecordedIsTrue :
  r541xR573ExplicitCompositionRecorded ≡ true
r541xR573ExplicitCompositionRecordedIsTrue =
  Weld541x573.roundSpectatorNestedR541WeightInstantiatedIntoR573IsTrue

nestedRouteLandsOnCanonicalDirectCarrierIsTrue :
  nestedRouteLandsOnCanonicalDirectCarrier ≡ true
nestedRouteLandsOnCanonicalDirectCarrierIsTrue =
  NestedFibre.nestedFactoredFullToCanonicalR497CarrierClosedIsTrue

liveR584ExactPaymentExistenceClosedIsTrue :
  liveR584ExactPaymentExistenceClosed ≡ true
liveR584ExactPaymentExistenceClosedIsTrue =
  Exact584Payment.liveR584ClassNormPaymentExistenceClosedIsTrue

currentUsefulUniformEnvelopeClosedIsFalse :
  currentUsefulUniformEnvelopeClosed ≡ false
currentUsefulUniformEnvelopeClosedIsFalse =
  Exact584Payment.uniformUpperOnExactClassNormEnvelopeClosedIsFalse

currentR503BudgetClosedIsFalse : currentR503BudgetClosed ≡ false
currentR503BudgetClosedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
