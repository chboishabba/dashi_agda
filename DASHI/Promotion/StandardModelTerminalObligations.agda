module DASHI.Promotion.StandardModelTerminalObligations where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Constants.Registry as Registry
import DASHI.Physics.QFT.ExactSMMatchToken as ExactSM
import DASHI.Physics.QFT.SMContentSummaryReceipt as SMContent
import DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary as Terminal

------------------------------------------------------------------------
-- Standard Model and terminal/full-unification promotion obligations.
--
-- This module is a promotion queue, not a claim flip.  It records the
-- concrete proof/authority rows that must be inhabited before Standard Model
-- or terminal/full-unification promotion can be accepted.

data PromotionPhase : Set where
  standardModelPhase : PromotionPhase
  terminalFullUnificationPhase : PromotionPhase

data ObligationStatus : Set where
  packagedPositiveInput : ObligationStatus
  authorityRequired : ObligationStatus
  proofRequired : ObligationStatus
  validationRequired : ObligationStatus
  claimAuditRequired : ObligationStatus

data PromotionGuard : Set where
  standardModelPromotedGuard : PromotionGuard
  continuousGaugeGroupBridgeGuard : PromotionGuard
  physicalSectorMapGuard : PromotionGuard
  empiricalObservableBridgeGuard : PromotionGuard
  crossLaneConsistencyGuard : PromotionGuard
  noContradictoryBlockersGuard : PromotionGuard
  aggregateValidationGuard : PromotionGuard
  claimSurfaceAuditGuard : PromotionGuard
  terminalTheoremAuthorityTokenGuard : PromotionGuard
  terminalPromotionGuard : PromotionGuard

data StandardModelPromotionTarget : Set where
  representationTableTarget : StandardModelPromotionTarget
  gaugeNormalizationTarget : StandardModelPromotionTarget
  hyperchargeConventionTarget : StandardModelPromotionTarget
  anomalyCancellationTarget : StandardModelPromotionTarget
  higgsYukawaCKMPMNSPDGAuthorityTarget : StandardModelPromotionTarget
  continuousGaugeBridgeTarget : StandardModelPromotionTarget
  physicalSectorMapTarget : StandardModelPromotionTarget
  empiricalObservableBridgeTarget : StandardModelPromotionTarget
  exactSMMatchTokenTarget : StandardModelPromotionTarget

data TerminalPromotionTarget : Set where
  crossLaneConsistencyTarget : TerminalPromotionTarget
  noContradictoryBlockersTarget : TerminalPromotionTarget
  aggregateValidationTarget : TerminalPromotionTarget
  claimSurfaceAuditTarget : TerminalPromotionTarget
  terminalTheoremAuthorityTokenTarget : TerminalPromotionTarget

data PromotionTarget : Set where
  smTarget : StandardModelPromotionTarget → PromotionTarget
  terminalTarget : TerminalPromotionTarget → PromotionTarget

record PromotionObligationRow : Set₁ where
  field
    obligationLabel : String
    phase : PromotionPhase
    target : PromotionTarget
    ownerSurface : String
    upstreamReceipts : List String
    requiredProofOrAuthority : List String
    blockingDeficits : List String
    guardToFlip : PromotionGuard
    currentStatus : ObligationStatus
    validationTarget : String
    promotesClaim : Bool
    promotesClaimIsFalse : promotesClaim ≡ false

open PromotionObligationRow public

obligationCount : List PromotionObligationRow → Nat
obligationCount [] = zero
obligationCount (_ ∷ xs) = suc (obligationCount xs)

appendObligations :
  List PromotionObligationRow →
  List PromotionObligationRow →
  List PromotionObligationRow
appendObligations [] ys = ys
appendObligations (x ∷ xs) ys = x ∷ appendObligations xs ys

mkObligation :
  String →
  PromotionPhase →
  PromotionTarget →
  String →
  List String →
  List String →
  List String →
  PromotionGuard →
  ObligationStatus →
  String →
  PromotionObligationRow
mkObligation label phase target owner upstream required blockers guard status
  validation =
  record
    { obligationLabel = label
    ; phase = phase
    ; target = target
    ; ownerSurface = owner
    ; upstreamReceipts = upstream
    ; requiredProofOrAuthority = required
    ; blockingDeficits = blockers
    ; guardToFlip = guard
    ; currentStatus = status
    ; validationTarget = validation
    ; promotesClaim = false
    ; promotesClaimIsFalse = refl
    }

canonicalStandardModelObligations : List PromotionObligationRow
canonicalStandardModelObligations =
  mkObligation
    "representation table"
    standardModelPhase
    (smTarget representationTableTarget)
    "DASHI.Physics.QFT.SMContentSummaryReceipt"
    ( "canonicalSMContentSummaryReceipt"
    ∷ "canonicalExactSMMatchReceipt"
    ∷ []
    )
    ( "complete chiral fermion representation table for SU3c x SU2L x U1Y"
    ∷ "left/right chirality convention"
    ∷ "generation and neutrino convention"
    ∷ "faithful map from finite lane rows to continuous SM representations"
    ∷ []
    )
    ( "finite content rows are not yet a physical representation theorem"
    ∷ "exact carrier-functor match remains blocked"
    ∷ []
    )
    standardModelPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/SMContentSummaryReceipt.agda"
  ∷ mkObligation
    "gauge normalization"
    standardModelPhase
    (smTarget gaugeNormalizationTarget)
    "DASHI.Physics.QFT.ChargeNormalisationReceipt"
    ( "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    ∷ "canonicalSMContentSummaryReceipt"
    ∷ []
    )
    ( "normalised generators for SU3c, SU2L, and U1Y"
    ∷ "coupling and charge convention receipt"
    ∷ "PDG/CODATA authority binding for physical normalization"
    ∷ []
    )
    ( "finite charge bookkeeping does not fix physical normalization"
    ∷ "measured coupling constants remain authority-gated"
    ∷ []
    )
    standardModelPromotedGuard
    authorityRequired
    "agda -i . DASHI/Constants/Registry.agda"
  ∷ mkObligation
    "hypercharge convention"
    standardModelPhase
    (smTarget hyperchargeConventionTarget)
    "DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt"
    ( "canonicalSMContentSummaryReceipt"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "exact U1Y convention with standard sixfold normalization"
    ∷ "left/right multiplet assignment"
    ∷ "electric charge relation Q = T3 + Y"
    ∷ []
    )
    ( "continuous U1Y bridge remains conditional"
    ∷ "carrier-derived exact hypercharge assignment is not proved"
    ∷ []
    )
    continuousGaugeGroupBridgeGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/HyperchargeNormalisationAnomalyReceipt.agda"
  ∷ mkObligation
    "anomaly cancellation"
    standardModelPhase
    (smTarget anomalyCancellationTarget)
    "DASHI.Physics.QFT.HyperchargeNormalisationAnomalyReceipt"
    ( "canonicalSMContentSummaryReceipt"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "SU3^2-U1 anomaly sum"
    ∷ "SU2^2-U1 anomaly sum"
    ∷ "U1^3 anomaly sum"
    ∷ "gravitational-U1 anomaly sum"
    ∷ "global SU2/Witten anomaly boundary"
    ∷ []
    )
    ( "standard anomaly ledger is separated from carrier derivation"
    ∷ "multiplet table and hypercharge convention must be consumed first"
    ∷ []
    )
    standardModelPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/HyperchargeNormalisationAnomalyReceipt.agda"
  ∷ mkObligation
    "Higgs Yukawa CKM PMNS PDG authority"
    standardModelPhase
    (smTarget higgsYukawaCKMPMNSPDGAuthorityTarget)
    "DASHI.Constants.Registry"
    ( "canonicalAuthorityConsumptionPolicyReceipt"
    ∷ "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    ∷ []
    )
    ( "PDG versioned Higgs, W/Z, fermion masses, CKM, PMNS, alpha_s, and G_F receipt"
    ∷ "source checksum and access date"
    ∷ "uncertainty and rounding policy"
    ∷ "consumer receipt proving values were loaded under policy"
    ∷ []
    )
    ( "numeric measured values are not promoted"
    ∷ "Higgs/Yukawa/CKM/PMNS are currently authority placeholders"
    ∷ []
    )
    standardModelPromotedGuard
    authorityRequired
    "agda -i . DASHI/Constants/Registry.agda"
  ∷ mkObligation
    "continuous SU3 x SU2 x U1 bridge"
    standardModelPhase
    (smTarget continuousGaugeBridgeTarget)
    "DASHI.Physics.QFT.ExactSMMatchToken"
    ( "canonicalExactSMMatchReceipt"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "DHR compact-group to SM gauge-isomorphism receipt"
    ∷ "finite-to-continuous SU3c bridge"
    ∷ "finite-to-continuous SU2L bridge"
    ∷ "finite-to-continuous U1Y bridge"
    ∷ "Gate1/Gate6 carrier-functor equivalence"
    ∷ []
    )
    ( "canonical first blocker is carrier-functor equivalence"
    ∷ "DHR compact-group to SM gauge isomorphism is absent"
    ∷ []
    )
    continuousGaugeGroupBridgeGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/ExactSMMatchToken.agda"
  ∷ mkObligation
    "physical sector map"
    standardModelPhase
    (smTarget physicalSectorMapTarget)
    "DASHI.Physics.QFT.SMContentSummaryReceipt"
    ( "canonicalSMContentSummaryReceipt"
    ∷ "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    ∷ []
    )
    ( "gauge boson sector"
    ∷ "fermion sector"
    ∷ "Higgs sector"
    ∷ "Yukawa and mixing sector"
    ∷ "mass/eigenbasis convention"
    ∷ []
    )
    ( "finite matter-lane labels are not a physical sector map"
    ∷ "lepton and Higgs/Yukawa closures remain conditional"
    ∷ []
    )
    physicalSectorMapGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/SMContentSummaryReceipt.agda"
  ∷ mkObligation
    "empirical observable bridge"
    standardModelPhase
    (smTarget empiricalObservableBridgeTarget)
    "DASHI.Constants.Registry"
    ( "canonicalEmpiricalRuntimeKnownInputsReferenceReceipt"
    ∷ "canonicalAuthorityConsumptionPolicyReceipt"
    ∷ []
    )
    ( "observable definition"
    ∷ "projection/transform law"
    ∷ "comparison law"
    ∷ "covariance/unit/calibration receipt"
    ∷ "holdout validation protocol"
    ∷ "accepted provider authority token"
    ∷ []
    )
    ( "provider authority is not accepted"
    ∷ "comparison, covariance, calibration, and holdout guards remain false"
    ∷ []
    )
    empiricalObservableBridgeGuard
    validationRequired
    "agda -i . DASHI/Constants/Registry.agda"
  ∷ mkObligation
    "exact SM match token boundary"
    standardModelPhase
    (smTarget exactSMMatchTokenTarget)
    "DASHI.Physics.QFT.ExactSMMatchToken"
    ( "canonicalExactSMMatchReceipt"
    ∷ "canonicalGate8Term1FiniteGaugeEvidenceBlockerReceipt"
    ∷ []
    )
    ( "exact carrier-functor match"
    ∷ "DHR compact-group to SM gauge isomorphism"
    ∷ "low-energy SU2R breaking receipt when using the Pati-Salam-side path"
    ∷ []
    )
    ( "token packages finite witnesses only"
    ∷ "exact SM match promotion remains false"
    ∷ []
    )
    standardModelPromotedGuard
    proofRequired
    "agda -i . DASHI/Physics/QFT/ExactSMMatchToken.agda"
  ∷ []

canonicalTerminalObligations : List PromotionObligationRow
canonicalTerminalObligations =
  mkObligation
    "cross-lane consistency"
    terminalFullUnificationPhase
    (terminalTarget crossLaneConsistencyTarget)
    "DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary"
    ( "canonicalCategoricalInterlinkReceipt"
    ∷ "canonicalPhysicsAdapterKnownInputsReferenceReceipt"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "G_DHR = G_SM compatibility"
    ∷ "T_YM = T_GR stress-energy compatibility"
    ∷ "DHR/Yukawa compatibility"
    ∷ "Stone spectrum versus YM mass-gap compatibility"
    ∷ "shared unit and authority policy"
    ∷ []
    )
    ( "Gate1/Gate6 exact SM match remains blocked"
    ∷ "stress-energy, Stone, and YM mass-gap bridges are not jointly closed"
    ∷ []
    )
    crossLaneConsistencyGuard
    proofRequired
    "agda -i . DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda"
  ∷ mkObligation
    "no contradictory blockers"
    terminalFullUnificationPhase
    (terminalTarget noContradictoryBlockersTarget)
    "DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary"
    ( "canonicalCategoricalInterlinkReceipt"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "global blocker scan"
    ∷ "all open blockers classified as solved, superseded, or out-of-scope"
    ∷ "no false promotion flag in consumed receipts"
    ∷ []
    )
    ( "known Standard Model, QFT, empirical, NS, and YM blockers remain live"
    ∷ "terminal promotion cannot outrun lane guards"
    ∷ []
    )
    noContradictoryBlockersGuard
    validationRequired
    "rg -n \"Promoted.*false|terminal.*false|Blocker|blocked\" DASHI Docs"
  ∷ mkObligation
    "aggregate validation"
    terminalFullUnificationPhase
    (terminalTarget aggregateValidationTarget)
    "DASHI.Everything"
    ( "DASHI.Promotion.StandardModelTerminalObligations"
    ∷ "DASHI.Constants.Registry"
    ∷ "DASHI.Interop.CategoricalInterlinkLayer"
    ∷ []
    )
    ( "targeted Agda validation for all consumed owners"
    ∷ "root or certification aggregate validation"
    ∷ "diff/link/checksum sanity"
    ∷ "failure triage with no skipped required lane"
    ∷ []
    )
    ( "DASHI/Everything.agda is heavy/certification-only"
    ∷ "root validation has not been used as promotion evidence"
    ∷ []
    )
    aggregateValidationGuard
    validationRequired
    "agda -i . DASHI/Everything.agda"
  ∷ mkObligation
    "claim-surface audit"
    terminalFullUnificationPhase
    (terminalTarget claimSurfaceAuditTarget)
    "Docs/Paper8ReceiptIndex.md"
    ( "canonicalStandardModelTerminalPromotionObligationReceipt"
    ∷ "canonicalCategoricalInterlinkReceipt"
    ∷ []
    )
    ( "public theorem statement"
    ∷ "claim boundary audit"
    ∷ "promotion flag audit"
    ∷ "receipt index update"
    ∷ []
    )
    ( "claim docs must follow code guards, not precede them"
    ∷ "this worker was code-only, so docs are intentionally untouched"
    ∷ []
    )
    claimSurfaceAuditGuard
    claimAuditRequired
    "git diff --check -- Docs README.md TODO.md CHANGELOG.md"
  ∷ mkObligation
    "terminal theorem authority token"
    terminalFullUnificationPhase
    (terminalTarget terminalTheoremAuthorityTokenTarget)
    "DASHI.Physics.Closure.GRQFTTerminalCompositionBoundary"
    ( "canonicalGRQFTTerminalCompositionBoundary"
    ∷ "canonicalExactSMMatchBlockerReceipt"
    ∷ []
    )
    ( "terminal theorem statement"
    ∷ "inhabited proof or accepted external authority token"
    ∷ "all upstream lane guards consumed"
    ∷ "aggregate validation receipt"
    ∷ "claim-surface audit receipt"
    ∷ []
    )
    ( "terminal theorem/authority token is absent"
    ∷ "full unification remains downstream of Standard Model, QFT, GR, NS, YM, empirical, and adapter gates"
    ∷ []
    )
    terminalTheoremAuthorityTokenGuard
    proofRequired
    "agda -i . DASHI/Physics/Closure/GRQFTTerminalCompositionBoundary.agda"
  ∷ []

canonicalAllObligations : List PromotionObligationRow
canonicalAllObligations =
  appendObligations
    canonicalStandardModelObligations
    canonicalTerminalObligations

record StandardModelTerminalPromotionObligationReceipt : Setω where
  field
    registryReceipt :
      Registry.PhysicsAdapterKnownInputsReferenceReceipt

    smContentSummaryReceipt :
      SMContent.SMContentSummaryReceipt

    exactSMMatchBlockerReceipt :
      ExactSM.ExactSMMatchBlockerReceipt

    terminalCompositionBoundary :
      Terminal.GRQFTCompositionBoundary

    standardModelObligations :
      List PromotionObligationRow

    terminalObligations :
      List PromotionObligationRow

    allObligations :
      List PromotionObligationRow

    standardModelObligationCount :
      Nat

    standardModelObligationCountMatches :
      standardModelObligationCount ≡ obligationCount standardModelObligations

    terminalObligationCount :
      Nat

    terminalObligationCountMatches :
      terminalObligationCount ≡ obligationCount terminalObligations

    allObligationCount :
      Nat

    allObligationCountMatches :
      allObligationCount ≡ obligationCount allObligations

    standardModelPromoted :
      Bool

    standardModelPromotedIsFalse :
      standardModelPromoted ≡ false

    terminalPromotion :
      Bool

    terminalPromotionIsFalse :
      terminalPromotion ≡ false

    fullUnificationPromoted :
      Bool

    fullUnificationPromotedIsFalse :
      fullUnificationPromoted ≡ false

    promotionBoundary :
      List String

open StandardModelTerminalPromotionObligationReceipt public

canonicalStandardModelTerminalPromotionObligationReceipt :
  StandardModelTerminalPromotionObligationReceipt
canonicalStandardModelTerminalPromotionObligationReceipt =
  record
    { registryReceipt =
        Registry.canonicalPhysicsAdapterKnownInputsReferenceReceipt
    ; smContentSummaryReceipt =
        SMContent.canonicalSMContentSummaryReceipt
    ; exactSMMatchBlockerReceipt =
        ExactSM.canonicalExactSMMatchBlockerReceipt
    ; terminalCompositionBoundary =
        Terminal.canonicalGRQFTCompositionBoundary
    ; standardModelObligations =
        canonicalStandardModelObligations
    ; terminalObligations =
        canonicalTerminalObligations
    ; allObligations =
        canonicalAllObligations
    ; standardModelObligationCount =
        obligationCount canonicalStandardModelObligations
    ; standardModelObligationCountMatches =
        refl
    ; terminalObligationCount =
        obligationCount canonicalTerminalObligations
    ; terminalObligationCountMatches =
        refl
    ; allObligationCount =
        obligationCount canonicalAllObligations
    ; allObligationCountMatches =
        refl
    ; standardModelPromoted =
        false
    ; standardModelPromotedIsFalse =
        refl
    ; terminalPromotion =
        false
    ; terminalPromotionIsFalse =
        refl
    ; fullUnificationPromoted =
        false
    ; fullUnificationPromotedIsFalse =
        refl
    ; promotionBoundary =
        "Standard Model promotion requires representation, normalization, hypercharge, anomaly, authority, continuous-gauge, sector-map, and empirical-observable obligations"
        ∷ "Terminal promotion additionally requires cross-lane consistency, no contradictory blockers, aggregate validation, claim-surface audit, and a terminal theorem/authority token"
        ∷ "This receipt is a promotion obligation index only; every claim-promoting bit remains false"
        ∷ []
    }

canonicalStandardModelObligationCountIs9 :
  standardModelObligationCount
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  9
canonicalStandardModelObligationCountIs9 = refl

canonicalTerminalObligationCountIs5 :
  terminalObligationCount
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  5
canonicalTerminalObligationCountIs5 = refl

canonicalAllObligationCountIs14 :
  allObligationCount
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  14
canonicalAllObligationCountIs14 = refl

standardModelTerminalReceiptKeepsSMPromotionFalse :
  standardModelPromoted
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  false
standardModelTerminalReceiptKeepsSMPromotionFalse = refl

standardModelTerminalReceiptKeepsTerminalPromotionFalse :
  terminalPromotion
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  false
standardModelTerminalReceiptKeepsTerminalPromotionFalse = refl

standardModelTerminalReceiptKeepsFullUnificationFalse :
  fullUnificationPromoted
    canonicalStandardModelTerminalPromotionObligationReceipt
  ≡
  false
standardModelTerminalReceiptKeepsFullUnificationFalse = refl
