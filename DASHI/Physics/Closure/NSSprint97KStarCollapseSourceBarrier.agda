module DASHI.Physics.Closure.NSSprint97KStarCollapseSourceBarrier where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint96KStarCollapseMechanismConstraints
  as Sprint96

------------------------------------------------------------------------
-- Sprint 97 K* collapse source barrier.
--
-- This receipt records a negative in-repo status: the current Option B
-- candidate families do not supply a same-source finite-time mechanism
-- forcing K*(t) -> 0.  It closes only this source-barrier ledger and does
-- not solve or promote the Clay Navier-Stokes problem.

kStarCollapseSourceBarrierLedgerClosed : Bool
kStarCollapseSourceBarrierLedgerClosed = true

failClosedKStarSourceBarrier : Bool
failClosedKStarSourceBarrier = true

sameSourceCollapseMechanismAvailable : Bool
sameSourceCollapseMechanismAvailable = false

finiteTimeKStarCollapseClosed : Bool
finiteTimeKStarCollapseClosed = false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

optionBBlowupConstructionClosed : Bool
optionBBlowupConstructionClosed = false

data CandidateFamily : Set where
  algebraicCandidate :
    CandidateFamily
  logarithmicCandidate :
    CandidateFamily
  oscillatoryCandidate :
    CandidateFamily
  constantLowerBoundCandidate :
    CandidateFamily

data CandidateFamilyRejection : Set where
  AlgebraicCollapseRejected :
    CandidateFamilyRejection
  LogarithmicCollapseRejected :
    CandidateFamilyRejection
  OscillatoryCollapseRejected :
    CandidateFamilyRejection
  ConstantLowerBoundRejected :
    CandidateFamilyRejection

data RequiredAnalyticObject : Set where
  LowModeEnergyConcentrationDynamics :
    RequiredAnalyticObject
  ViscousDampingDefeatEstimate :
    RequiredAnalyticObject
  LerayCompatibleCollapseTrajectory :
    RequiredAnalyticObject
  SingularityExtractionWithoutBKMOrSerrin :
    RequiredAnalyticObject

requiredAnalyticObjects :
  List RequiredAnalyticObject
requiredAnalyticObjects =
  LowModeEnergyConcentrationDynamics
  ∷ ViscousDampingDefeatEstimate
  ∷ LerayCompatibleCollapseTrajectory
  ∷ SingularityExtractionWithoutBKMOrSerrin
  ∷ []

KStarCollapseSourceBarrierResiduals :
  List RequiredAnalyticObject
KStarCollapseSourceBarrierResiduals =
  requiredAnalyticObjects

record SameSourceCollapseMechanism : Set where
  constructor sameSourceCollapseMechanismReceipt
  field
    available :
      Bool
    availableIsFalse :
      available ≡ false
    finiteTimeCollapseClosedHere :
      finiteTimeKStarCollapseClosed ≡ false
    inheritedSprint96MechanismStillOpen :
      Sprint96.kStarCollapseMechanismClosed ≡ false
    note :
      String

open SameSourceCollapseMechanism public

canonicalSameSourceCollapseMechanism :
  SameSourceCollapseMechanism
canonicalSameSourceCollapseMechanism =
  sameSourceCollapseMechanismReceipt
    false
    refl
    refl
    refl
    "No same-source finite-time K*(t)->0 collapse mechanism is supplied by the current in-repo Option B candidate families."

record CollapseSourceBarrier : Set where
  constructor collapseSourceBarrierReceipt
  field
    mechanism :
      SameSourceCollapseMechanism
    mechanismIsCanonical :
      mechanism ≡ canonicalSameSourceCollapseMechanism
    missingObjects :
      List RequiredAnalyticObject
    missingObjectsAreCanonical :
      missingObjects ≡ requiredAnalyticObjects
    sameSourceMechanismAvailableHere :
      sameSourceCollapseMechanismAvailable ≡ false
    optionBConstructionClosedHere :
      optionBBlowupConstructionClosed ≡ false
    clayPromotionRejectedHere :
      clayNavierStokesPromoted ≡ false
    note :
      String

open CollapseSourceBarrier public

KStarSourceBarrier : Set
KStarSourceBarrier = CollapseSourceBarrier

canonicalCollapseSourceBarrier :
  CollapseSourceBarrier
canonicalCollapseSourceBarrier =
  collapseSourceBarrierReceipt
    canonicalSameSourceCollapseMechanism
    refl
    requiredAnalyticObjects
    refl
    refl
    refl
    refl
    "The source barrier is closed as a diagnostic ledger only; the finite-time blowup construction remains open."

record CandidateRejectionLedgerEntry : Set where
  constructor candidateRejectionLedgerEntry
  field
    family :
      CandidateFamily
    rejection :
      CandidateFamilyRejection
    suppliesSameSourceCollapse :
      Bool
    suppliesSameSourceCollapseIsFalse :
      suppliesSameSourceCollapse ≡ false
    note :
      String

open CandidateRejectionLedgerEntry public

algebraicCollapseRejection :
  CandidateRejectionLedgerEntry
algebraicCollapseRejection =
  candidateRejectionLedgerEntry
    algebraicCandidate
    AlgebraicCollapseRejected
    false
    refl
    "Algebraic decay/collapse ansatz is rejected as an in-repo same-source finite-time K* collapse source."

logarithmicCollapseRejection :
  CandidateRejectionLedgerEntry
logarithmicCollapseRejection =
  candidateRejectionLedgerEntry
    logarithmicCandidate
    LogarithmicCollapseRejected
    false
    refl
    "Logarithmic decay/collapse ansatz is rejected as an in-repo same-source finite-time K* collapse source."

oscillatoryCollapseRejection :
  CandidateRejectionLedgerEntry
oscillatoryCollapseRejection =
  candidateRejectionLedgerEntry
    oscillatoryCandidate
    OscillatoryCollapseRejected
    false
    refl
    "Oscillatory ansatz is rejected as an in-repo same-source finite-time K* collapse source."

constantLowerBoundRejection :
  CandidateRejectionLedgerEntry
constantLowerBoundRejection =
  candidateRejectionLedgerEntry
    constantLowerBoundCandidate
    ConstantLowerBoundRejected
    false
    refl
    "Constant lower-bound family blocks K*(t)->0 and is rejected as a collapse source."

candidateFamilyRejectionLedger :
  List CandidateRejectionLedgerEntry
candidateFamilyRejectionLedger =
  algebraicCollapseRejection
  ∷ logarithmicCollapseRejection
  ∷ oscillatoryCollapseRejection
  ∷ constantLowerBoundRejection
  ∷ []

record NSSprint97KStarCollapseSourceBarrier : Set where
  constructor nsSprint97KStarCollapseSourceBarrierReceipt
  field
    sprint96Anchor :
      Sprint96.NSSprint96KStarCollapseMechanismConstraints
    sprint96AnchorIsCanonical :
      sprint96Anchor
      ≡ Sprint96.canonicalNSSprint96KStarCollapseMechanismConstraints
    sourceBarrier :
      CollapseSourceBarrier
    sourceBarrierIsCanonical :
      sourceBarrier ≡ canonicalCollapseSourceBarrier
    rejectionLedger :
      List CandidateRejectionLedgerEntry
    rejectionLedgerIsCanonical :
      rejectionLedger ≡ candidateFamilyRejectionLedger
    requiredAnalyticObjectAnchor :
      List RequiredAnalyticObject
    requiredAnalyticObjectAnchorIsCanonical :
      requiredAnalyticObjectAnchor ≡ requiredAnalyticObjects
    kStarCollapseSourceBarrierLedgerClosedIsTrue :
      kStarCollapseSourceBarrierLedgerClosed ≡ true
    sameSourceCollapseMechanismAvailableIsFalse :
      sameSourceCollapseMechanismAvailable ≡ false
    finiteTimeKStarCollapseClosedIsFalse :
      finiteTimeKStarCollapseClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    optionBBlowupConstructionClosedIsFalse :
      optionBBlowupConstructionClosed ≡ false
    inheritedSprint96OptionBFiniteTimeKStarCollapseStillOpen :
      Sprint96.optionBFiniteTimeKStarCollapseClosed ≡ false
    noClayClaim :
      String

open NSSprint97KStarCollapseSourceBarrier public

canonicalNSSprint97KStarCollapseSourceBarrier :
  NSSprint97KStarCollapseSourceBarrier
canonicalNSSprint97KStarCollapseSourceBarrier =
  nsSprint97KStarCollapseSourceBarrierReceipt
    Sprint96.canonicalNSSprint96KStarCollapseMechanismConstraints
    refl
    canonicalCollapseSourceBarrier
    refl
    candidateFamilyRejectionLedger
    refl
    requiredAnalyticObjects
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    "No Navier-Stokes Clay solution is claimed; this receipt only records the same-source K* collapse source barrier."

canonicalNSSprint97KStarCollapseSourceBarrierReceipt :
  NSSprint97KStarCollapseSourceBarrier
canonicalNSSprint97KStarCollapseSourceBarrierReceipt =
  canonicalNSSprint97KStarCollapseSourceBarrier

canonicalSprint97Flags :
  (kStarCollapseSourceBarrierLedgerClosed ≡ true)
  × (sameSourceCollapseMechanismAvailable ≡ false)
  × (finiteTimeKStarCollapseClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
  × (optionBBlowupConstructionClosed ≡ false)
canonicalSprint97Flags =
  refl , refl , refl , refl , refl
