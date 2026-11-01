module DASHI.Physics.Closure.NSSprint95OptionBBlowupFeasibilityLedger where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint94KStarForkObstructionAndConditionalRegularity
  as Sprint94

------------------------------------------------------------------------
-- Sprint 95 Option B blowup feasibility ledger.
--
-- Sprint 94 records the K* fork: the general-data regularity route is
-- obstructed by the K* lower-bound/small-data calculation, Option C is
-- only a conditional regularity criterion, and Option B blowup remains
-- open.  Sprint 95 does not construct a singular solution.  It records
-- the concrete feasibility requirements that an Option B blowup attempt
-- would still have to close.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

blowupConstructionClosed : Bool
blowupConstructionClosed = false

optionBBlowupConstructionClosed : Bool
optionBBlowupConstructionClosed = false

optionBBlowupFeasibilityLedgerClosed : Bool
optionBBlowupFeasibilityLedgerClosed = true

optionBFeasibilityLedgerClosed : Bool
optionBFeasibilityLedgerClosed = true

sprint94ForkObstructionInheritedClosed : Bool
sprint94ForkObstructionInheritedClosed = true

sprint94ConditionalCriterionInheritedClosed : Bool
sprint94ConditionalCriterionInheritedClosed = true

kStarCollapseMechanismClosed : Bool
kStarCollapseMechanismClosed = false

compatibilityWithLerayEnergyClosed : Bool
compatibilityWithLerayEnergyClosed = false

exclusionOfConditionalKStarLowerBoundClosed : Bool
exclusionOfConditionalKStarLowerBoundClosed = false

finiteTimeSingularityExtractionClosed : Bool
finiteTimeSingularityExtractionClosed = false

data OptionBBlowupFeasibilityGate : Set where
  kStarCollapseMechanism :
    OptionBBlowupFeasibilityGate
  compatibilityWithLerayEnergy :
    OptionBBlowupFeasibilityGate
  exclusionOfConditionalKStarLowerBound :
    OptionBBlowupFeasibilityGate
  finiteTimeSingularityExtraction :
    OptionBBlowupFeasibilityGate

canonicalOptionBBlowupFeasibilityGates :
  List OptionBBlowupFeasibilityGate
canonicalOptionBBlowupFeasibilityGates =
  kStarCollapseMechanism
  ∷ compatibilityWithLerayEnergy
  ∷ exclusionOfConditionalKStarLowerBound
  ∷ finiteTimeSingularityExtraction
  ∷ []

data OptionBGateStatus : Set where
  openAfterSprint94 :
    OptionBGateStatus

record OptionBOpenGateLedgerEntry : Set where
  constructor optionBOpenGateLedgerEntry
  field
    gate :
      OptionBBlowupFeasibilityGate
    status :
      OptionBGateStatus
    closed :
      Bool
    closedIsFalse :
      closed ≡ false
    note :
      String

open OptionBOpenGateLedgerEntry public

kStarCollapseMechanismLedger :
  OptionBOpenGateLedgerEntry
kStarCollapseMechanismLedger =
  optionBOpenGateLedgerEntry
    kStarCollapseMechanism
    openAfterSprint94
    false
    refl
    "Open gate: provide a mechanism forcing K* collapse rather than assuming the Sprint 94 conditional lower-bound hypothesis."

compatibilityWithLerayEnergyLedger :
  OptionBOpenGateLedgerEntry
compatibilityWithLerayEnergyLedger =
  optionBOpenGateLedgerEntry
    compatibilityWithLerayEnergy
    openAfterSprint94
    false
    refl
    "Open gate: show the proposed cascade is compatible with the Leray energy inequality and finite-energy evolution."

exclusionOfConditionalKStarLowerBoundLedger :
  OptionBOpenGateLedgerEntry
exclusionOfConditionalKStarLowerBoundLedger =
  optionBOpenGateLedgerEntry
    exclusionOfConditionalKStarLowerBound
    openAfterSprint94
    false
    refl
    "Open gate: exclude the Sprint 94 conditional K* lower-bound criterion on the intended blowup trajectory."

finiteTimeSingularityExtractionLedger :
  OptionBOpenGateLedgerEntry
finiteTimeSingularityExtractionLedger =
  optionBOpenGateLedgerEntry
    finiteTimeSingularityExtraction
    openAfterSprint94
    false
    refl
    "Open gate: extract an actual finite-time singularity from the candidate cascade."

canonicalOptionBOpenGateLedger :
  List OptionBOpenGateLedgerEntry
canonicalOptionBOpenGateLedger =
  kStarCollapseMechanismLedger
  ∷ compatibilityWithLerayEnergyLedger
  ∷ exclusionOfConditionalKStarLowerBoundLedger
  ∷ finiteTimeSingularityExtractionLedger
  ∷ []

record KStarCollapseHypothesis : Set where
  constructor kStarCollapseHypothesis
  field
    kStarCollapseMechanismAvailable :
      Bool
    kStarCollapseMechanismAvailableIsFalse :
      kStarCollapseMechanismAvailable ≡ false
    sprint94ConditionalLowerBoundStillAvailableAsCriterion :
      Sprint94.optionCConditionalRegularityCriterionClosed ≡ true
    sprint94GeneralDataObstructionInherited :
      Sprint94.generalDataGateObstructedByKStarLowerBound ≡ true
    note :
      String

open KStarCollapseHypothesis public

canonicalKStarCollapseHypothesis :
  KStarCollapseHypothesis
canonicalKStarCollapseHypothesis =
  kStarCollapseHypothesis
    false
    refl
    refl
    refl
    "Sprint 95 records no K* collapse mechanism; Sprint 94's conditional lower-bound criterion and obstruction remain inherited."

record FiniteTimeBlowupMechanism : Set where
  constructor finiteTimeBlowupMechanism
  field
    cascadeCandidate :
      Bool
    cascadeCandidateIsRecorded :
      cascadeCandidate ≡ true
    finiteTimeSingularityExtracted :
      Bool
    finiteTimeSingularityExtractedIsFalse :
      finiteTimeSingularityExtracted ≡ false
    blowupConstructionClosedHere :
      Bool
    blowupConstructionClosedHereIsFalse :
      blowupConstructionClosedHere ≡ false
    note :
      String

open FiniteTimeBlowupMechanism public

canonicalFiniteTimeBlowupMechanism :
  FiniteTimeBlowupMechanism
canonicalFiniteTimeBlowupMechanism =
  finiteTimeBlowupMechanism
    true
    refl
    false
    refl
    false
    refl
    "A low-frequency cascade candidate is recorded for feasibility accounting, but no finite-time singularity is extracted."

record LowFrequencyCascadeCandidate : Set where
  constructor lowFrequencyCascadeCandidate
  field
    lowFrequencyRouteRecorded :
      Bool
    lowFrequencyRouteRecordedIsTrue :
      lowFrequencyRouteRecorded ≡ true
    compatibleWithLerayEnergy :
      Bool
    compatibleWithLerayEnergyIsFalse :
      compatibleWithLerayEnergy ≡ false
    excludesConditionalKStarLowerBound :
      Bool
    excludesConditionalKStarLowerBoundIsFalse :
      excludesConditionalKStarLowerBound ≡ false
    note :
      String

open LowFrequencyCascadeCandidate public

canonicalLowFrequencyCascadeCandidate :
  LowFrequencyCascadeCandidate
canonicalLowFrequencyCascadeCandidate =
  lowFrequencyCascadeCandidate
    true
    refl
    false
    refl
    false
    refl
    "The low-frequency cascade is only a candidate; Leray-energy compatibility and exclusion of the Sprint 94 K* lower bound remain open."

record SmoothFiniteEnergyInitialDataCompatibility : Set where
  constructor smoothFiniteEnergyInitialDataCompatibility
  field
    smoothInitialDataClassRecorded :
      Bool
    smoothInitialDataClassRecordedIsTrue :
      smoothInitialDataClassRecorded ≡ true
    finiteEnergyClassRecorded :
      Bool
    finiteEnergyClassRecordedIsTrue :
      finiteEnergyClassRecorded ≡ true
    compatibilityWithCandidateClosed :
      Bool
    compatibilityWithCandidateClosedIsFalse :
      compatibilityWithCandidateClosed ≡ false
    note :
      String

open SmoothFiniteEnergyInitialDataCompatibility public

canonicalSmoothFiniteEnergyInitialDataCompatibility :
  SmoothFiniteEnergyInitialDataCompatibility
canonicalSmoothFiniteEnergyInitialDataCompatibility =
  smoothFiniteEnergyInitialDataCompatibility
    true
    refl
    true
    refl
    false
    refl
    "Smooth finite-energy data are the required Clay class, but compatibility with the candidate cascade remains an open gate."

data Sprint95ClosedBookkeeping : Set where
  sprint94ObstructionBookkeepingInherited :
    Sprint95ClosedBookkeeping
  sprint94ConditionalCriterionBookkeepingInherited :
    Sprint95ClosedBookkeeping
  optionBFeasibilityGatesRecorded :
    Sprint95ClosedBookkeeping
  clayPromotionRecordedFalse :
    Sprint95ClosedBookkeeping

canonicalSprint95ClosedBookkeeping :
  List Sprint95ClosedBookkeeping
canonicalSprint95ClosedBookkeeping =
  sprint94ObstructionBookkeepingInherited
  ∷ sprint94ConditionalCriterionBookkeepingInherited
  ∷ optionBFeasibilityGatesRecorded
  ∷ clayPromotionRecordedFalse
  ∷ []

sprint95FeasibilityStatement : String
sprint95FeasibilityStatement =
  "Sprint 95 records Option B blowup feasibility gates after Sprint 94; it closes only bookkeeping and does not close a blowup construction."

record OptionBBlowupFeasibilityLedger : Set where
  constructor optionBBlowupFeasibilityLedger
  field
    gates :
      List OptionBBlowupFeasibilityGate
    gatesAreCanonical :
      gates ≡ canonicalOptionBBlowupFeasibilityGates
    openGateLedger :
      List OptionBOpenGateLedgerEntry
    openGateLedgerIsCanonical :
      openGateLedger ≡ canonicalOptionBOpenGateLedger
    kStarCollapse :
      KStarCollapseHypothesis
    kStarCollapseIsCanonical :
      kStarCollapse ≡ canonicalKStarCollapseHypothesis
    blowupMechanism :
      FiniteTimeBlowupMechanism
    blowupMechanismIsCanonical :
      blowupMechanism ≡ canonicalFiniteTimeBlowupMechanism
    lowFrequencyCascade :
      LowFrequencyCascadeCandidate
    lowFrequencyCascadeIsCanonical :
      lowFrequencyCascade ≡ canonicalLowFrequencyCascadeCandidate
    initialDataCompatibility :
      SmoothFiniteEnergyInitialDataCompatibility
    initialDataCompatibilityIsCanonical :
      initialDataCompatibility
      ≡ canonicalSmoothFiniteEnergyInitialDataCompatibility
    closedBookkeeping :
      List Sprint95ClosedBookkeeping
    closedBookkeepingIsCanonical :
      closedBookkeeping ≡ canonicalSprint95ClosedBookkeeping
    sprint94Obstruction :
      Sprint94.generalDataGateObstructedByKStarLowerBound ≡ true
    sprint94ConditionalCriterion :
      Sprint94.optionCConditionalRegularityCriterionClosed ≡ true
    sprint94OptionBStillOpen :
      Sprint94.optionBBlowupConstructionClosed ≡ false
    sprint94BlowupStillOpen :
      Sprint94.blowupConstructionClosed ≡ false
    sprint94NoClay :
      Sprint94.clayNavierStokesPromoted ≡ false
    kStarCollapseMechanismOpen :
      kStarCollapseMechanismClosed ≡ false
    compatibilityWithLerayEnergyOpen :
      compatibilityWithLerayEnergyClosed ≡ false
    exclusionOfConditionalKStarLowerBoundOpen :
      exclusionOfConditionalKStarLowerBoundClosed ≡ false
    finiteTimeSingularityExtractionOpen :
      finiteTimeSingularityExtractionClosed ≡ false
    blowupConstructionClosedHere :
      blowupConstructionClosed ≡ false
    clayPromotionClosedHere :
      clayNavierStokesPromoted ≡ false
    statement :
      String
    statementIsCanonical :
      statement ≡ sprint95FeasibilityStatement

open OptionBBlowupFeasibilityLedger public

canonicalOptionBBlowupFeasibilityLedger :
  OptionBBlowupFeasibilityLedger
canonicalOptionBBlowupFeasibilityLedger =
  optionBBlowupFeasibilityLedger
    canonicalOptionBBlowupFeasibilityGates
    refl
    canonicalOptionBOpenGateLedger
    refl
    canonicalKStarCollapseHypothesis
    refl
    canonicalFiniteTimeBlowupMechanism
    refl
    canonicalLowFrequencyCascadeCandidate
    refl
    canonicalSmoothFiniteEnergyInitialDataCompatibility
    refl
    canonicalSprint95ClosedBookkeeping
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    sprint95FeasibilityStatement
    refl

record NSSprint95OptionBBlowupFeasibilityLedger : Set where
  field
    sprint94ForkLedger :
      Sprint94.Sprint94KStarForkLedger
    sprint94ForkLedgerIsCanonical :
      sprint94ForkLedger ≡ Sprint94.canonicalSprint94KStarForkLedger
    sprint94ObstructionInherited :
      Sprint94.generalDataGateObstructedByKStarLowerBound ≡ true
    sprint94ConditionalCriterionInherited :
      Sprint94.optionCConditionalRegularityCriterionClosed ≡ true
    sprint94OptionBStillOpen :
      Sprint94.optionBBlowupConstructionClosed ≡ false
    sprint94NoClay :
      Sprint94.clayNavierStokesPromoted ≡ false

    feasibilityLedger :
      OptionBBlowupFeasibilityLedger
    feasibilityLedgerIsCanonical :
      feasibilityLedger ≡ canonicalOptionBBlowupFeasibilityLedger
    openGates :
      List OptionBBlowupFeasibilityGate
    openGatesAreCanonical :
      openGates ≡ canonicalOptionBBlowupFeasibilityGates
    openGateLedger :
      List OptionBOpenGateLedgerEntry
    openGateLedgerIsCanonical :
      openGateLedger ≡ canonicalOptionBOpenGateLedger

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    blowupConstructionClosedIsFalse :
      blowupConstructionClosed ≡ false
    optionBBlowupConstructionClosedIsFalse :
      optionBBlowupConstructionClosed ≡ false
    exactOpenGateLedger :
      (kStarCollapseMechanismClosed ≡ false)
      × (compatibilityWithLerayEnergyClosed ≡ false)
      × (exclusionOfConditionalKStarLowerBoundClosed ≡ false)
      × (finiteTimeSingularityExtractionClosed ≡ false)

open NSSprint95OptionBBlowupFeasibilityLedger public

canonicalNSSprint95OptionBBlowupFeasibilityLedger :
  NSSprint95OptionBBlowupFeasibilityLedger
canonicalNSSprint95OptionBBlowupFeasibilityLedger =
  record
    { sprint94ForkLedger =
        Sprint94.canonicalSprint94KStarForkLedger
    ; sprint94ForkLedgerIsCanonical =
        refl
    ; sprint94ObstructionInherited =
        refl
    ; sprint94ConditionalCriterionInherited =
        refl
    ; sprint94OptionBStillOpen =
        refl
    ; sprint94NoClay =
        refl
    ; feasibilityLedger =
        canonicalOptionBBlowupFeasibilityLedger
    ; feasibilityLedgerIsCanonical =
        refl
    ; openGates =
        canonicalOptionBBlowupFeasibilityGates
    ; openGatesAreCanonical =
        refl
    ; openGateLedger =
        canonicalOptionBOpenGateLedger
    ; openGateLedgerIsCanonical =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; blowupConstructionClosedIsFalse =
        refl
    ; optionBBlowupConstructionClosedIsFalse =
        refl
    ; exactOpenGateLedger =
        refl , refl , refl , refl
    }

canonicalNSSprint95OptionBBlowupFeasibilityReceipt :
  NSSprint95OptionBBlowupFeasibilityLedger
canonicalNSSprint95OptionBBlowupFeasibilityReceipt =
  canonicalNSSprint95OptionBBlowupFeasibilityLedger

canonicalSprint95Flags :
  (clayNavierStokesPromoted ≡ false)
  × (blowupConstructionClosed ≡ false)
  × (optionBBlowupConstructionClosed ≡ false)
  × (kStarCollapseMechanismClosed ≡ false)
  × (compatibilityWithLerayEnergyClosed ≡ false)
  × (exclusionOfConditionalKStarLowerBoundClosed ≡ false)
  × (finiteTimeSingularityExtractionClosed ≡ false)
canonicalSprint95Flags =
  refl , refl , refl , refl , refl , refl , refl
