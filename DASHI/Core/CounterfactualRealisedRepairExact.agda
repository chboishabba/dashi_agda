module DASHI.Core.CounterfactualRealisedRepairExact where

------------------------------------------------------------------------
-- COUNTERFACTUAL REALISED REPAIR
--
-- Generic DASHI owner cross-pollinated with the legal but-for programme via
-- CounterfactualModelContractExact.  This module is not itself a tort/statutory
-- factual-causation doctrine.  It asks whether an admissible corrected-world
-- fibre would realise a declared terminal repair outcome.
--
-- Key discipline inherited from the but-for lane:
--   * correct the relevant relation/conduct; do not merely delete a label/event;
--   * declare changed and held-fixed coordinates;
--   * distinguish robust, selected-world and underidentified counterfactuals;
--   * counterfactual dependence does not by itself create liability, legitimacy,
--     political authority or remedial sufficiency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.CounterfactualModelContractExact as Counterfactual

------------------------------------------------------------------------
-- Positive correction meaning: deletion alone is not a sufficient intervention.
------------------------------------------------------------------------

record CorrectiveInterventionMeaning : Set where
  constructor corrective-intervention-meaning
  field
    observedRelation : String
    correctedRelation : String
    changedRelationReference : String
    correctionIsMereDeletion : Bool
    correctionIsMereDeletionIsFalse : correctionIsMereDeletion ≡ false
    correctedRelationAddsPositiveStructure : Bool
    correctedRelationAddsPositiveStructureIsTrue :
      correctedRelationAddsPositiveStructure ≡ true

open CorrectiveInterventionMeaning public

------------------------------------------------------------------------
-- Fibre of admissible corrected worlds.
------------------------------------------------------------------------

record CorrectedWorldFibre : Set₁ where
  constructor corrected-world-fibre
  field
    World Outcome : Set
    admissibleCorrectedWorld : World → Set
    realisedOutcome : World → Outcome
    AcceptableOutcome : Outcome → Set
    interventionMeaning : CorrectiveInterventionMeaning
    sourceReference : String
    consumerReference : String

open CorrectedWorldFibre public

record RobustRealisedRepairReceipt (fibre : CorrectedWorldFibre) : Set₁ where
  constructor robust-realised-repair-receipt
  field
    everyAdmissibleCorrectedWorldRepairs :
      (world : World fibre) →
      admissibleCorrectedWorld fibre world →
      AcceptableOutcome fibre (realisedOutcome fibre world)

open RobustRealisedRepairReceipt public

record SelectedRealisedRepairReceipt (fibre : CorrectedWorldFibre) : Set₁ where
  constructor selected-realised-repair-receipt
  field
    selectedWorld : World fibre
    selectedWorldAdmissible : admissibleCorrectedWorld fibre selectedWorld
    selectedOutcomeAcceptable : AcceptableOutcome fibre (realisedOutcome fibre selectedWorld)
    selectionJustification : Set
    selectionReference : String

open SelectedRealisedRepairReceipt public

record CounterfactualRepairUnderidentification (fibre : CorrectedWorldFibre) : Set₁ where
  constructor counterfactual-repair-underidentification
  field
    repairingWorld nonRepairingWorld : World fibre
    repairingWorldAdmissible : admissibleCorrectedWorld fibre repairingWorld
    nonRepairingWorldAdmissible : admissibleCorrectedWorld fibre nonRepairingWorld
    repairingWorldRepairs : AcceptableOutcome fibre (realisedOutcome fibre repairingWorld)
    nonRepairingWorldDoesNotRepair :
      AcceptableOutcome fibre (realisedOutcome fibre nonRepairingWorld) → ⊥

open CounterfactualRepairUnderidentification public

------------------------------------------------------------------------
-- Status is consumer-relative.  Source/application modules decide which
-- receipt, if any, is available.
------------------------------------------------------------------------

data CounterfactualRepairStatus : Set where
  robustRepairIdentified : CounterfactualRepairStatus
  selectedRepairOnly : CounterfactualRepairStatus
  counterfactualRepairUnderidentified : CounterfactualRepairStatus
  causalIdentificationNotYetPaid : CounterfactualRepairStatus


------------------------------------------------------------------------
-- Compatibility with the generic counterfactual contract.
------------------------------------------------------------------------

record RealisedRepairCounterfactualContract : Set₁ where
  constructor realised-repair-counterfactual-contract
  field
    counterfactualContract : Counterfactual.CounterfactualContract
    correctionMeaning : CorrectiveInterventionMeaning
    legalButForDoctrineImportedByThisOwner : Bool
    legalButForDoctrineImportedByThisOwnerIsFalse :
      legalButForDoctrineImportedByThisOwner ≡ false
    structuralDiagnosisEqualsLegalFactualCausation : Bool
    structuralDiagnosisEqualsLegalFactualCausationIsFalse :
      structuralDiagnosisEqualsLegalFactualCausation ≡ false
    effectiveRemedyRealisationEqualsLegalFactualCausation : Bool
    effectiveRemedyRealisationEqualsLegalFactualCausationIsFalse :
      effectiveRemedyRealisationEqualsLegalFactualCausation ≡ false
    compatibilityReference : String

open RealisedRepairCounterfactualContract public

------------------------------------------------------------------------
-- Reverse-search obligations.
------------------------------------------------------------------------

data CounterfactualRepairNeed : Set where
  acquireAdmissibleCorrectedWorlds : CounterfactualRepairNeed
  acquireHeldFixedJustification : CounterfactualRepairNeed
  acquireOutcomeComparison : CounterfactualRepairNeed
  acquireCausalIdentification : CounterfactualRepairNeed
  acquireAffectedCommunityOutcomeReceipt : CounterfactualRepairNeed
  acquireIndependentComparatorReceipt : CounterfactualRepairNeed


------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record CounterfactualRealisedRepairBoundary : Set where
  constructor counterfactual-realised-repair-boundary
  field
    deletingHarmfulLabelEqualsPositiveRelationCorrection : Bool
    deletingHarmfulLabelEqualsPositiveRelationCorrectionIsFalse :
      deletingHarmfulLabelEqualsPositiveRelationCorrection ≡ false
    oneSuccessfulSelectedWorldProvesRobustRepair : Bool
    oneSuccessfulSelectedWorldProvesRobustRepairIsFalse :
      oneSuccessfulSelectedWorldProvesRobustRepair ≡ false
    underidentificationMeansNoCausalEffect : Bool
    underidentificationMeansNoCausalEffectIsFalse :
      underidentificationMeansNoCausalEffect ≡ false
    counterfactualOutcomeDifferenceCreatesLiability : Bool
    counterfactualOutcomeDifferenceCreatesLiabilityIsFalse :
      counterfactualOutcomeDifferenceCreatesLiability ≡ false
    counterfactualOutcomeDifferenceProvesLegitimacy : Bool
    counterfactualOutcomeDifferenceProvesLegitimacyIsFalse :
      counterfactualOutcomeDifferenceProvesLegitimacy ≡ false
    institutionalSelfReportDefinesAcceptableOutcome : Bool
    institutionalSelfReportDefinesAcceptableOutcomeIsFalse :
      institutionalSelfReportDefinesAcceptableOutcome ≡ false
    causalIdentificationMustBeSeparatelyPaid : Bool
    causalIdentificationMustBeSeparatelyPaidIsTrue :
      causalIdentificationMustBeSeparatelyPaid ≡ true

open CounterfactualRealisedRepairBoundary public

canonicalCounterfactualRealisedRepairBoundary : CounterfactualRealisedRepairBoundary
canonicalCounterfactualRealisedRepairBoundary = counterfactual-realised-repair-boundary
  false refl
  false refl
  false refl
  false refl
  false refl
  false refl
  true refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data DeleteDoctrineThereforeRepair : Set where
data SelectedWorldThereforeRobust : Set where
data StructuralCounterfactualThereforeLegalLiability : Set where
data CommunityOutcomeThereforeEpistemicFusion : Set where

deleteDoctrineDoesNotByItselfRealiseRepair : DeleteDoctrineThereforeRepair → ⊥
deleteDoctrineDoesNotByItselfRealiseRepair ()

selectedWorldDoesNotByItselfProveRobustness : SelectedWorldThereforeRobust → ⊥
selectedWorldDoesNotByItselfProveRobustness ()

structuralCounterfactualDoesNotCreateLegalLiability :
  StructuralCounterfactualThereforeLegalLiability → ⊥
structuralCounterfactualDoesNotCreateLegalLiability ()

communityOutcomeDoesNotFuseEpistemologies : CommunityOutcomeThereforeEpistemicFusion → ⊥
communityOutcomeDoesNotFuseEpistemologies ()
