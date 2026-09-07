module DASHI.Core.AdmissibleCounterfactualWorldFamilyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.CounterfactualModelContractExact as Counterfactual

------------------------------------------------------------------------
-- ADMISSIBLE COUNTERFACTUAL WORLD FAMILY
--
-- DASHI-original reusable refinement of CounterfactualModelContractExact.
--
-- The causal object is not an arbitrary imagined world and not merely an event
-- with one token deleted.  A world must separately pay admissibility, corrected
-- intervention/relation, held-fixed justification and comparison geometry.
-- Multiple admissible corrected worlds can still disagree on the outcome; that
-- disagreement is retained as underidentification rather than silently choosing
-- one preferred world.
------------------------------------------------------------------------

data WorldAdmissibilityStatus : Set where
  admissibleWorld
  inadmissibleWorld
  admissibilityUnresolved
  : WorldAdmissibilityStatus

data CorrectionKind : Set where
  correctedConduct
  correctedInstitutionalRelation
  correctedPhysicalIntervention
  correctedPolicyRegime
  correctedBoundaryCondition
  unresolvedCorrection
  : CorrectionKind

data CounterfactualIdentificationStatus : Set where
  uniquelyIdentifiedAcrossAdmissibleWorlds
  underidentifiedAcrossAdmissibleWorlds
  noAdmissibleWorldLocated
  identificationUnresolved
  : CounterfactualIdentificationStatus

record AdmissibleWorldFamily : Set₁ where
  constructor admissible-world-family
  field
    World Outcome : Set
    observedWorld : World
    candidateWorlds : List World
    admissibility : World → WorldAdmissibilityStatus
    correctionKind : World → CorrectionKind
    correctedRelationReceipt : World → Set
    heldFixedJustificationReceipt : World → Set
    comparisonAlignmentReceipt : World → Set
    outcome : World → Outcome
    sourceReference : String
    familyMeaning : String

open AdmissibleWorldFamily public

record AdmissibleCorrectedWorld (family : AdmissibleWorldFamily) : Set where
  constructor admissible-corrected-world
  field
    world : World family
    admissibilityExact : admissibility family world ≡ admissibleWorld
    correctionNotMerelyDeletedEvent : Set
    correctedRelation : correctedRelationReceipt family world
    heldFixedJustified : heldFixedJustificationReceipt family world
    comparisonAligned : comparisonAlignmentReceipt family world

open AdmissibleCorrectedWorld public

record OutcomeDisagreementWitness (family : AdmissibleWorldFamily) : Set where
  constructor outcome-disagreement-witness
  field
    left right : AdmissibleCorrectedWorld family
    outcomesDiffer :
      outcome family (world left) ≡ outcome family (world right) → ⊥

open OutcomeDisagreementWitness public

record OutcomeAgreementReceipt (family : AdmissibleWorldFamily) : Set₁ where
  constructor outcome-agreement-receipt
  field
    canonicalOutcome : Outcome family
    everyAdmissibleCorrectedWorldAgrees :
      (worldReceipt : AdmissibleCorrectedWorld family) →
      outcome family (world worldReceipt) ≡ canonicalOutcome

open OutcomeAgreementReceipt public

identificationFromAgreement :
  (family : AdmissibleWorldFamily) →
  OutcomeAgreementReceipt family →
  CounterfactualIdentificationStatus
identificationFromAgreement family receipt = uniquelyIdentifiedAcrossAdmissibleWorlds

identificationFromDisagreement :
  (family : AdmissibleWorldFamily) →
  OutcomeDisagreementWitness family →
  CounterfactualIdentificationStatus
identificationFromDisagreement family witness = underidentifiedAcrossAdmissibleWorlds

------------------------------------------------------------------------
-- A corrected relation is stronger than removing an event label.
------------------------------------------------------------------------

data EventDeletionOnly : Set where eventDeletionOnly : EventDeletionOnly
data CorrectedRelationSpecified : Set where correctedRelationSpecified : CorrectedRelationSpecified

data EventDeletionAloneSuppliesCorrectedRelation : Set where

eventDeletionAloneDoesNotSupplyCorrectedRelation :
  EventDeletionAloneSuppliesCorrectedRelation → ⊥
eventDeletionAloneDoesNotSupplyCorrectedRelation ()

------------------------------------------------------------------------
-- Cross-domain promotion firewalls.
------------------------------------------------------------------------

data CausalDependence : Set where causalDependenceEstablished : CausalDependence
data LiabilityConclusion : Set where liabilityConclusion : LiabilityConclusion
data LegitimacyConclusion : Set where legitimacyConclusion : LegitimacyConclusion
data RemedyConclusion : Set where remedyConclusion : RemedyConclusion
data AuthorityConclusion : Set where authorityConclusion : AuthorityConclusion

data CausalDependenceAutomaticallyCreatesLiability : Set where
data CausalDependenceAutomaticallyCreatesLegitimacy : Set where
data CausalDependenceAutomaticallyCreatesRemedy : Set where
data CausalDependenceAutomaticallyCreatesAuthority : Set where

causalDependenceDoesNotAutoCreateLiability :
  CausalDependenceAutomaticallyCreatesLiability → ⊥
causalDependenceDoesNotAutoCreateLiability ()

causalDependenceDoesNotAutoCreateLegitimacy :
  CausalDependenceAutomaticallyCreatesLegitimacy → ⊥
causalDependenceDoesNotAutoCreateLegitimacy ()

causalDependenceDoesNotAutoCreateRemedy :
  CausalDependenceAutomaticallyCreatesRemedy → ⊥
causalDependenceDoesNotAutoCreateRemedy ()

causalDependenceDoesNotAutoCreateAuthority :
  CausalDependenceAutomaticallyCreatesAuthority → ⊥
causalDependenceDoesNotAutoCreateAuthority ()

------------------------------------------------------------------------
-- Existing single-world counterfactual contract remains upstream-compatible.
------------------------------------------------------------------------

baseCounterfactualBoundary : Counterfactual.CounterfactualBoundary
baseCounterfactualBoundary = Counterfactual.canonicalCounterfactualBoundary

arbitraryAlternativeStillNotCausalCounterfactual :
  Counterfactual.arbitraryAlternativeIsCausalCounterfactual baseCounterfactualBoundary ≡ false
arbitraryAlternativeStillNotCausalCounterfactual = refl

------------------------------------------------------------------------
-- TSFV/physics-compatible realisation boundary, stated generically.
------------------------------------------------------------------------

data CounterfactualTheoryPoint : Set where counterfactualTheoryPoint : CounterfactualTheoryPoint
data PhysicallyRealisedAlternative : Set where physicallyRealisedAlternative : PhysicallyRealisedAlternative

data TheoryPointAutomaticallyRealised : Set where

theoryPointDoesNotAutoBecomeRealisedWorld : TheoryPointAutomaticallyRealised → ⊥
theoryPointDoesNotAutoBecomeRealisedWorld ()

record AdmissibleCounterfactualBoundary : Set where
  constructor admissible-counterfactual-boundary
  field
    arbitraryImaginationCountsAsAdmissibleWorld : Bool
    arbitraryImaginationCountsAsAdmissibleWorldIsFalse :
      arbitraryImaginationCountsAsAdmissibleWorld ≡ false
    deletingObservedEventIsEnoughCorrection : Bool
    deletingObservedEventIsEnoughCorrectionIsFalse :
      deletingObservedEventIsEnoughCorrection ≡ false
    multipleAdmissibleWorldsMayUnderidentifyOutcome : Bool
    multipleAdmissibleWorldsMayUnderidentifyOutcomeIsTrue :
      multipleAdmissibleWorldsMayUnderidentifyOutcome ≡ true
    causalIdentificationEqualsLiability : Bool
    causalIdentificationEqualsLiabilityIsFalse :
      causalIdentificationEqualsLiability ≡ false
    legalAdmissibilityEqualsPhysicalRealisation : Bool
    legalAdmissibilityEqualsPhysicalRealisationIsFalse :
      legalAdmissibilityEqualsPhysicalRealisation ≡ false

canonicalAdmissibleCounterfactualBoundary : AdmissibleCounterfactualBoundary
canonicalAdmissibleCounterfactualBoundary =
  admissible-counterfactual-boundary
    false refl
    false refl
    true refl
    false refl
    false refl
