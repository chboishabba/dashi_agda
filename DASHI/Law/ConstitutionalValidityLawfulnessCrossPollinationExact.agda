module DASHI.Law.ConstitutionalValidityLawfulnessCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Law.CoerciveEncounterLawfulnessBidiExact as Law
import DASHI.Law.CoerciveEncounterLawfulnessProductExact as Product
import DASHI.Law.JarrettPostBondiConstitutionalSourceReceiptsExact as Jarrett
import DASHI.Governance.AuthorityPhaseSeparationExact as Phase

------------------------------------------------------------------------
-- Constitutional validity is an additional proof coordinate on top of the
-- existing lawfulness product.  We wrap rather than mutate the older owner so
-- existing consumers keep their constructor surface while stronger consumers
-- can demand validity closure.
------------------------------------------------------------------------

data ConstitutionalValidityState : Set where
  constitutionallyValid constitutionallyInvalid validityUnresolved : ConstitutionalValidityState

record ConstitutionalValidityReceipt : Set where
  constructor constitutionalValidityReceipt
  field
    validityState : ConstitutionalValidityState
    validityReference : String
    sourceRole : Jarrett.LegalSourceRole

open ConstitutionalValidityReceipt public

record ApplicableLawReceipt : Set where
  constructor applicableLawReceipt
  field
    enactmentReference : String
    jurisdictionReference : String
    temporalApplicabilityReference : String

record ConstitutionallyLawfulEdge (edge : Law.LegalTransitionFibre) : Set where
  constructor constitutionallyLawfulEdge
  field
    applicableLaw : ApplicableLawReceipt
    constitutionalValidity : ConstitutionalValidityReceipt
    constitutionalValidityClosed : validityState constitutionalValidity ≡ constitutionallyValid
    ordinaryLawfulness : Product.LawfulEdge edge
    extendedReference : String

open ConstitutionallyLawfulEdge public

------------------------------------------------------------------------
-- BIDI coordinate extension.
------------------------------------------------------------------------

data ExtendedLawfulnessCoordinate : Set where
  applicableLawCoordinate
  constitutionalValidityCoordinate
  ordinaryLawfulnessCoordinate : ExtendedLawfulnessCoordinate

data ExtendedCoordinateState : Set where
  extendedClosed extendedOpen : ExtendedCoordinateState

record ExtendedLawfulnessVector : Set where
  constructor extendedLawfulnessVector
  field
    applicableLawState : ExtendedCoordinateState
    validityStateClosed : ExtendedCoordinateState
    ordinaryLawfulnessState : ExtendedCoordinateState

open ExtendedLawfulnessVector public

data ExtendedLawfulnessResult : Set where
  extendedLawfulnessClosed : ExtendedLawfulnessResult
  firstOpenExtendedCoordinate : ExtendedLawfulnessCoordinate → ExtendedLawfulnessResult

firstOpenExtendedLawfulness : ExtendedLawfulnessVector → ExtendedLawfulnessResult
firstOpenExtendedLawfulness v with applicableLawState v
... | extendedOpen = firstOpenExtendedCoordinate applicableLawCoordinate
... | extendedClosed with validityStateClosed v
...   | extendedOpen = firstOpenExtendedCoordinate constitutionalValidityCoordinate
...   | extendedClosed with ordinaryLawfulnessState v
...     | extendedOpen = firstOpenExtendedCoordinate ordinaryLawfulnessCoordinate
...     | extendedClosed = extendedLawfulnessClosed

jarrettShapeVector : ExtendedLawfulnessVector
jarrettShapeVector = extendedLawfulnessVector extendedClosed extendedOpen extendedOpen

jarrettShapeStopsAtConstitutionalValidity :
  firstOpenExtendedLawfulness jarrettShapeVector
  ≡ firstOpenExtendedCoordinate constitutionalValidityCoordinate
jarrettShapeStopsAtConstitutionalValidity = refl

------------------------------------------------------------------------
-- Court-held invalidity regression.  This records the source role and exact
-- proposition boundary without pretending to instantiate a specific Herzog
-- encounter or decide every police act/charge.
------------------------------------------------------------------------

jarrettInvalidityReceipt : ConstitutionalValidityReceipt
jarrettInvalidityReceipt = constitutionalValidityReceipt
  constitutionallyInvalid
  "Jarrett v State of New South Wales [2026] NSWCA 62: impugned PARD scheme provisions declared invalid"
  Jarrett.courtHolding

record InvalidAuthorityProducerWitness : Set where
  constructor invalidAuthorityProducerWitness
  field
    enactedTextExists : Bool
    enactedTextExistsIsTrue : enactedTextExists ≡ true
    constitutionalState : ConstitutionalValidityState
    constitutionalStateIsInvalid : constitutionalState ≡ constitutionallyInvalid
    courtHoldingReceipt : Jarrett.LegalSourceReceipt

open InvalidAuthorityProducerWitness public

canonicalJarrettInvalidProducer : InvalidAuthorityProducerWitness
canonicalJarrettInvalidProducer = invalidAuthorityProducerWitness
  true refl
  constitutionallyInvalid refl
  Jarrett.jarrettInvalidityHolding

------------------------------------------------------------------------
-- Authority-phase cross-pollination: even where some authority surface exists,
-- phase-specific role remains non-factorable, and validity is a further axis.
------------------------------------------------------------------------

record ValidityPhaseAuthorityFibre : Set where
  constructor validityPhaseAuthorityFibre
  field
    validity : ConstitutionalValidityState
    phase : Phase.InterventionPhase
    phaseRole : Phase.PhaseAuthorityRole
    phaseRoleExact : phaseRole ≡ Phase.phaseAuthorityRole phase
    fibreReference : String

open ValidityPhaseAuthorityFibre public

responseValidAuthority : ValidityPhaseAuthorityFibre
responseValidAuthority = validityPhaseAuthorityFibre
  constitutionallyValid
  Phase.responsePhase
  Phase.responseAuthorityRole
  refl
  "synthetic valid response-phase authority"

repairValidAuthority : ValidityPhaseAuthorityFibre
repairValidAuthority = validityPhaseAuthorityFibre
  constitutionallyValid
  Phase.repairPhase
  Phase.repairAuthorityRole
  refl
  "synthetic valid repair-phase authority"

phaseDifferenceSurvivesEqualValidity :
  phaseRole responseValidAuthority ≡ phaseRole repairValidAuthority → ⊥
phaseDifferenceSurvivesEqualValidity ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

record ConstitutionalLawfulnessBoundary : Set where
  constructor constitutionalLawfulnessBoundary
  field
    enactedTextImpliesConstitutionalValidity : Bool
    enactedTextImpliesConstitutionalValidityIsFalse : enactedTextImpliesConstitutionalValidity ≡ false
    constitutionalValidityAloneImpliesLawfulExercise : Bool
    constitutionalValidityAloneImpliesLawfulExerciseIsFalse : constitutionalValidityAloneImpliesLawfulExercise ≡ false
    invalidOnePowerImpliesNoOtherAuthorityCouldExist : Bool
    invalidOnePowerImpliesNoOtherAuthorityCouldExistIsFalse : invalidOnePowerImpliesNoOtherAuthorityCouldExist ≡ false
    coarseAuthoritySurfaceDeterminesPhaseAndValidity : Bool
    coarseAuthoritySurfaceDeterminesPhaseAndValidityIsFalse : coarseAuthoritySurfaceDeterminesPhaseAndValidity ≡ false

canonicalConstitutionalLawfulnessBoundary : ConstitutionalLawfulnessBoundary
canonicalConstitutionalLawfulnessBoundary =
  constitutionalLawfulnessBoundary false refl false refl false refl false refl
