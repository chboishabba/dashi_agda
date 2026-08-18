module DASHI.Governance.EvolvingCapacityReligiousAutonomyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.DependentAuthorityCoercionKernel as Coercion
import DASHI.Governance.DevelopmentalAgencyState as Agency

------------------------------------------------------------------------
-- SOURCE CALIBRATION
--
-- United Nations General Assembly,
-- "Convention on the Rights of the Child" (1989), Articles 1, 5, 12 and 14.
-- Treaty source; no DOI asserted.
--
-- Article 1 supplies the under-18 child-status boundary (subject to earlier
-- majority under applicable law). Articles 5, 12 and 14 supply the relevant
-- evolving-capacities / participation / thought-conscience-religion structure.
-- They do NOT impose a universal rule that religious exposure is prohibited
-- until age 18, nor a single fixed "age of reason" threshold.
------------------------------------------------------------------------

record ChildRightsSource : Set where
  constructor childRightsSource
  field
    authorInstitution : String
    title : String
    identifier : String
    boundedRole : String

crc1989Source : ChildRightsSource
crc1989Source =
  childRightsSource
    "United Nations General Assembly"
    "Convention on the Rights of the Child"
    "1989; Articles 1, 5, 12, 14"
    "under-18 child status plus evolving-capacity, participation, and freedom-of-thought/conscience/religion vocabulary; no age-18 ban on formation"

------------------------------------------------------------------------
-- A developmental autonomy trajectory is capacity-relative rather than a
-- birthday switch. Parental/caregiver direction and the child's own exercise
-- of rights are represented as distinct coordinates.
------------------------------------------------------------------------

record ReligiousAutonomyState : Set where
  constructor religiousAutonomyState
  field
    developmental : Coercion.DevelopmentalState
    agency : Agency.DevelopmentalAgency
    guidanceMagnitude : Nat
    independentAlternativeAccess : Nat
    refusalCapacity : Nat
    recognisedChildVoice : Nat
    practicalExitCapacity : Nat

record EvolvingCapacityTransition
    (earlier later : ReligiousAutonomyState) : Set where
  constructor evolvingCapacityTransition
  field
    cognitiveCapacityNondecreasing :
      Coercion.cognitiveCapacity (ReligiousAutonomyState.developmental earlier)
      ≤ Coercion.cognitiveCapacity (ReligiousAutonomyState.developmental later)
    informationalIndependenceNondecreasing :
      Coercion.informationalIndependence (ReligiousAutonomyState.developmental earlier)
      ≤ Coercion.informationalIndependence (ReligiousAutonomyState.developmental later)
    refusalCapacityNondecreasing :
      ReligiousAutonomyState.refusalCapacity earlier
      ≤ ReligiousAutonomyState.refusalCapacity later
    recognisedVoiceNondecreasing :
      ReligiousAutonomyState.recognisedChildVoice earlier
      ≤ ReligiousAutonomyState.recognisedChildVoice later
    alternativeAccessNondecreasing :
      ReligiousAutonomyState.independentAlternativeAccess earlier
      ≤ ReligiousAutonomyState.independentAlternativeAccess later

------------------------------------------------------------------------
-- Fail-closed boundaries around the common age-18 misreading and around the
-- stronger claim actually relevant to the paper: formation begins before
-- substantial epistemic independence and must later be tested for reopening.
------------------------------------------------------------------------

data Under18MeansNoReligiousExposure : Set where

data ParentalGuidanceMeansOwnershipOfBelief : Set where

data EarlyReligiousExposureEstablishesCoercion : Set where

data EarlyFormationEstablishesEntrapment : Set where

under18DoesNotMeanNoReligiousExposure : Under18MeansNoReligiousExposure → ⊥
under18DoesNotMeanNoReligiousExposure ()

parentalGuidanceDoesNotMeanOwnershipOfBelief :
  ParentalGuidanceMeansOwnershipOfBelief → ⊥
parentalGuidanceDoesNotMeanOwnershipOfBelief ()

earlyReligiousExposureDoesNotEstablishCoercion :
  EarlyReligiousExposureEstablishesCoercion → ⊥
earlyReligiousExposureDoesNotEstablishCoercion ()

earlyFormationDoesNotEstablishEntrapment :
  EarlyFormationEstablishesEntrapment → ⊥
earlyFormationDoesNotEstablishEntrapment ()

record EvolvingCapacityReligiousAutonomyBoundary : Set where
  constructor evolvingCapacityReligiousAutonomyBoundary
  field
    under18ChildStatusRelevant : Bool
    fixedAge18ReligiousConsentSwitch : Bool
    fixedAgeOfReasonRequiredByFormalism : Bool
    formationBeforeEpistemicIndependenceRelevant : Bool
    laterAlternativeAccessRelevant : Bool
    laterRefusalCapacityRelevant : Bool
    laterRecognisedVoiceRelevant : Bool
    earlyFormationAloneEqualsCoercion : Bool

canonicalEvolvingCapacityReligiousAutonomyBoundary :
  EvolvingCapacityReligiousAutonomyBoundary
canonicalEvolvingCapacityReligiousAutonomyBoundary =
  evolvingCapacityReligiousAutonomyBoundary
    true false false true true true true false
