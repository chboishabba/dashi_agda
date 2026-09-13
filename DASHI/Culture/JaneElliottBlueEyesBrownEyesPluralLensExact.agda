module DASHI.Culture.JaneElliottBlueEyesBrownEyesPluralLensExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Core.SnowballPluralLensInvariantExact as Snow
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query

------------------------------------------------------------------------
-- JANE ELLIOTT BLUE-EYES / BROWN-EYES EXERCISE
--
-- Source boundary:
--   Jane Elliott's classroom exercise is represented as a pedagogical/social
--   intervention about arbitrary classification, authority and discrimination.
--   It is not promoted to a definitive experimental model of racism.
--
-- Program-evaluation source:
--   Stewart et al. (2003), "Do the Eyes Have It? A Program Evaluation of Jane
--   Elliott's Blue-Eyes/Brown-Eyes Diversity Training Exercise",
--   Journal of Applied Social Psychology 33(9):1898-1921.
--   DOI 10.1111/j.1559-1816.2003.tb02086.x.
------------------------------------------------------------------------

data ElliottAxis : Set where
  assignedCategory : ElliottAxis
  authorityBacking : ElliottAxis
  privilegeRestriction : ElliottAxis
  peerTreatment : ElliottAxis
  taskPerformance : ElliottAxis
  affect : ElliottAxis
  consentSafeguard : ElliottAxis
  historicalRacism : ElliottAxis
  institutionalStructure : ElliottAxis
  debriefRepair : ElliottAxis

relevantAxis : ElliottAxis → Bool
relevantAxis axis = true

retainedAxis : ElliottAxis → Bool
retainedAxis axis = true

elliottLens : Snow.PluralLens ElliottAxis
elliottLens = Snow.plural-lens relevantAxis retainedAxis (λ axis eq → eq)

record ElliottExerciseBoundary : Set where
  constructor elliott-exercise-boundary
  field
    arbitraryClassifierCanAcquireSocialForce : Bool
    authorityCanAmplifyClassifier : Bool
    treatmentCanAlterObservedPerformance : Bool
    exerciseEqualsRacism : Bool
    eyeColourBiologicallyExplainsHierarchy : Bool
    classroomEffectAutomaticallyGeneralises : Bool
    ethicalSafeguardsAreIrrelevant : Bool
    historicalAndInstitutionalRacismMustRemainSeparateAxes : Bool
open ElliottExerciseBoundary public

canonicalElliottExerciseBoundary : ElliottExerciseBoundary
canonicalElliottExerciseBoundary = elliott-exercise-boundary
  true true true false false false false true

-- A coarse observer that remembers only assigned eye-colour group cannot recover
-- the complete situated state when authority/treatment/history differ.

data DemoState : Set where
  sameGroupLowPower : DemoState
  sameGroupHighPower : DemoState

data DemoGroup : Set where sameGroup : DemoGroup
data DemoOutcome : Set where lowConstraint highConstraint : DemoOutcome

groupObserver : DemoState → DemoGroup
groupObserver state = sameGroup

constraintOutcome : DemoState → DemoOutcome
constraintOutcome sameGroupLowPower = lowConstraint
constraintOutcome sameGroupHighPower = highConstraint

groupCannotRecoverPowerRelation : INF.FactorsThrough groupObserver constraintOutcome → ⊥
groupCannotRecoverPowerRelation factor =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness sameGroupLowPower sameGroupHighPower refl (λ ()))
    factor

record TwoEyedReading : Set where
  constructor two-eyed-reading
  field
    firstEye : String
    secondEye : String
    sharedSurfaceDoesNotFuseHistories : Bool
    secondEyeIsNotFinalGodsEye : Bool
open TwoEyedReading public

elliottTwoEyedReading : TwoEyedReading
elliottTwoEyedReading = two-eyed-reading
  "participant-visible arbitrary category and treatment"
  "historical/institutional racism, authority, consent, affect and repair context"
  true true

data ElliottExerciseProvesRacismEquivalent : Set where
data AssignedCategoryCreatesNaturalDifference : Set where
data RoleReversalRepairsAllHarm : Set where

exerciseDoesNotProveRacismEquivalent : ElliottExerciseProvesRacismEquivalent → ⊥
exerciseDoesNotProveRacismEquivalent ()
assignedCategoryDoesNotCreateNaturalDifference : AssignedCategoryCreatesNaturalDifference → ⊥
assignedCategoryDoesNotCreateNaturalDifference ()
roleReversalDoesNotGuaranteeRepair : RoleReversalRepairsAllHarm → ⊥
roleReversalDoesNotGuaranteeRepair ()
