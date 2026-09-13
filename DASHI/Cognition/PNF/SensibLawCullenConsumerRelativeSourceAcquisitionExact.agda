module DASHI.Cognition.PNF.SensibLawCullenConsumerRelativeSourceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawConsumerSourceAcquisitionPriorityExact as Priority
import DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact as Atomic
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact as CullenCLA
import DASHI.Cognition.PNF.SensibLawCullenS43ASpecialStatutoryPowerAtomicExact as S43A
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Family
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilitySourceRealisationExact as Vicarious

------------------------------------------------------------------------
-- CULLEN CONSUMER-RELATIVE SOURCE ACQUISITION
--
-- Same unresolved coordinate, different consumer.  An upstream atomic failure
-- may block a coordinate for the actual-disposition consumer without deleting
-- that coordinate from counterfactual/source-completeness consumers.
------------------------------------------------------------------------

data CullenConsumer : Set where
  actualLiabilityDisposition : CullenConsumer
  counterfactualVicariousRouteIfTort : CullenConsumer
  counterfactualS43AStandardIfEngaged : CullenConsumer

data CullenSourceCoordinate : Set where
  exactS8VicariousSubroute : CullenSourceCoordinate
  s43ASpecialStandardApplication : CullenSourceCoordinate

data CullenLiveSensitive : CullenConsumer → CullenSourceCoordinate → Set where
  counterfactualNeedsS8Route :
    CullenLiveSensitive counterfactualVicariousRouteIfTort exactS8VicariousSubroute
  counterfactualNeedsS43AStandard :
    CullenLiveSensitive counterfactualS43AStandardIfEngaged s43ASpecialStandardApplication

data CullenCounterfactualSensitive : CullenConsumer → CullenSourceCoordinate → Set where
  actualConsumerHasS8Counterfactual :
    CullenCounterfactualSensitive actualLiabilityDisposition exactS8VicariousSubroute
  actualConsumerHasS43ACounterfactual :
    CullenCounterfactualSensitive actualLiabilityDisposition s43ASpecialStandardApplication

cullenSourcePolicy : Priority.ConsumerSourcePolicy
cullenSourcePolicy = Priority.consumer-source-policy
  CullenConsumer
  CullenSourceCoordinate
  CullenLiveSensitive
  CullenCounterfactualSensitive
  "Cullen source work is scheduled relative to the selected legal consumer; unresolved downstream coordinates do not automatically consume the actual-disposition search budget."

------------------------------------------------------------------------
-- Actual disposition: s 5B(1)(c) is a sourced -1 upstream blocker for the
-- precise vicarious subroute.  Learning route (a) versus route (b) cannot repair
-- the already-failed breach coordinate.
------------------------------------------------------------------------

actualS8SubrouteBlockedByBreach :
  Priority.UpstreamAtomicBlocker
    cullenSourcePolicy
    actualLiabilityDisposition
    exactS8VicariousSubroute
actualS8SubrouteBlockedByBreach = Priority.upstream-atomic-blocker
  CLA.reasonablePersonWouldTakePrecautions
  CullenCLA.cullenReasonablePrecautionsAtom
  refl
  (λ ())
  "Cullen joint reasons [42]-[48] source the s 5B(1)(c) failure. Resolving s 8(1)(a) versus s 8(1)(b) cannot establish the missing upstream breach element for the actual disposition consumer."

actualS8AcquisitionDisposition :
  Priority.SourceAcquisitionDisposition
    cullenSourcePolicy
    actualLiabilityDisposition
    exactS8VicariousSubroute
actualS8AcquisitionDisposition =
  Priority.blockedDownstream actualS8SubrouteBlockedByBreach

actualS8HasNoAcquireNowSensitivity :
  CullenLiveSensitive actualLiabilityDisposition exactS8VicariousSubroute → ⊥
actualS8HasNoAcquireNowSensitivity =
  Priority.blockedCoordinateHasNoLiveSensitivity actualS8SubrouteBlockedByBreach

------------------------------------------------------------------------
-- Actual disposition: s 43A engagement itself is -1, so the downstream s 43A
-- special unreasonableness standard is not a live acquisition target either.
------------------------------------------------------------------------

actualS43AStandardBlockedByNonEngagement :
  Priority.UpstreamAtomicBlocker
    cullenSourcePolicy
    actualLiabilityDisposition
    s43ASpecialStandardApplication
actualS43AStandardBlockedByNonEngagement = Priority.upstream-atomic-blocker
  S43A.liabilityBasedOnExerciseOfSpecialStatutoryPower
  S43A.cullenS43ABasedOnAtom
  refl
  (λ ())
  "The source-conditioned s 43A engagement atom is -1 on Cullen. The downstream s 43A(3) standard is therefore not a live requirement for the actual-disposition consumer."

actualS43AAcquisitionDisposition :
  Priority.SourceAcquisitionDisposition
    cullenSourcePolicy
    actualLiabilityDisposition
    s43ASpecialStandardApplication
actualS43AAcquisitionDisposition =
  Priority.blockedDownstream actualS43AStandardBlockedByNonEngagement

------------------------------------------------------------------------
-- Counterfactual consumers deliberately reopen those coordinates.
------------------------------------------------------------------------

counterfactualS8AcquisitionDisposition :
  Priority.SourceAcquisitionDisposition
    cullenSourcePolicy
    counterfactualVicariousRouteIfTort
    exactS8VicariousSubroute
counterfactualS8AcquisitionDisposition =
  Priority.acquireForLiveConsumer counterfactualNeedsS8Route

counterfactualS8AcquireNowPermission :
  Priority.AcquireNowPermission
    cullenSourcePolicy
    counterfactualVicariousRouteIfTort
    exactS8VicariousSubroute
counterfactualS8AcquireNowPermission =
  Priority.permissionFromLiveDisposition counterfactualNeedsS8Route

counterfactualS43AAcquisitionDisposition :
  Priority.SourceAcquisitionDisposition
    cullenSourcePolicy
    counterfactualS43AStandardIfEngaged
    s43ASpecialStandardApplication
counterfactualS43AAcquisitionDisposition =
  Priority.acquireForLiveConsumer counterfactualNeedsS43AStandard

------------------------------------------------------------------------
-- Deferral/blocking does not erase source state or a separately paid family.
------------------------------------------------------------------------

cullenS8SubrouteStillUnresolved :
  Vicarious.currentCullenS8SubrouteFrontier ≡ Vicarious.subrouteUnresolved
cullenS8SubrouteStillUnresolved = refl

familyIsAlreadyRecognised :
  Atomic.gate Family.cullenVicariousFamilyAtom ≡ BT.pos
familyIsAlreadyRecognised = refl

familyRecognitionStillDoesNotMakeS8LiveForActualConsumer :
  CullenLiveSensitive actualLiabilityDisposition exactS8VicariousSubroute → ⊥
familyRecognitionStillDoesNotMakeS8LiveForActualConsumer = λ ()

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DeferredForActualMeansGloballyIrrelevant : Set where
data FamilyPositiveOverridesUpstreamBreachBlocker : Set where
data CounterfactualAcquisitionChangesActualDisposition : Set where
data UnresolvedSubrouteMeansFamilyUnresolved : Set where
data S43ANonEngagementDeletesS43AFromOntology : Set where

deferredDoesNotMeanGloballyIrrelevant : DeferredForActualMeansGloballyIrrelevant → ⊥
deferredDoesNotMeanGloballyIrrelevant ()

familyPositiveDoesNotOverrideBreachBlocker :
  FamilyPositiveOverridesUpstreamBreachBlocker → ⊥
familyPositiveDoesNotOverrideBreachBlocker ()

counterfactualWorkDoesNotSilentlyChangeActualConsumer :
  CounterfactualAcquisitionChangesActualDisposition → ⊥
counterfactualWorkDoesNotSilentlyChangeActualConsumer ()

subrouteUnresolvedDoesNotUndoFamilyRecognition :
  UnresolvedSubrouteMeansFamilyUnresolved → ⊥
subrouteUnresolvedDoesNotUndoFamilyRecognition ()

s43ABlockedForActualDoesNotDeleteCoordinate :
  S43ANonEngagementDeletesS43AFromOntology → ⊥
s43ABlockedForActualDoesNotDeleteCoordinate ()
