module DASHI.Cognition.PNF.SensibLawCullenConsumerRelativeSourceAcquisitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.PNF.SensibLawConsumerSourceAcquisitionPriorityExact as Priority
import DASHI.Cognition.PNF.SensibLawNSWCivilLiabilityActAtomicSourceAtlasExact as CLA
import DASHI.Cognition.PNF.SensibLawCullenNSWCLAAtomicApplicationExact as CullenCLA
import DASHI.Cognition.PNF.SensibLawCullenVicariousLiabilityFamilyAtomicExact as Family
import DASHI.Cognition.PNF.SensibLawNSWVicariousLiabilitySourceRealisationExact as Vicarious

------------------------------------------------------------------------
-- CULLEN CONSUMER-RELATIVE SOURCE ACQUISITION
--
-- Same unresolved source coordinate, different consumer:
--
-- actual disposition consumer:
--   breach already fails on the retained s 5B(1)(c) atom, so selecting the
--   precise s 8(1)(a)/(b) vicarious subroute cannot repair that upstream defect.
--
-- counterfactual vicarious-route consumer:
--   conditional on an underlying police tort, the exact s 8 route IS the live
--   question, so source acquisition is admitted.
------------------------------------------------------------------------

data CullenConsumer : Set where
  actualLiabilityDisposition : CullenConsumer
  counterfactualVicariousRouteIfTort : CullenConsumer

data CullenSourceCoordinate : Set where
  exactS8VicariousSubroute : CullenSourceCoordinate
  s43ASpecialStandardApplication : CullenSourceCoordinate

data CullenLiveSensitive : CullenConsumer → CullenSourceCoordinate → Set where
  counterfactualNeedsS8Route :
    CullenLiveSensitive counterfactualVicariousRouteIfTort exactS8VicariousSubroute

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
-- Actual disposition: s 5B(1)(c) is a sourced -1 upstream blocker.
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
-- Counterfactual consumer: exact s 8 route becomes live.
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

------------------------------------------------------------------------
-- The route remains unresolved in the statutory source owner.  Deferral for
-- one consumer therefore does NOT erase, solve, or deny the coordinate.
------------------------------------------------------------------------

cullenS8SubrouteStillUnresolved :
  Vicarious.currentCullenS8SubrouteFrontier ≡ Vicarious.subrouteUnresolved
cullenS8SubrouteStillUnresolved = refl

familyIsAlreadyRecognised :
  BT.Trit
familyIsAlreadyRecognised =
  DASHI.Cognition.PNF.SensibLawAtomicLegalTestBalancedTernaryExact.gate
    Family.cullenVicariousFamilyAtom

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
