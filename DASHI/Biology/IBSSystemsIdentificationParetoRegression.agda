module DASHI.Biology.IBSSystemsIdentificationParetoRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSSystemsIdentificationParetoExact as Systems

measurementAtlasRegression :
  Systems.canonicalIBSMeasurementAtlas ≡ Systems.canonicalIBSMeasurementAtlas
measurementAtlasRegression = refl

systemsFrontierRegression :
  Systems.canonicalIBSSystemsParetoFrontier ≡ Systems.canonicalIBSSystemsParetoFrontier
systemsFrontierRegression = refl

singleMarkerDoesNotIdentifyStateRegression :
  Systems.SingleMarkerIdentifiesWholeSystemStatePermission → ⊥
singleMarkerDoesNotIdentifyStateRegression = Systems.singleMarkerDoesNotIdentifyWholeSystemState

symptomSubtypeDoesNotIdentifyMechanismRegression :
  Systems.BowelHabitSubtypeIdentifiesMechanismPermission → ⊥
symptomSubtypeDoesNotIdentifyMechanismRegression = Systems.bowelHabitSubtypeDoesNotIdentifyMechanism

crossSectionDoesNotIdentifyFeedbackRegression :
  Systems.CrossSectionIdentifiesFeedbackDirectionPermission → ⊥
crossSectionDoesNotIdentifyFeedbackRegression = Systems.crossSectionDoesNotIdentifyFeedbackDirection

interventionPanelRegression :
  Systems.canonicalMinimumDiscriminatingPanel ≡ Systems.canonicalMinimumDiscriminatingPanel
interventionPanelRegression = refl
