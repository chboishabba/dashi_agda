module DASHI.Culture.Cuisine.CuisineFormalismTests where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Culture.Cuisine.QualitativeSensoryCore as Q
import DASHI.Culture.Cuisine.DishIdentityLineageCore as D
import DASHI.Culture.Cuisine.CompositionProvenanceCore as C
import DASHI.Culture.Cuisine.CuisineFormalismBundle as B

------------------------------------------------------------------------
-- Focused regression witnesses for the nontrivial finite parts.
------------------------------------------------------------------------

umamiInteractionRegression :
  Q.interactionTerm Q.kombuKatsuobushiUmami ≡ 6
umamiInteractionRegression = refl

umamiCombinedRegression :
  Q.combinedIntensity Q.kombuKatsuobushiUmami ≡ 11
umamiCombinedRegression = refl

dashiProfileUmamiRegression :
  Q.tasteIntensity Q.dashiSensoryProfile Q.umami ≡ 11
dashiProfileUmamiRegression = refl

funkReadingContextRegression :
  Q.firstReading Q.fermentedFunkDivergentReading ≡ Q.trainedFunkReading
funkReadingContextRegression = refl

funkSafetySeparationRegression :
  Q.safetyStatus (Q.firstBoundary Q.sameFunkCueDifferentSafety) ≡ Q.safetyVerified
funkSafetySeparationRegression = refl

carbonaraCreamClassificationRegression :
  D.classify D.carbonaraCandidateEnvelope D.cream ≡ D.canonicallyExcluded
carbonaraCreamClassificationRegression = refl

proteinCompositionRegression :
  C.totalAmount C.proteinCompositionExample ≡ 12
proteinCompositionRegression = refl

mornayPathRegression : D.SaucePath D.bechamel D.mornay
mornayPathRegression = D.mornayDerivesFromBechamel

bordelaisePathRegression : D.SaucePath D.espagnole D.bordelaise
bordelaisePathRegression = D.bordelaiseDerivesFromEspagnole

nonCollapseRegression : B.CuisineNonCollapse
nonCollapseRegression = B.canonicalCuisineNonCollapse
