module DASHI.Cognition.PNF.SensibLawMaboPabaiPositiveNegativeRegressionExact where

------------------------------------------------------------------------
-- KNOWN-POSITIVE / KNOWN-NEGATIVE REGRESSION FOR LEGAL PATH SEARCH
--
-- Mabo is the positive calibration: reproduce how a previously closed path
-- reopened through a legally available common-law recognition move.
-- Pabai is the negative calibration: reproduce why the pleaded negligence path
-- closes without converting that closure into a theorem that Parliament is the
-- only possible source of every differently formulated obligation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawMaboRecognitionCreationFootholdExact as Mabo
import DASHI.Cognition.PNF.SensibLawAuthorityTransformationMinimalCutExact as Cut
import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate

maboPositivePathIsReachable :
  Cut.reachableUnderCurrentAuthorities Cut.maboPositiveCalibration ≡ true
maboPositivePathIsReachable = refl

pabaiCandidatePathCurrentlyUnreachable :
  Cut.reachableUnderCurrentAuthorities Cut.pabaiNegativeCalibration ≡ false
pabaiCandidatePathCurrentlyUnreachable = refl

pabaiCandidateStillNeedsProof :
  Cut.proofStillRequired Cut.pabaiNegativeCalibration ≡ true
pabaiCandidateStillNeedsProof = refl

maboRecognitionMode :
  Mabo.mode Mabo.maboKnownPositive ≡ Mabo.recognisePreExistingInterest
maboRecognitionMode = refl

climateSearchMode :
  Mabo.mode Mabo.climateCandidateSearch ≡ Mabo.incrementalCommonLawDevelopment
climateSearchMode = refl

------------------------------------------------------------------------
-- The regression target is structural explanation, not desired outcome.
------------------------------------------------------------------------

data PositiveCaseMeansEveryAnalogousCaseMustReopen : Set where
data NegativeCaseMeansLegislationAlwaysNecessary : Set where

positiveCalibrationDoesNotForceAnalogy : PositiveCaseMeansEveryAnalogousCaseMustReopen → ⊥
positiveCalibrationDoesNotForceAnalogy ()

negativeCalibrationDoesNotUniversaliseLegislationNecessity :
  NegativeCaseMeansLegislationAlwaysNecessary → ⊥
negativeCalibrationDoesNotUniversaliseLegislationNecessity ()

pabaiNoDutyStillDoesNotCloseEveryReformulation :
  Climate.PabaiNoDutyClosesEveryPossibleClimateDuty → ⊥
pabaiNoDutyStillDoesNotCloseEveryReformulation =
  Climate.pabaiDoesNotCloseEveryReformulatedDutyByDefinition
