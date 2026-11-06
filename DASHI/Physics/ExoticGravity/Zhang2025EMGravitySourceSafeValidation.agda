{-# OPTIONS --safe #-}
module DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceSafeValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceClaimExact as S

onePatentFamily :
  S.family S.chineseApplication ≡ S.family S.unitedStatesGrant
onePatentFamily = refl

oneInternationalFamily :
  S.family S.internationalApplication ≡ S.family S.unitedStatesGrant
oneInternationalFamily = refl

insulatorStillPolarizable :
  S.PossibleClassicalRoute S.nonconductingNonmagnetic S.dielectricPolarisation
insulatorStillPolarizable = S.dielectricInsulator

documentNotMeasuredMetric :
  S.PatentClaimEntitlement S.engineeredMetricShift → S.Contradiction
documentNotMeasuredMetric = S.patentDoesNotClaimMeasuredMetric

documentNotMeasuredGW :
  S.PatentClaimEntitlement S.propagatingGravityWave → S.Contradiction
documentNotMeasuredGW = S.patentDoesNotClaimMeasuredGW

motionNotEquivalentToMetricConsumer :
  S.SameClaimConsumer S.apparatusMotion S.metricClock → S.Contradiction
motionNotEquivalentToMetricConsumer = S.motionIsNotMetricConsumer

motionNotEquivalentToGWConsumer :
  S.SameClaimConsumer S.apparatusMotion S.farFieldTTStrain → S.Contradiction
motionNotEquivalentToGWConsumer = S.motionIsNotGWConsumer

noAutomaticMeasuredReplications :
  S.PatentClaimBoundary.patentIsExperimentalReplication
    S.canonicalPatentClaimBoundary ≡ false
noAutomaticMeasuredReplications = refl

distinctApparatusPreventsUnpaidWeld :
  S.SameApparatusSource S.zhangPatentVacuumSphere S.zhangXuToroidAirGap →
  S.Contradiction
distinctApparatusPreventsUnpaidWeld = S.patentSphereNotToroid

differentCurlHypothesesRequireIndependentTest :
  S.SameTheoryStatement S.directMagneticFieldCurlLaw
                        S.magneticTimeDerivativeCurlLaw →
  S.Contradiction
differentCurlHypothesesRequireIndependentTest = S.distinctMagneticCurlClaims

import DASHI.Physics.ExoticGravity.Zhang2025EMGravityQuantitativeSourceExact as Q

sourcePaperMassIsReported :
  Q.massMg Q.paper ≡ 50
sourcePaperMassIsReported = Q.paperMassFiftyMilligrams

sourceAluminiumMassIsReported :
  Q.massMg Q.aluminium ≡ 2000
sourceAluminiumMassIsReported = Q.aluminiumMassTwoGrams

nominalFieldDoesNotPayZhangAnomaly :
  Q.AdmissibleNonPromotingUse
    Q.zhangXu2025Toroid Q.reportedNominalInput Q.sameApparatusAnomaly →
  S.Contradiction
nominalFieldDoesNotPayZhangAnomaly = Q.noZhangNominalToSameApparatusAnomaly

Dresden2024NoiseCannotPayZhangMetric :
  Q.AdmissibleNonPromotingUse
    Q.tajmar2024SteadyVacuumBalance Q.authorNoiseScreening
    Q.gravitationalFreeFallMetric →
  S.Contradiction
Dresden2024NoiseCannotPayZhangMetric =
  Q.noTajmar2024SensitivityToZhangMetric

Dresden2026ResolutionCannotPayZhangAnomaly :
  Q.AdmissibleNonPromotingUse
    Q.tajmar2026ThreeAmpereDCToroid Q.instrumentalResolution
    Q.sameApparatusAnomaly →
  S.Contradiction
Dresden2026ResolutionCannotPayZhangAnomaly =
  Q.noTajmar2026ResolutionToZhangAnomaly

publishedNominalNotMeasuredAcceleration :
  Q.PublishedQuantitativeEvidenceBoundary.originalZhangAcceleration95CIAvailable
    Q.canonicalPublishedQuantitativeEvidenceBoundary ≡ false
publishedNominalNotMeasuredAcceleration = refl
