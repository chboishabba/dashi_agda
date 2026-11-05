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
