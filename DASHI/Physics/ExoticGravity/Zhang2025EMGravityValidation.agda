module DASHI.Physics.ExoticGravity.Zhang2025EMGravityValidation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.ExoticGravity.Zhang2025EMGravitySourceClaimExact as S
import DASHI.Physics.ExoticGravity.Zhang2025EMGravityPhysicalPromotionExact as P
import DASHI.Physics.ExoticGravity.AntigravityMaterialBidiCrossPollinationExact as Anti

-- The US, CN and WO publications belong to the SAME source family.
onePatentFamilyNotIndependentReplications :
  S.family S.chineseApplication ≡ S.family S.unitedStatesGrant
onePatentFamilyNotIndependentReplications = refl

internationalPublicationSameFamily :
  S.family S.internationalApplication ≡ S.family S.unitedStatesGrant
internationalPublicationSameFamily = refl

-- A nonconducting target does not exclude ordinary electric polarization.
insulatorPolarisationIsAClassicalCandidate :
  S.PossibleClassicalRoute S.nonconductingNonmagnetic S.dielectricPolarisation
insulatorPolarisationIsAClassicalCandidate =
  S.nonconductorDoesNotExcludePolarisation

-- Source-only paths are definitionally unable to pay these consumers.
sourceMotionCannotEqualMetricReadout :
  S.SameClaimConsumer S.apparatusMotion S.metricClock → S.Contradiction
sourceMotionCannotEqualMetricReadout = S.motionIsNotMetricConsumer

sourceMotionCannotEqualTTReadout :
  S.SameClaimConsumer S.apparatusMotion S.farFieldTTStrain → S.Contradiction
sourceMotionCannotEqualTTReadout = S.motionIsNotGWConsumer

sourceCannotEntitleMetricClaim :
  S.PatentClaimEntitlement S.engineeredMetricShift → S.Contradiction
sourceCannotEntitleMetricClaim = S.patentDoesNotClaimMeasuredMetric

sourceCannotEntitleGWClaim :
  S.PatentClaimEntitlement S.propagatingGravityWave → S.Contradiction
sourceCannotEntitleGWClaim = S.patentDoesNotClaimMeasuredGW

-- Routing preserves the exact consumer/claim identity already in DASHI.
externalRouteUsesRemoteField :
  P.canonicalExternalRoute ≡
    P.remoteProbe Anti.remoteRepulsiveField refl
externalRouteUsesRemoteField = refl

metricRouteUsesMetricConsumer :
  P.canonicalMetricRoute ≡
    P.metricProbe Anti.engineeredMetricResponse refl
metricRouteUsesMetricConsumer = refl

currentSourceHasNoIndependentPhysicalReceipt :
  P.CurrentZhangPhysicalAuthority → S.Contradiction
currentSourceHasNoIndependentPhysicalReceipt ()

sourceOnlyDoesNotAssertEmpiricalPromotion :
  S.PatentClaimBoundary.patentIsExperimentalReplication
    S.canonicalPatentClaimBoundary ≡ false
sourceOnlyDoesNotAssertEmpiricalPromotion = refl

nearVacuumDoesNotCloseElectrostatics :
  P.NonPromotionBoundary.nearVacuumExcludesElectrostatics
    P.canonicalNonPromotionBoundary ≡ false
nearVacuumDoesNotCloseElectrostatics = refl

betterFitDoesNotIdentifyUniqueGravityMechanism :
  P.NonPromotionBoundary.alternativeModelBetterFitIdentifiesUniqueMechanism
    P.canonicalNonPromotionBoundary ≡ false
betterFitDoesNotIdentifyUniqueGravityMechanism = refl
