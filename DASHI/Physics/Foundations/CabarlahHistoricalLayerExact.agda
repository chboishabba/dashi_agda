module DASHI.Physics.Foundations.CabarlahHistoricalLayerExact where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahClaimStatusExact as Status

------------------------------------------------------------------------
-- Exact integer calibration of the approximate coordinates used in the
-- attached analysis.  Units are one ten-thousandth of a degree south.

cabarlahLatitude : Nat
cabarlahLatitude = 274261

brisbaneLatitude : Nat
brisbaneLatitude = 274705

latitudeDifference : Nat
latitudeDifference = 444

cabarlahPlusDifferenceIsBrisbane :
  cabarlahLatitude + latitudeDifference ≡ brisbaneLatitude
cabarlahPlusDifferenceIsBrisbane = refl

-- At 111 km per degree this is 49284 / 10000 km = 4.9284 km.  The theorem is
-- exact integer arithmetic; it is not a geodetic survey result.
latitudeDistanceNumerator : Nat
latitudeDistanceNumerator = 111 * latitudeDifference

latitudeDistanceNumeratorIs49284 :
  latitudeDistanceNumerator ≡ 49284
latitudeDistanceNumeratorIs49284 = refl

------------------------------------------------------------------------
-- The World-War-II fallback narrative and the later anti-communist signals
-- role are distinct historical layers with distinct enemies.

data HistoricalEnemy : Set where
  imperialJapan : HistoricalEnemy
  coldWarCommunistForces : HistoricalEnemy

data CabarlahPeriod : Set where
  worldWarTwoTrainingPeriod : CabarlahPeriod
  postwarSignalsPeriod : CabarlahPeriod

periodEnemy : CabarlahPeriod → HistoricalEnemy
periodEnemy worldWarTwoTrainingPeriod = imperialJapan
periodEnemy postwarSignalsPeriod = coldWarCommunistForces

worldWarTwoEnemyIsJapan :
  periodEnemy worldWarTwoTrainingPeriod ≡ imperialJapan
worldWarTwoEnemyIsJapan = refl

postwarSignalsEnemyIsCommunistForces :
  periodEnemy postwarSignalsPeriod ≡ coldWarCommunistForces
postwarSignalsEnemyIsCommunistForces = refl

japanIsNotColdWarCommunism :
  imperialJapan ≡ coldWarCommunistForces → ⊥
japanIsNotColdWarCommunism ()

periodsDoNotCollapse :
  worldWarTwoTrainingPeriod ≡ postwarSignalsPeriod → ⊥
periodsDoNotCollapse ()

------------------------------------------------------------------------
-- Borneo Barracks is represented as an institutional-lineage hinge, not as a
-- proof that the World-War-II and Cold-War enemies were identical.

data SignalsLineageStage : Set where
  wartimeSpecialWirelessStage : SignalsLineageStage
  permanentCabarlahSignalsStage : SignalsLineageStage
  borneoOperationalStage : SignalsLineageStage
  vietnamOperationalStage : SignalsLineageStage

nextSignalsLineageStage : SignalsLineageStage → SignalsLineageStage
nextSignalsLineageStage wartimeSpecialWirelessStage =
  permanentCabarlahSignalsStage
nextSignalsLineageStage permanentCabarlahSignalsStage =
  borneoOperationalStage
nextSignalsLineageStage borneoOperationalStage =
  vietnamOperationalStage
nextSignalsLineageStage vietnamOperationalStage =
  vietnamOperationalStage

wartimeLineageReachesBorneoInTwo :
  nextSignalsLineageStage
    (nextSignalsLineageStage wartimeSpecialWirelessStage)
  ≡ borneoOperationalStage
wartimeLineageReachesBorneoInTwo = refl

cabarlahLineageReachesVietnamInTwo :
  nextSignalsLineageStage
    (nextSignalsLineageStage permanentCabarlahSignalsStage)
  ≡ vietnamOperationalStage
cabarlahLineageReachesVietnamInTwo = refl

wartimeStageIsNotBorneoStage :
  wartimeSpecialWirelessStage ≡ borneoOperationalStage → ⊥
wartimeStageIsNotBorneoStage ()

------------------------------------------------------------------------
-- Terminal-frontier language is represented as a claim carrying its status,
-- not as a total function that manufactures a historical boundary for every
-- enemy.

data FrontierName : Set where
  allegedBrisbaneLine : FrontierName
  cabarlahLocality : FrontierName

record FrontierClaim : Set where
  constructor frontierClaim
  field
    enemy : HistoricalEnemy
    frontier : FrontierName
    status : Status.EvidenceStatus

open FrontierClaim public

worldWarTwoFallbackClaim : FrontierClaim
worldWarTwoFallbackClaim =
  frontierClaim imperialJapan allegedBrisbaneLine Status.contested

rejectedCommunistCabarlahClaim : FrontierClaim
rejectedCommunistCabarlahClaim =
  frontierClaim
    coldWarCommunistForces
    cabarlahLocality
    Status.refuted

fallbackClaimEnemyIsJapan :
  enemy worldWarTwoFallbackClaim ≡ imperialJapan
fallbackClaimEnemyIsJapan = refl

fallbackClaimIsContested :
  status worldWarTwoFallbackClaim ≡ Status.contested
fallbackClaimIsContested = refl

communistCabarlahClaimIsRefuted :
  status rejectedCommunistCabarlahClaim ≡ Status.refuted
communistCabarlahClaimIsRefuted = refl

record HistoricalLayerBoundary : Set where
  constructor historicalLayerBoundary
  field
    latitudeCoincidenceProvesOfficialLine : Bool
    latitudeCoincidenceProvesOfficialLineIsFalse :
      latitudeCoincidenceProvesOfficialLine ≡ false

    worldWarTwoEnemyEqualsColdWarEnemy : Bool
    worldWarTwoEnemyEqualsColdWarEnemyIsFalse :
      worldWarTwoEnemyEqualsColdWarEnemy ≡ false

    signalsRoleProvesTerritorialConcession : Bool
    signalsRoleProvesTerritorialConcessionIsFalse :
      signalsRoleProvesTerritorialConcession ≡ false

    institutionalLineageMakesEnemiesIdentical : Bool
    institutionalLineageMakesEnemiesIdenticalIsFalse :
      institutionalLineageMakesEnemiesIdentical ≡ false

open HistoricalLayerBoundary public

canonicalHistoricalLayerBoundary : HistoricalLayerBoundary
canonicalHistoricalLayerBoundary =
  historicalLayerBoundary
    false refl
    false refl
    false refl
    false refl
