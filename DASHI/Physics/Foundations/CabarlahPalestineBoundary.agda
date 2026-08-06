module DASHI.Physics.Foundations.CabarlahPalestineBoundary where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahClaimStatusExact as Status
import DASHI.Physics.Foundations.CabarlahHistoricalLayerExact as History
import DASHI.Physics.Foundations.CabarlahToponymTranscriptionExact as Toponym
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Enemy
import DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact as Circuit
import DASHI.Physics.Foundations.FrontierEnemyPersistenceExact as Persistence
import DASHI.Physics.Foundations.CabarlahPalestineSourceAtlas as Sources

------------------------------------------------------------------------
-- Cabarlah as a layered place.  The ordering records institutional succession,
-- not extinction of Country or transfer of Indigenous sovereignty.

data CabarlahLayer : Set where
  indigenousCountryLayer : CabarlahLayer
  settlerLocalityLayer : CabarlahLayer
  militarySecurityLayer : CabarlahLayer

nextCabarlahLayer : CabarlahLayer → CabarlahLayer
nextCabarlahLayer indigenousCountryLayer = settlerLocalityLayer
nextCabarlahLayer settlerLocalityLayer = militarySecurityLayer
nextCabarlahLayer militarySecurityLayer = militarySecurityLayer

countryThroughSettlementToMilitarySite :
  nextCabarlahLayer (nextCabarlahLayer indigenousCountryLayer)
  ≡ militarySecurityLayer
countryThroughSettlementToMilitarySite = refl

countryLayerIsNotMilitaryLayer :
  indigenousCountryLayer ≡ militarySecurityLayer → ⊥
countryLayerIsNotMilitaryLayer ()

------------------------------------------------------------------------
-- Integrated boundary.  Every positive theorem is paired with a scope guard
-- that blocks the overstatement corrected in the attached discussion.

record CabarlahPalestineFormalBoundary : Set where
  field
    claimStatusBoundary : Status.ClaimStatusBoundary
    historicalLayerBoundary : History.HistoricalLayerBoundary
    toponymBoundary : Toponym.ToponymTranscriptionBoundary
    enemyAbstractionBoundary : Enemy.EnemyAbstractionBoundary
    intelligenceCircuitBoundary : Circuit.IntelligenceCircuitBoundary
    frontierPersistenceBoundary :
      Persistence.FrontierEnemyPersistenceBoundary

    exactLatitudeDifference :
      History.cabarlahLatitude + History.latitudeDifference
      ≡ History.brisbaneLatitude

    worldWarTwoAndColdWarEnemiesDistinct :
      History.imperialJapan ≡ History.coldWarCommunistForces → ⊥

    communistCabarlahBoundaryRejected :
      History.status History.rejectedCommunistCabarlahClaim
      ≡ Status.refuted

    colonialToponymRenderNonInjective :
      ¬ Toponym.InjectiveColonialRender

    enemyCompressionNonInjective :
      ¬ Enemy.CompressionInjective

    australianAmalekComparisonStructuralOnly :
      Enemy.comparisonAuthority Enemy.indigenousAustraliaSettlerStructure
      ≡ Enemy.structuralHomologyOnly

    pineGapAndBorneoBarracksDistinct :
      Circuit.pineGap ≡ Circuit.borneoBarracksCabarlah → ⊥

    pineGapDemandCouplesLandReturn :
      Circuit.hasReturnDemand Circuit.pineGapPalestineDemands ≡ true

    pineGapDemandCouplesPalestine :
      Circuit.hasPalestineDemand Circuit.pineGapPalestineDemands ≡ true

    frontierExcludedYetSecurityDependent :
      Persistence.includedInProtectedCore
        Persistence.canonicalFrontierParadox
      ≡ false
      ×
      Persistence.requiredForCoreSecurity
        Persistence.canonicalFrontierParadox
      ≡ true

    abstractEnemyCanOutliveConcreteActor :
      Persistence.abstractEnemyOf Persistence.firstConcreteEnemy
      ≡ Persistence.abstractEnemyOf Persistence.laterConcreteEnemy

    sourceCountIsNine :
      Sources.canonicalCabarlahPalestineSourceCount ≡ 9

    capbarlahIsSemanticConstruction : Bool
    capbarlahIsSemanticConstructionIsFalse :
      capbarlahIsSemanticConstruction ≡ false

    conventionalNamePreservesIndigenousAuthority : Bool
    conventionalNamePreservesIndigenousAuthorityIsFalse :
      conventionalNamePreservesIndigenousAuthority ≡ false

    protestConcernIsSpecificStrikeVerification : Bool
    protestConcernIsSpecificStrikeVerificationIsFalse :
      protestConcernIsSpecificStrikeVerification ≡ false

open CabarlahPalestineFormalBoundary public

canonicalCabarlahPalestineFormalBoundary :
  CabarlahPalestineFormalBoundary
canonicalCabarlahPalestineFormalBoundary =
  record
    { claimStatusBoundary = Status.canonicalClaimStatusBoundary
    ; historicalLayerBoundary = History.canonicalHistoricalLayerBoundary
    ; toponymBoundary = Toponym.canonicalToponymTranscriptionBoundary
    ; enemyAbstractionBoundary = Enemy.canonicalEnemyAbstractionBoundary
    ; intelligenceCircuitBoundary =
        Circuit.canonicalIntelligenceCircuitBoundary
    ; frontierPersistenceBoundary =
        Persistence.canonicalFrontierEnemyPersistenceBoundary
    ; exactLatitudeDifference =
        History.cabarlahPlusDifferenceIsBrisbane
    ; worldWarTwoAndColdWarEnemiesDistinct =
        History.japanIsNotColdWarCommunism
    ; communistCabarlahBoundaryRejected =
        History.communistCabarlahClaimIsRefuted
    ; colonialToponymRenderNonInjective =
        Toponym.colonialRenderIsNotInjective
    ; enemyCompressionNonInjective =
        Enemy.rhetoricalCompressionIsNotInjective
    ; australianAmalekComparisonStructuralOnly =
        Enemy.australianComparisonIsStructuralOnly
    ; pineGapAndBorneoBarracksDistinct =
        Circuit.pineGapIsNotBorneoBarracks
    ; pineGapDemandCouplesLandReturn =
        Circuit.pineGapProtestHasReturnDemand
    ; pineGapDemandCouplesPalestine =
        Circuit.pineGapProtestHasPalestineDemand
    ; frontierExcludedYetSecurityDependent =
        Persistence.frontierExcludedFromCore
        , Persistence.frontierRequiredForSecurity
    ; abstractEnemyCanOutliveConcreteActor =
        Persistence.categoryPersistsAfterFirstDefeat
    ; sourceCountIsNine =
        Sources.canonicalCabarlahPalestineSourceCountIsNine
    ; capbarlahIsSemanticConstruction = false
    ; capbarlahIsSemanticConstructionIsFalse = refl
    ; conventionalNamePreservesIndigenousAuthority = false
    ; conventionalNamePreservesIndigenousAuthorityIsFalse = refl
    ; protestConcernIsSpecificStrikeVerification = false
    ; protestConcernIsSpecificStrikeVerificationIsFalse = refl
    }
