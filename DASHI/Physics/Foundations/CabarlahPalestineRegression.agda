module DASHI.Physics.Foundations.CabarlahPalestineRegression where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.CabarlahClaimStatusExact as Status
import DASHI.Physics.Foundations.CabarlahEvidenceWitnessExact as Witness
import DASHI.Physics.Foundations.CabarlahHistoricalLayerExact as History
import DASHI.Physics.Foundations.CabarlahToponymTranscriptionExact as Toponym
import DASHI.Physics.Foundations.CabarlahSignalInferenceExact as Signal
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Enemy
import DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact as Circuit
import DASHI.Physics.Foundations.FrontierEnemyPersistenceExact as Persistence
import DASHI.Physics.Foundations.CabarlahPalestineSourceAtlas as Sources
import DASHI.Physics.Foundations.CabarlahPalestineBoundary as Boundary

------------------------------------------------------------------------
-- Correction regressions.

capbarlahRemainsARejectedHistoricalSpelling :
  Status.claimStatus Status.capbarlahHistoricalSpelling ≡ Status.refuted
capbarlahRemainsARejectedHistoricalSpelling =
  Status.capbarlahTypoIsNotHistoricalSpelling

communistConcessionRemainsRejected :
  Status.claimStatus Status.communistConcessionBoundaryAtCabarlah
  ≡ Status.refuted
communistConcessionRemainsRejected =
  Status.communistBoundaryClaimIsRefuted

communistConcessionHasNoFactWitness :
  Witness.EvidenceWitness Status.communistConcessionBoundaryAtCabarlah
  → ⊥
communistConcessionHasNoFactWitness =
  Witness.noCommunistConcessionBoundaryWitness

uniquePronunciationHasNoFactWitness :
  Witness.EvidenceWitness Status.exactIndigenousSourcePronunciation
  → ⊥
uniquePronunciationHasNoFactWitness =
  Witness.noUniqueSourcePronunciationWitness

brisbaneLatitudeArithmeticRegression :
  274261 + 444 ≡ 274705
brisbaneLatitudeArithmeticRegression = refl

worldWarTwoAndColdWarDoNotCollapse :
  History.imperialJapan ≡ History.coldWarCommunistForces → ⊥
worldWarTwoAndColdWarDoNotCollapse =
  History.japanIsNotColdWarCommunism

signalsLineageReachesBorneoRegression :
  History.nextSignalsLineageStage
    (History.nextSignalsLineageStage
      History.wartimeSpecialWirelessStage)
  ≡ History.borneoOperationalStage
signalsLineageReachesBorneoRegression =
  History.wartimeLineageReachesBorneoInTwo

------------------------------------------------------------------------
-- Loss, interpretation, and abstraction regressions.

toponymTranscriptionRemainsNonInjective :
  ¬ Toponym.InjectiveColonialRender
toponymTranscriptionRemainsNonInjective =
  Toponym.colonialRenderIsNotInjective

signalInferenceRemainsNonInjective :
  ¬ Signal.SignalInferenceInjective
signalInferenceRemainsNonInjective =
  Signal.signalInferenceIsNotInjective

signSignalComparisonRemainsStructural :
  Signal.interpretationComparison
    Signal.theologicalSignInterpretation
    Signal.militarySignalInterpretation
  ≡ Signal.structuralComparisonOnly
signSignalComparisonRemainsStructural =
  Signal.crossDomainComparisonIsStructuralOnly

enemyCompressionRemainsNonInjective :
  ¬ Enemy.CompressionInjective
enemyCompressionRemainsNonInjective =
  Enemy.rhetoricalCompressionIsNotInjective

australianAmalekComparisonRemainsStructural :
  Enemy.comparisonAuthority Enemy.indigenousAustraliaSettlerStructure
  ≡ Enemy.structuralHomologyOnly
australianAmalekComparisonRemainsStructural =
  Enemy.australianComparisonIsStructuralOnly

------------------------------------------------------------------------
-- Site and protest regressions.

pineGapAndBorneoRemainDistinct :
  Circuit.pineGap ≡ Circuit.borneoBarracksCabarlah → ⊥
pineGapAndBorneoRemainDistinct =
  Circuit.pineGapIsNotBorneoBarracks

pineGapDemandPairRegression :
  (Circuit.hasReturnDemand Circuit.pineGapPalestineDemands ≡ true)
  ×
  (Circuit.hasPalestineDemand Circuit.pineGapPalestineDemands ≡ true)
pineGapDemandPairRegression =
  Circuit.pineGapProtestHasReturnDemand
  , Circuit.pineGapProtestHasPalestineDemand

specificStrikeLinkRemainsUnverified :
  Circuit.openSourceOperationalStatus
  ≡ Circuit.publiclyVerifiedSpecificStrikeLink
  → ⊥
specificStrikeLinkRemainsUnverified =
  Circuit.openSourceStatusIsNotSpecificStrikeVerification

------------------------------------------------------------------------
-- Generic frontier and source regressions.

frontierParadoxRegression :
  (Persistence.includedInProtectedCore Persistence.canonicalFrontierParadox
  ≡ false)
  ×
  (Persistence.requiredForCoreSecurity Persistence.canonicalFrontierParadox
  ≡ true)
frontierParadoxRegression =
  Persistence.frontierExcludedFromCore
  , Persistence.frontierRequiredForSecurity

permanentEnemyEffectRegression :
  Persistence.abstractEnemyOf Persistence.firstConcreteEnemy
  ≡ Persistence.abstractEnemyOf Persistence.laterConcreteEnemy
permanentEnemyEffectRegression =
  Persistence.categoryPersistsAfterFirstDefeat

sourceCountRegression :
  Sources.canonicalCabarlahPalestineSourceCount ≡ 10
sourceCountRegression =
  Sources.canonicalCabarlahPalestineSourceCountIsTen

integratedBoundaryRegression : Boundary.CabarlahPalestineFormalBoundary
integratedBoundaryRegression =
  Boundary.canonicalCabarlahPalestineFormalBoundary
