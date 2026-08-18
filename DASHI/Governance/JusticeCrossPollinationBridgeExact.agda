module DASHI.Governance.JusticeCrossPollinationBridgeExact where

------------------------------------------------------------------------
-- JUSTICE CROSS-POLLINATION BRIDGES
--
-- This module welds existing Palestine/Amalek, externality-carrier, trauma,
-- epistemic-closure, historical-origin and council-gluing carriers to the
-- situated authority/justice lane.  It deliberately does not manufacture a
-- live political, legal, clinical or historical conclusion from a structural
-- analogy.  Every stronger conclusion requires the corresponding typed
-- witness at the bridge boundary.
--
-- Source calibration inherited from imported modules:
--
-- Kimberle Williams Crenshaw,
-- "Mapping the Margins: Intersectionality, Identity Politics, and Violence
-- against Women of Color", Stanford Law Review 43(6), 1241-1299 (1991).
-- DOI: 10.2307/1229039.
--
-- Reuven Firestone, Holy War in Judaism: The Fall and Rise of a Controversial
-- Idea, chapter "Who Is the Enemy?" (Oxford University Press, 2012).
-- DOI: 10.1093/acprof:oso/9780199860302.003.0007.
--
-- These references motivate provenance/role-binding and intersectional
-- separation only.  The bridge theorems below are DASHI constructions.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Culture.AmalekAuthorityProjectionBoundary as AmalekAuthority
import DASHI.Governance.ComparativeCrisisClimateAtlas as Comparative
import DASHI.Governance.EpistemicAttractorCore as Epistemic
import DASHI.Governance.ExternalityCarrierAttractor as Externality
import DASHI.Governance.LocalGlobalCouncilGluing as CouncilGluing
import DASHI.Governance.SituatedInverseJusticeFibreExact as Justice
import DASHI.Governance.TraumaExploitationAttractor as TraumaAttractor
import DASHI.Governance.TraumaMemorySublationBoundary as TraumaMemory
import DASHI.Physics.Foundations.FrontierEnemyPersistenceExact as Frontier
import DASHI.Physics.Foundations.SettlerEnemyAbstractionExact as Enemy

------------------------------------------------------------------------
-- 1. Enemy compression -> justice-relevant non-factorability.
------------------------------------------------------------------------

data FineJusticeAssessment : Set where
  actorSpecificAssessment civilianPopulationProtectionAssessment :
    FineJusticeAssessment

fineJusticeAssessment : Enemy.ConcreteActor → FineJusticeAssessment
fineJusticeAssessment Enemy.hamasActor = actorSpecificAssessment
fineJusticeAssessment Enemy.palestinianCivilianPopulation =
  civilianPopulationProtectionAssessment
fineJusticeAssessment Enemy.malayanCommunistForces = actorSpecificAssessment
fineJusticeAssessment Enemy.heterogeneousAntiColonialMovements =
  civilianPopulationProtectionAssessment

combatantCivilianAssessmentsDiffer :
  fineJusticeAssessment Enemy.hamasActor
  ≡ fineJusticeAssessment Enemy.palestinianCivilianPopulation →
  ⊥
combatantCivilianAssessmentsDiffer ()

enemyCompressionJusticeNonFactorability :
  NonFactor.NonFactorabilityWitness
    Enemy.rhetoricalCompression
    fineJusticeAssessment
enemyCompressionJusticeNonFactorability =
  NonFactor.nonFactorabilityWitness
    Enemy.hamasActor
    Enemy.palestinianCivilianPopulation
    Enemy.combatantAndCivilianCollapseUnderCompression
    combatantCivilianAssessmentsDiffer

justiceRelevantEnemyCompressionCannotBeJusticeSufficient :
  NonFactor.FactorsThrough
    Enemy.rhetoricalCompression
    fineJusticeAssessment →
  ⊥
justiceRelevantEnemyCompressionCannotBeJusticeSufficient =
  NonFactor.witnessRulesOutEveryFlatFactorisation
    enemyCompressionJusticeNonFactorability

record CivilianNonSubstitutionCollision : Set₁ where
  constructor civilianNonSubstitutionCollision
  field
    invariant : TraumaMemory.SublationInvariant
    invariantIsCivilianNonSubstitutability :
      invariant ≡ TraumaMemory.civilianNonSubstitutabilityInvariant
    collision :
      NonFactor.NonFactorabilityWitness
        Enemy.rhetoricalCompression
        fineJusticeAssessment

canonicalCivilianNonSubstitutionCollision : CivilianNonSubstitutionCollision
canonicalCivilianNonSubstitutionCollision =
  civilianNonSubstitutionCollision
    TraumaMemory.civilianNonSubstitutabilityInvariant
    refl
    enemyCompressionJusticeNonFactorability

------------------------------------------------------------------------
-- 2. Externality carrier -> punitive-route promotion boundary.
------------------------------------------------------------------------

CarrierVisibilityCannotPromoteToCoerciveRoute :
  Externality.VisibleCarrierEstablishesSufficientCause → ⊥
CarrierVisibilityCannotPromoteToCoerciveRoute =
  Externality.visibleCarrierDoesNotEstablishSufficientCause

record PunitiveExternalityInverseJusticeBridge
    (S : Externality.ReformSystem)
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    (transition : Justice.JusticeTransition before after) : Set₁ where
  constructor punitiveExternalityInverseJusticeBridge
  field
    punitiveCycle : Externality.PunitiveRestorationCycle S
    inverseJustice : Justice.InverseJusticeOperator transition
    carrierVisibilityStillDoesNotEstablishCause :
      Externality.VisibleCarrierEstablishesSufficientCause → ⊥

open PunitiveExternalityInverseJusticeBridge public

punitiveCarrierCyclePlusNegativeTransitionYieldsBridge :
  ∀ {S : Externality.ReformSystem}
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    {transition : Justice.JusticeTransition before after} →
  Externality.PunitiveRestorationCycle S →
  Justice.InverseJusticeOperator transition →
  PunitiveExternalityInverseJusticeBridge S transition
punitiveCarrierCyclePlusNegativeTransitionYieldsBridge cycle inverse =
  punitiveExternalityInverseJusticeBridge
    cycle
    inverse
    Externality.visibleCarrierDoesNotEstablishSufficientCause

------------------------------------------------------------------------
-- 3. Historical-origin truncation -> causal-completeness boundary.
------------------------------------------------------------------------

selectedOriginCannotEstablishCompleteJusticeCause :
  (context : TraumaMemory.CollectiveTraumaContext) →
  (label : String) →
  TraumaMemory.selectedOriginIsCompleteCause
    (TraumaMemory.mkHistoricalOriginFrame context label)
  ≡ false
selectedOriginCannotEstablishCompleteJusticeCause context label = refl

iranNineteenFiftyThreeFrameIsNotCompleteCause :
  TraumaMemory.selectedOriginIsCompleteCause
    TraumaMemory.iranNineteenFiftyThreeFrame
  ≡ false
iranNineteenFiftyThreeFrameIsNotCompleteCause = refl

iranNineteenSeventyNineFrameIsNotCompleteCause :
  TraumaMemory.selectedOriginIsCompleteCause
    TraumaMemory.iranNineteenSeventyNineFrame
  ≡ false
iranNineteenSeventyNineFrameIsNotCompleteCause = refl

------------------------------------------------------------------------
-- 4. Closed authority and disconfirmation capture.
------------------------------------------------------------------------

record ClosedAuthoritySelfCertification : Set where
  constructor closedAuthoritySelfCertification
  field
    loop : AmalekAuthority.ClosedAuthorityLoop
    loopHasNoIndependentCorrection :
      AmalekAuthority.correctionChannelIndependent loop ≡ false
    selfCertificationClaimsIndependentCorrection :
      AmalekAuthority.correctionChannelIndependent loop ≡ true

open ClosedAuthoritySelfCertification public

closedAuthorityCannotSelfCertifyJustice :
  ClosedAuthoritySelfCertification → ⊥
closedAuthorityCannotSelfCertifyJustice claim with
  trans
    (sym (loopHasNoIndependentCorrection claim))
    (selfCertificationClaimsIndependentCorrection claim)
... | ()

canonicalClosedAuthorityHasNoIndependentCorrection :
  AmalekAuthority.correctionChannelIndependent
    AmalekAuthority.canonicalClosedAuthorityRisk
  ≡ false
canonicalClosedAuthorityHasNoIndependentCorrection =
  AmalekAuthority.canonicalClosedAuthorityRiskHasNoIndependentCorrection

record RepairCorrectionProtocol
    (S : Epistemic.TrustUpdateSystem)
    (R : Epistemic.EvidenceReframingSystem S) : Set₁ where
  constructor repairCorrectionProtocol
  field
    supportiveAndContraryDisjoint :
      (evidence : Epistemic.Evidence S) →
      Epistemic.EvidenceReframingSystem.Supportive R evidence →
      Epistemic.EvidenceReframingSystem.Contrary R evidence →
      ⊥
    contraryEvidenceMustRemainCorrective :
      (inversion : Epistemic.DisconfirmationInversion S R) →
      Epistemic.EvidenceReframingSystem.Contrary R
        (Epistemic.EvidenceReframingSystem.reframe R
          (Epistemic.DisconfirmationInversion.contraryEvidence inversion))

open RepairCorrectionProtocol public

DisconfirmationCaptureCanBlockJusticeRepair :
  ∀ {S : Epistemic.TrustUpdateSystem}
    {R : Epistemic.EvidenceReframingSystem S} →
  (inversion : Epistemic.DisconfirmationInversion S R) →
  RepairCorrectionProtocol S R →
  ⊥
DisconfirmationCaptureCanBlockJusticeRepair {R = R} inversion protocol =
  supportiveAndContraryDisjoint protocol
    (Epistemic.EvidenceReframingSystem.reframe R
      (Epistemic.DisconfirmationInversion.contraryEvidence inversion))
    (Epistemic.DisconfirmationInversion.reframedAsSupport inversion)
    (contraryEvidenceMustRemainCorrective protocol inversion)

------------------------------------------------------------------------
-- 5. Trauma recursion -> inverse-justice attractor specialization.
------------------------------------------------------------------------

record InverseJusticeAttractor
    (T : TraumaAttractor.TraumaExploitationSystem)
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    (interpretTransition :
      TraumaAttractor.HistoricalState T →
      Justice.JusticeTransition before after) : Set₁ where
  constructor inverseJusticeAttractor
  field
    fixedPoint : TraumaAttractor.FixedPoint T
    inverseAtFixedPoint :
      Justice.InverseJusticeOperator
        (interpretTransition
          (TraumaAttractor.FixedPoint.point fixedPoint))

open InverseJusticeAttractor public

fixedPointPlusInverseInterpreterYieldsInverseJusticeAttractor :
  ∀ {T : TraumaAttractor.TraumaExploitationSystem}
    {beforeBase afterBase : Justice.SituatedJusticeBase}
    {before : Justice.JusticeFibre beforeBase}
    {after : Justice.JusticeFibre afterBase}
    {interpretTransition :
      TraumaAttractor.HistoricalState T →
      Justice.JusticeTransition before after} →
  (fixedPoint : TraumaAttractor.FixedPoint T) →
  Justice.InverseJusticeOperator
    (interpretTransition
      (TraumaAttractor.FixedPoint.point fixedPoint)) →
  InverseJusticeAttractor T interpretTransition
fixedPointPlusInverseInterpreterYieldsInverseJusticeAttractor fixed inverse =
  inverseJusticeAttractor fixed inverse

------------------------------------------------------------------------
-- 6. Abstract-enemy persistence -> apparatus-closure boundary.
------------------------------------------------------------------------

concreteThreatRemovalDoesNotEstablishCoerciveApparatusClosure :
  Frontier.defeatingActorDissolvesEnemyCategoryAutomatically
    Frontier.canonicalFrontierEnemyPersistenceBoundary
  ≡ false
concreteThreatRemovalDoesNotEstablishCoerciveApparatusClosure =
  Frontier.defeatingActorDissolvesEnemyCategoryAutomaticallyIsFalse
    Frontier.canonicalFrontierEnemyPersistenceBoundary

abstractEnemyClassificationCanReachPermanentMobilisation :
  Frontier.nextSecurityStage
    (Frontier.nextSecurityStage
      (Frontier.nextSecurityStage Frontier.abstractEnemyStage))
  ≡ Frontier.permanentMobilisationStage
abstractEnemyClassificationCanReachPermanentMobilisation =
  Frontier.abstractEnemyToMobilisation

------------------------------------------------------------------------
-- 7. Ends/means non-collapse.
------------------------------------------------------------------------

JusticeEndDoesNotDetermineMeansSign :
  (label end base form means : String) →
  Comparative.liberatoryObjectiveAutomaticallyLegitimatesEveryTactic
    (Comparative.mkLiberationPracticeAssessment label end base form means)
  ≡ false
JusticeEndDoesNotDetermineMeansSign label end base form means = refl

MeansViolationDoesNotEraseUnderlyingJusticeClaim :
  (label end base form means : String) →
  Comparative.tacticCondemnationErasesUnderlyingLiberationClaim
    (Comparative.mkLiberationPracticeAssessment label end base form means)
  ≡ false
MeansViolationDoesNotEraseUnderlyingJusticeClaim label end base form means = refl

------------------------------------------------------------------------
-- 8. Compatible situated authorities can compose without sovereign collapse.
------------------------------------------------------------------------

CompatibleSituatedAuthoritiesCanComposeWithoutSovereigntyCollapse :
  CouncilGluing.CompatibleCouncilFamily
    CouncilGluing.canonicalLocalCouncilFamily
  ×
  (CouncilGluing.sheafAnalogyCreatesPoliticalAuthority
    CouncilGluing.canonicalCouncilGluingBoundary ≡ false)
CompatibleSituatedAuthoritiesCanComposeWithoutSovereigntyCollapse =
  CouncilGluing.canonicalCouncilCompatibility , refl

record JusticeCrossPollinationBoundary : Set where
  constructor justiceCrossPollinationBoundary
  field
    enemyCompressionDeterminesFineJusticeTreatment : Bool
    carrierVisibilityEstablishesCoerciveAuthority : Bool
    selectedOriginEstablishesCompleteCause : Bool
    closedAuthoritySelfCertifiesJustice : Bool
    fixedPointAutomaticallyMeansInverseJustice : Bool
    defeatedConcreteEnemyAutomaticallyClosesSecurityApparatus : Bool
    goodEndAutomaticallyLegitimatesEveryMeans : Bool
    tacticViolationErasesUnderlyingClaim : Bool
    compatibleLocalAuthorityMeansUnboundedSovereignty : Bool

canonicalJusticeCrossPollinationBoundary : JusticeCrossPollinationBoundary
canonicalJusticeCrossPollinationBoundary =
  justiceCrossPollinationBoundary
    false false false false false false false false false
