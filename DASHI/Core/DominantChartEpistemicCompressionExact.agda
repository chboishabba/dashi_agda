module DASHI.Core.DominantChartEpistemicCompressionExact where

------------------------------------------------------------------------
-- DOMINANT-CHART EPISTEMIC COMPRESSION
--
-- Generic repository owner for the following question:
--
--   What distinctions does a proposed observer make impossible to see for the
--   consumer that actually needs them?
--
-- This owner is deliberately not a master political ontology. Juridical,
-- economic, administrative, psychologising, representational, intersectional,
-- commodity-form and terminalising compressions are separately typed families.
-- A shared non-factorability shape does not make their histories, semantics or
-- source traditions identical.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.CategoryAuthorityAuditExact as CategoryAudit

------------------------------------------------------------------------
-- Operator families.
------------------------------------------------------------------------

data CompressionFamily : Set where
  juridicalRecognitionCompression : CompressionFamily
  economicScalarCompression : CompressionFamily
  administrativeClassificationCompression : CompressionFamily
  psychologisingIndividualisationCompression : CompressionFamily
  representationalSubjectCompression : CompressionFamily
  singleAxisIntersectionalCompression : CompressionFamily
  commodityFormCompression : CompressionFamily
  terminalisingEnemyCompression : CompressionFamily


------------------------------------------------------------------------
-- A projection-inadequacy receipt carries the exact witness, not merely prose.
------------------------------------------------------------------------

record ProjectionInadequacyReceipt
    {Situated Surface Outcome : Set}
    (observe : Situated → Surface)
    (target : Situated → Outcome) : Set₁ where
  constructor projection-inadequacy-receipt
  field
    family : CompressionFamily
    observerReference : String
    consumerReference : String
    lostDistinctionReference : String
    witness : INF.NonFactorabilityWitness observe target
    observerMayBeLocallyUseful : Bool
    observerMayBeLocallyUsefulIsTrue : observerMayBeLocallyUseful ≡ true
    observerIsSemanticallyExhaustive : Bool
    observerIsSemanticallyExhaustiveIsFalse : observerIsSemanticallyExhaustive ≡ false
    posthocRelabellingRecoversLostDistinction : Bool
    posthocRelabellingRecoversLostDistinctionIsFalse :
      posthocRelabellingRecoversLostDistinction ≡ false
    sharedPatternMakesHistoricalDoctrinesIdentical : Bool
    sharedPatternMakesHistoricalDoctrinesIdenticalIsFalse :
      sharedPatternMakesHistoricalDoctrinesIdentical ≡ false

open ProjectionInadequacyReceipt public

projectionCannotFactorTarget :
  ∀ {Situated Surface Outcome : Set}
    {observe : Situated → Surface}
    {target : Situated → Outcome} →
  ProjectionInadequacyReceipt observe target →
  INF.FactorsThrough observe target → ⊥
projectionCannotFactorTarget receipt =
  INF.witnessRulesOutEveryFlatFactorisation (witness receipt)

projectionCannotBeRepairedByPostcomposition :
  ∀ {Situated Surface Recharted Outcome : Set}
    {observe : Situated → Surface}
    {target : Situated → Outcome} →
  ProjectionInadequacyReceipt observe target →
  (rechart : Surface → Recharted) →
  INF.FactorsThrough (λ state → rechart (observe state)) target → ⊥
projectionCannotBeRepairedByPostcomposition receipt rechart =
  INF.rechartingCannotRecoverErasedPhenomenon rechart (witness receipt)

------------------------------------------------------------------------
-- The audit surface tells downstream consumers what disappeared.
------------------------------------------------------------------------

record InvisibilityAudit : Set where
  constructor invisibility-audit
  field
    observer : String
    collision : String
    distinctionMadeInvisible : String
    affectedConsumer : String
    requiredResidual : String
    correctionChannelRequired : Bool
    interpretiveLensReference : String
    interpretiveLensAutomaticallyWorldTruth : Bool
    interpretiveLensAutomaticallyWorldTruthIsFalse :
      interpretiveLensAutomaticallyWorldTruth ≡ false

open InvisibilityAudit public

------------------------------------------------------------------------
-- Positive repair must add information rather than merely rename the quotient.
------------------------------------------------------------------------

record ResidualRepair
    {Situated Surface Residual : Set}
    (observe : Situated → Surface) : Set₁ where
  constructor residual-repair
  field
    residual : Situated → Residual
    left right : Situated
    oldCollision : observe left ≡ observe right
    residualSeparates : residual left ≡ residual right → ⊥

open ResidualRepair public

residualRepairStrictlyRefines :
  ∀ {Situated Surface Residual : Set}
    {observe : Situated → Surface} →
  (repair : ResidualRepair {Residual = Residual} observe) →
  Observer.StrictRefinement
    observe
    (Observer.pairObserver observe (residual repair))
residualRepairStrictlyRefines {observe = observe} repair =
  Observer.strictPairRefinement
    observe
    (residual repair)
    (left repair)
    (right repair)
    (oldCollision repair)
    (residualSeparates repair)

------------------------------------------------------------------------
-- Category adequacy is not ontology. This directly reuses the generic audit.
------------------------------------------------------------------------

categoryAuthorityBoundary : CategoryAudit.CategoryAuthorityBoundary
categoryAuthorityBoundary = CategoryAudit.canonicalCategoryAuthorityBoundary

categoryTechnicalAdequacyDoesNotProveNeutrality :
  CategoryAudit.technicalAdequacyImpliesPoliticalNeutrality categoryAuthorityBoundary ≡ false
categoryTechnicalAdequacyDoesNotProveNeutrality = refl

categoryTechnicalAdequacyDoesNotProveExhaustiveness :
  CategoryAudit.completeDataImpliesSemanticExhaustiveness categoryAuthorityBoundary ≡ false
categoryTechnicalAdequacyDoesNotProveExhaustiveness = refl

------------------------------------------------------------------------
-- Terminalisation is a stricter failure mode than ordinary coarse projection.
-- It can additionally damage the correction interface itself.
------------------------------------------------------------------------

record TerminalisationRiskBoundary : Set where
  constructor terminalisation-risk-boundary
  field
    terminalisationIsOnlyOrdinaryProjectionLoss : Bool
    terminalisationIsOnlyOrdinaryProjectionLossIsFalse :
      terminalisationIsOnlyOrdinaryProjectionLoss ≡ false
    terminalisationMayCloseCorrectionChannel : Bool
    terminalisationMayCloseCorrectionChannelIsTrue :
      terminalisationMayCloseCorrectionChannel ≡ true
    terminalisationMayReclassifyDissentAsConfirmingFault : Bool
    terminalisationMayReclassifyDissentAsConfirmingFaultIsTrue :
      terminalisationMayReclassifyDissentAsConfirmingFault ≡ true
    humanGroupMayBePromotedToTerminalEnemyPredicate : Bool
    humanGroupMayBePromotedToTerminalEnemyPredicateIsFalse :
      humanGroupMayBePromotedToTerminalEnemyPredicate ≡ false
    describingTerminalisationLicencesDomination : Bool
    describingTerminalisationLicencesDominationIsFalse :
      describingTerminalisationLicencesDomination ≡ false

open TerminalisationRiskBoundary public

canonicalTerminalisationRiskBoundary : TerminalisationRiskBoundary
canonicalTerminalisationRiskBoundary =
  terminalisation-risk-boundary
    false refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Generic no-collapse laws.
------------------------------------------------------------------------

data LocalUsefulnessImpliesSemanticExhaustiveness : Set where
data SharedNonfactorabilityImpliesSameHistoricalDoctrine : Set where
data CriticalLensAutomaticallyProvesEmpiricalIntent : Set where
data PosthocInclusiveRelabellingRepairsErasedRelation : Set where
data TerminalisationEqualsEveryCoarseObserver : Set where

localUsefulnessDoesNotMakeObserverExhaustive :
  LocalUsefulnessImpliesSemanticExhaustiveness → ⊥
localUsefulnessDoesNotMakeObserverExhaustive ()

sharedPatternDoesNotMergeHistoricalDoctrines :
  SharedNonfactorabilityImpliesSameHistoricalDoctrine → ⊥
sharedPatternDoesNotMergeHistoricalDoctrines ()

criticalLensDoesNotAutomaticallyProveIntent :
  CriticalLensAutomaticallyProvesEmpiricalIntent → ⊥
criticalLensDoesNotAutomaticallyProveIntent ()

inclusiveRelabellingCannotRepairErasedRelation :
  PosthocInclusiveRelabellingRepairsErasedRelation → ⊥
inclusiveRelabellingCannotRepairErasedRelation ()

terminalisationIsNotEveryCoarseObserver :
  TerminalisationEqualsEveryCoarseObserver → ⊥
terminalisationIsNotEveryCoarseObserver ()

record DominantChartEpistemicCompressionBoundary : Set where
  constructor dominant-chart-epistemic-compression-boundary
  field
    usefulObserverMayStillBeLossy : Bool
    usefulObserverMayStillBeLossyIsTrue : usefulObserverMayStillBeLossy ≡ true
    observerOutputIsOntologyByDefault : Bool
    observerOutputIsOntologyByDefaultIsFalse : observerOutputIsOntologyByDefault ≡ false
    relabellingCollapsedObserverRestoresErasedDistinction : Bool
    relabellingCollapsedObserverRestoresErasedDistinctionIsFalse :
      relabellingCollapsedObserverRestoresErasedDistinction ≡ false
    genuineRepairMayRequireNewResidualCoordinate : Bool
    genuineRepairMayRequireNewResidualCoordinateIsTrue :
      genuineRepairMayRequireNewResidualCoordinate ≡ true
    sharedFormalFailureImpliesSharedPolitics : Bool
    sharedFormalFailureImpliesSharedPoliticsIsFalse :
      sharedFormalFailureImpliesSharedPolitics ≡ false
    terminalisationHasExtraCorrectionClosureRisk : Bool
    terminalisationHasExtraCorrectionClosureRiskIsTrue :
      terminalisationHasExtraCorrectionClosureRisk ≡ true

canonicalDominantChartEpistemicCompressionBoundary :
  DominantChartEpistemicCompressionBoundary
canonicalDominantChartEpistemicCompressionBoundary =
  dominant-chart-epistemic-compression-boundary
    true refl
    false refl
    false refl
    true refl
    false refl
    true refl
