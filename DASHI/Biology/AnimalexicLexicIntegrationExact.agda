module DASHI.Biology.AnimalexicLexicIntegrationExact where

------------------------------------------------------------------------
-- Upper Animalexic integration layer: latent embodied state remains separate
-- from behavioural motifs, communicative hypotheses, set-valued evidence and
-- interventional validation.  This module reuses the generic DASHI cores rather
-- than baking one particular ML stack into the formal system.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Biology.AnimalexicFormalSystemExact as Animal
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Core.SetValuedEvidenceConflictExact as Evidence
import DASHI.Core.ReopenableQuotientForestExact as Forest
import DASHI.Core.ExperimentLanguageEquivalenceExact as Experiment
import DASHI.Core.SufficientSupportFamilyInvalidationExact as Support
import DASHI.Core.ProvenanceClosureIndependenceExact as Provenance
import DASHI.Core.ConsumerIndexedSemanticDebtExact as Debt
import DASHI.Core.SafeEvidenceExtensionPromotionExact as Promotion
import DASHI.Core.FiniteRankedRefinementStabilizationExact as Ranked

------------------------------------------------------------------------
-- 1. Incremental factor state remains a dependency graph unless a particular
--    application supplies probabilistic semantics for its factors.
------------------------------------------------------------------------

AnimalFactorGraph : Set → Set → Set₁
AnimalFactorGraph = Animal.IncrementalFactorState

record LocalFactorInsertion
    {Variable Factor : Set}
    (graph : Animal.IncrementalFactorState Variable Factor) : Set₁ where
  constructor localFactorInsertion
  field
    insertedFactor : Factor
    Affected : Variable → Set
    affectedRequiresDependency :
      ∀ variable →
      Affected variable →
      Animal.DependsOn graph insertedFactor variable

open LocalFactorInsertion public

------------------------------------------------------------------------
-- 2. Behavioural syllables are latent recurring motifs, not semantic labels.
-- Keypoint-MoSeq motivates the pose-dynamics vocabulary; semantic promotion is
-- deliberately represented by a separate status/provenance surface.
------------------------------------------------------------------------

record BehaviourSyllable
    (Motif Interval Provenance : Set) : Set₁ where
  constructor behaviourSyllable
  field
    motif : Motif
    interval : Interval
    provenance : Provenance
    semanticStatus : Base.AlternativeStatus
    semanticPromotionReference : String

open BehaviourSyllable public

record BehaviourSyllableBoundary : Set where
  constructor behaviourSyllableBoundary
  field
    recurrentPoseMotifIsNotSemanticMeaning : Bool
    clusterIdentifierDoesNotNameBehaviourByItself : Bool
    contextAndInteractionCanSupplyLaterEvidence : Bool
    inactiveSemanticCandidateNeedNotBeRefuted : Bool

canonicalBehaviourSyllableBoundary : BehaviourSyllableBoundary
canonicalBehaviourSyllableBoundary =
  behaviourSyllableBoundary true true true true

------------------------------------------------------------------------
-- 3. The semantic layer is a reopenable quotient forest plus set-valued
--    evidence.  Family-level evidence can support {request,play} without
--    inventing a winner, while compressed alternatives retain ancestry.
------------------------------------------------------------------------

AnimalHypothesisForest : Set → Set → Set₁
AnimalHypothesisForest = Forest.ReopenableQuotientForest

AnimalSetValuedEvidence : Set → Set → Set → Set₁
AnimalSetValuedEvidence = Evidence.SetValuedEvidence

AnimalSupportFamily :
  ∀ {Assumption : Set} →
  (Assumption → Set) → Set → Set₁
AnimalSupportFamily {Assumption} Holds Claim =
  Support.SufficientSupportFamily Assumption Holds Claim

------------------------------------------------------------------------
-- 4. Interventional validation is relative to an explicit experiment language.
------------------------------------------------------------------------

AnimalExperimentLanguage : Set → Set₁
AnimalExperimentLanguage = Experiment.ExperimentLanguage

animalAdmissibleSeparatingExperimentRefutesSemanticEquivalence :
  ∀ {State Action Observation}
    {language : Experiment.ExperimentLanguage Action}
    {observe : State → Observation}
    {step : Action → State → State}
    {left right : State} →
  Experiment.AdmissibleSeparatingExperiment language observe step left right →
  Experiment.LanguageEquivalent language observe step left right →
  ⊥
animalAdmissibleSeparatingExperimentRefutesSemanticEquivalence =
  Experiment.admissibleSeparatingExperimentRefutesLanguageEquivalence

------------------------------------------------------------------------
-- 5. Upstream provenance, not modality names, governs independence.
------------------------------------------------------------------------

AnimalProvenanceSystem : Set → Set₁
AnimalProvenanceSystem = Provenance.ProvenanceSystem

animalSharedUpstreamRootRefutesIndependence :
  ∀ {Artifact}
    {system : Provenance.ProvenanceSystem Artifact}
    {left right : Artifact} →
  Provenance.SharedUpstreamRoot system left right →
  Provenance.IndependentByUpstreamClosure system left right →
  ⊥
animalSharedUpstreamRootRefutesIndependence =
  Provenance.sharedUpstreamRootRefutesIndependence

------------------------------------------------------------------------
-- 6. Unresolved semantic state becomes mandatory to resolve only when it is
--    relevant to the declared consumer and no longer covered by that consumer's
--    margin.
------------------------------------------------------------------------

AnimalSemanticDebt : Set → Set → Set₁
AnimalSemanticDebt = Debt.StructuredConsumerDebt

animalUncoveredRelevantDebtForcesResolution :
  ∀ {Residual Consumer}
    {debt : Debt.StructuredConsumerDebt Residual Consumer}
    {policy : Debt.DeferralPolicy debt}
    {residual : Residual}
    {consumer : Consumer} →
  Debt.NeedsResolution debt residual consumer →
  Debt.Deferred policy residual →
  ⊥
animalUncoveredRelevantDebtForcesResolution =
  Debt.needsResolutionRefutesDeferral

------------------------------------------------------------------------
-- 7. Finite counterexample-guided refinement can reuse the already-proved
--    ranked stabilization theorem once an Animalexic implementation supplies a
--    bounded rank increased by every unresolved strict split.
------------------------------------------------------------------------

AnimalRankedRefinementProcess : Set₁
AnimalRankedRefinementProcess = Ranked.RankedRefinementProcess

animalRankedRefinementStabilizes :
  (process : Ranked.RankedRefinementProcess) →
  (start : Ranked.Code process) →
  Ranked.StabilizationWitness process start
animalRankedRefinementStabilizes = Ranked.rankedRefinementStabilizes

------------------------------------------------------------------------
-- 8. Promotion monotonicity is only available along a safe evidence extension.
------------------------------------------------------------------------

AnimalClaimEvidenceOrder : Set → Set → Set₁
AnimalClaimEvidenceOrder = Promotion.ClaimEvidenceOrder

record AnimalLexicIntegrationBoundary : Set where
  constructor animalLexicIntegrationBoundary
  field
    factorGraphDoesNotForceProbabilityOnEveryFactor : Bool
    behaviouralSyllableDoesNotSupplyMeaning : Bool
    hypothesisCompressionRetainsReopenableAncestry : Bool
    setValuedEvidenceCanRetainAmbiguity : Bool
    conflictMustRemainExplicitBeforeNormalization : Bool
    semanticEquivalenceIsExperimentLanguageRelative : Bool
    evidenceIndependenceUsesUpstreamClosure : Bool
    semanticDebtIsConsumerIndexed : Bool
    boundedStrictRefinementCanReuseRankedStabilization : Bool
    promotionMonotonicityNeedsSafeEvidenceExtension : Bool

canonicalAnimalLexicIntegrationBoundary : AnimalLexicIntegrationBoundary
canonicalAnimalLexicIntegrationBoundary =
  animalLexicIntegrationBoundary
    true true true true true true true true true true
