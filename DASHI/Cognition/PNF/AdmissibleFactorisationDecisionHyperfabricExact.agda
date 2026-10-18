module DASHI.Cognition.PNF.AdmissibleFactorisationDecisionHyperfabricExact where

------------------------------------------------------------------------
-- ADMISSIBLE FACTORISATION / DECISION / MEMORY SPINE
--
-- DASHI CONTRIBUTION
--
-- Cross-weld the repo-native binary-in-ternary embedding, ternary-to-binary
-- loss witness, consumer-relative factorisation, decision multiplicity,
-- memory/learning updates and trauma/current-assessment separation.
--
-- The governing rule is:
--
--   a coarse observation is admissible for a declared consumer exactly when
--   that consumer descends through the observation; adequacy for one consumer
--   does not make the observation reconstructive or world-complete.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.ComputerScience.BinaryBalancedTernarySubcarrierExact as BinaryInTernary
import DASHI.Cognition.PNF.BinaryBalancedTernaryAggregateLossExact as TernaryLoss
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Cognition.PNF.DecisionActionProjectionNonFactorabilityExact as DecisionNF
import DASHI.Cognition.PNF.DecisionActionFibreMultiplicityExact as DecisionFibre
import DASHI.Cognition.PNF.MemoryFibre as Memory
import DASHI.Cognition.PNF.LearningAlgebra as Learning
import DASHI.Cognition.PNF.FibreLearningDynamics as FibreLearning
import DASHI.Reasoning.TraumaAttractorBranchRegulationExact as Trauma
import DASHI.Reasoning.AttractorAlignedBranchSelectionExact as Branch

AdmissibleFor :
  ∀ {State Surface Outcome : Set} →
  (State → Surface) →
  (State → Outcome) →
  Set
AdmissibleFor observe consumer =
  Descent.ConsumerSufficient observe consumer

binaryEmbeddingRoundTrip =
  BinaryInTernary.binaryTernaryRoundTrip

aggregateDirectionalLoss =
  TernaryLoss.aggregateErasesDisagreementDirection

actionDoesNotRecoverFineDecisionState =
  DecisionNF.actionCannotRecoverFineDecisionState

------------------------------------------------------------------------
-- Trauma/deformation history alone is not an adequate quotient for current
-- branch decision.  Same history coordinate, different current branch,
-- different current marginal decision.
------------------------------------------------------------------------

data TraumaDecisionEpisode : Set where
  prematureExploration : TraumaDecisionEpisode
  prematureDeadEnd : TraumaDecisionEpisode

historyOnlyObserver :
  TraumaDecisionEpisode → Trauma.TraumaBranchDeformation
historyOnlyObserver prematureExploration = Trauma.prematureClosure
historyOnlyObserver prematureDeadEnd = Trauma.prematureClosure

currentDecisionConsumer :
  TraumaDecisionEpisode → Branch.MarginalDecision
currentDecisionConsumer prematureExploration =
  Trauma.regulatedDecision Trauma.prematureClosure Branch.exploratoryRoute
currentDecisionConsumer prematureDeadEnd =
  Trauma.regulatedDecision Trauma.prematureClosure Branch.attractiveDeadEnd

sameTraumaHistory :
  historyOnlyObserver prematureExploration
  ≡ historyOnlyObserver prematureDeadEnd
sameTraumaHistory = refl

differentCurrentDecision :
  currentDecisionConsumer prematureExploration
  ≡ currentDecisionConsumer prematureDeadEnd →
  ⊥
differentCurrentDecision ()

traumaHistoryOnlyNonDescent :
  Descent.ConsumerNonDescentWitness
    historyOnlyObserver currentDecisionConsumer
traumaHistoryOnlyNonDescent =
  Descent.consumerNonDescentWitness
    prematureExploration
    prematureDeadEnd
    sameTraumaHistory
    differentCurrentDecision

currentDecisionDoesNotFactorThroughTraumaHistoryAlone :
  Descent.FactorsThrough
    historyOnlyObserver currentDecisionConsumer → ⊥
currentDecisionDoesNotFactorThroughTraumaHistoryAlone =
  Descent.nonDescentWitnessBlocksFactorization
    traumaHistoryOnlyNonDescent

record AdmissibleFactorisationDecisionBoundary : Set where
  constructor admissible-factorisation-decision-boundary
  field
    binaryMayBeExactDeclaredSubcarrier : Bool
    binaryObservationReconstructsWholeTernaryCarrier : Bool
    coarseActionReconstructsFineDecisionState : Bool
    rememberedContentEqualsCurrentActionPolicy : Bool
    traumaHistoryAloneDeterminesCurrentDecision : Bool
    adequacyIsConsumerIndexed : Bool
    oneConsumerAdequacyMeansWorldCompleteness : Bool

canonicalAdmissibleFactorisationDecisionBoundary :
  AdmissibleFactorisationDecisionBoundary
canonicalAdmissibleFactorisationDecisionBoundary =
  admissible-factorisation-decision-boundary
    true false false false false true false
