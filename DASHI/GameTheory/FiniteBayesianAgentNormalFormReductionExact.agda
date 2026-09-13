module DASHI.GameTheory.FiniteBayesianAgentNormalFormReductionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Rational.Base using (ℚ; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteMixedNashProductCorrectionExact as Correction
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian

------------------------------------------------------------------------
-- FINITE BAYESIAN GAME -> AGENT/CONTINGENT-PLAN NORMAL FORM
--
-- A finite Bayesian game may be represented as a strategic normal-form game
-- whose pure strategies are complete contingent plans.  In intensional Agda,
-- Bayesian.deviatingPlanInstalled is only pointwise in the signal, while
-- StrategicGame.deviationInstalls asks for equality of the whole contingent
-- strategy.  We therefore require the exact extensionality bridge explicitly.
--
-- The resulting finite mixed-Nash theorem is a MIXED law over contingent plans;
-- it is not silently identified with the existing pure FiniteBayesianNash carrier.
------------------------------------------------------------------------

record ContingentPlanExtensionality
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G) : Set₁ where
  constructor contingent-plan-extensionality
  field
    extensionality :
      (player : Game.Player G) →
      (left right : Bayesian.Signal B player → Game.Strategy G player) →
      ((signal : Bayesian.Signal B player) → left signal ≡ right signal) →
      left ≡ right
    reference : String

open ContingentPlanExtensionality public

bayesianNormalFormGame :
  {G : Game.StrategicGame} →
  (B : Bayesian.FiniteBayesianGame G) →
  (U : Mixed.FiniteExpectedUtilitySurface G) →
  ContingentPlanExtensionality B →
  Game.StrategicGame
bayesianNormalFormGame {G} B U ext =
  Game.strategic-game
    (Game.Player G)
    (Bayesian.PlanProfile B)
    (Bayesian.PlanProfile B)
    (λ player → Bayesian.Signal B player → Game.Strategy G player)
    (Bayesian.contingentStrategyAt B)
    (Bayesian.deviatePlan B)
    (λ plans player alternative →
      ContingentPlanExtensionality.extensionality ext
        player
        (Bayesian.contingentStrategyAt B
          (Bayesian.deviatePlan B plans player alternative) player)
        alternative
        (Bayesian.deviatingPlanInstalled B plans player alternative))
    (λ plans → plans)
    (λ player better worse →
      Bayesian.worldExpectedUtility B U player worse
        (Bayesian.NormalizedFiniteWorldPrior.atoms (Bayesian.prior B))
      ≤
      Bayesian.worldExpectedUtility B U player better
        (Bayesian.NormalizedFiniteWorldPrior.atoms (Bayesian.prior B)))
    (λ player better worse →
      Bayesian.worldExpectedUtility B U player worse
        (Bayesian.NormalizedFiniteWorldPrior.atoms (Bayesian.prior B))
      <
      Bayesian.worldExpectedUtility B U player better
        (Bayesian.NormalizedFiniteWorldPrior.atoms (Bayesian.prior B)))
    (λ player better worse strict → ℚP.<⇒≤ strict)
    "finite Bayesian contingent-plan agent normal form"
    "normal-form outcome is the complete contingent-plan profile"
    "preference is finite-common-prior expected utility"

bayesianNormalFormNumericalPayoff :
  {G : Game.StrategicGame}
  (B : Bayesian.FiniteBayesianGame G)
  (U : Mixed.FiniteExpectedUtilitySurface G)
  (ext : ContingentPlanExtensionality B) →
  Game.NumericalPayoffRealisation (bayesianNormalFormGame B U ext)
bayesianNormalFormNumericalPayoff B U ext =
  Game.numerical-payoff-realisation
    ℚ
    _≤_
    _<_
    (λ player plans →
      Bayesian.worldExpectedUtility B U player plans
        (Bayesian.NormalizedFiniteWorldPrior.atoms (Bayesian.prior B)))
    (λ player left right weak → weak)
    (λ player left right strict → strict)
    "finite common-prior expected utility"
    "rational order"

bayesianNormalFormExpectedUtility :
  {G : Game.StrategicGame}
  (B : Bayesian.FiniteBayesianGame G)
  (U : Mixed.FiniteExpectedUtilitySurface G)
  (ext : ContingentPlanExtensionality B) →
  Mixed.FiniteExpectedUtilitySurface (bayesianNormalFormGame B U ext)
bayesianNormalFormExpectedUtility B U ext =
  Mixed.finite-expected-utility-surface
    (bayesianNormalFormNumericalPayoff B U ext)
    (λ q → q)
    ⊤
    tt
    "Bayesian common-prior expected utility is the normal-form cardinal payoff"
    "finite rational prior from FiniteBayesianGame"

record FiniteBayesianNormalFormCoordinates
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G)
    (U : Mixed.FiniteExpectedUtilitySurface G) : Set₁ where
  constructor finite-bayesian-normal-form-coordinates
  field
    contingentExtensionality : ContingentPlanExtensionality B
    finiteAgentNormalForm :
      Correction.FiniteNormalFormReceipt
        (bayesianNormalFormGame B U contingentExtensionality)

    AgentNormalFormPreservesBayesianDeviationUtility : Set
    deviationUtilityPreservation : AgentNormalFormPreservesBayesianDeviationUtility

    reductionReference : String

open FiniteBayesianNormalFormCoordinates public

record FiniteMixedBayesianEquilibrium
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G)
    (U : Mixed.FiniteExpectedUtilitySurface G)
    (coordinates : FiniteBayesianNormalFormCoordinates B U) : Set₁ where
  constructor finite-mixed-bayesian-equilibrium
  field
    normalFormEquilibrium :
      Correction.StandardFiniteMixedNashEquilibrium
        (bayesianNormalFormGame B U (contingentExtensionality coordinates))
        (bayesianNormalFormExpectedUtility B U (contingentExtensionality coordinates))

    finiteNormalFormMatchesCoordinates :
      Correction.StandardFiniteMixedNashEquilibrium.finiteNormalForm normalFormEquilibrium
      ≡ finiteAgentNormalForm coordinates

    reductionSoundness : AgentNormalFormPreservesBayesianDeviationUtility coordinates
    equilibriumReference : String

open FiniteMixedBayesianEquilibrium public

------------------------------------------------------------------------
-- Consumer-minimal existence target.  Nash existence can now be reused on the
-- finite agent normal form.  No separate fixed-point theorem is needed for this
-- bounded mixed-Bayesian existence consumer once the reduction coordinates are
-- supplied.
------------------------------------------------------------------------

FiniteMixedBayesianExistenceConsumer :
  {G : Game.StrategicGame}
  (B : Bayesian.FiniteBayesianGame G)
  (U : Mixed.FiniteExpectedUtilitySurface G)
  (coordinates : FiniteBayesianNormalFormCoordinates B U) → Set₁
FiniteMixedBayesianExistenceConsumer B U coordinates =
  FiniteMixedBayesianEquilibrium B U coordinates

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PointwisePlanEqualityMeansFunctionEqualityPermission : Set where

data MixedAgentNormalFormMeansPureBayesianNashPermission : Set where

data CommonPriorMeansPosteriorUpdatePermission : Set where

data AgentNormalFormMeansEmpiricalBehaviourPermission : Set where

pointwisePlanEqualityDoesNotManufactureFunctionEquality :
  PointwisePlanEqualityMeansFunctionEqualityPermission → ⊥
pointwisePlanEqualityDoesNotManufactureFunctionEquality ()

mixedAgentNormalFormDoesNotBecomePureBayesianNash :
  MixedAgentNormalFormMeansPureBayesianNashPermission → ⊥
mixedAgentNormalFormDoesNotBecomePureBayesianNash ()

commonPriorStillDoesNotInventPosteriorUpdate :
  CommonPriorMeansPosteriorUpdatePermission → ⊥
commonPriorStillDoesNotInventPosteriorUpdate ()

normalFormEquilibriumDoesNotPredictObservedPlay :
  AgentNormalFormMeansEmpiricalBehaviourPermission → ⊥
normalFormEquilibriumDoesNotPredictObservedPlay ()

record FiniteBayesianNormalFormBoundary : Set where
  constructor finite-bayesian-normal-form-boundary
  field
    contingentPlansBecomePureNormalFormStrategies : Bool
    functionExtensionalityAssumedImplicitly : Bool
    expectedUtilityReusedFromFinitePrior : Bool
    correctedProductMixedNashReused : Bool
    pureBayesianCarrierIdentifiedWithMixedBayesian : Bool
    separateBayesianFixedPointTheoremRequiredAfterReduction : Bool

canonicalFiniteBayesianNormalFormBoundary : FiniteBayesianNormalFormBoundary
canonicalFiniteBayesianNormalFormBoundary =
  finite-bayesian-normal-form-boundary
    true false true true false false
