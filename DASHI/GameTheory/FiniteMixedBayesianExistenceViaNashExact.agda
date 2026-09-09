module DASHI.GameTheory.FiniteMixedBayesianExistenceViaNashExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteIncompleteInformationBayesianExact as Bayesian
import DASHI.GameTheory.FiniteBayesianAgentNormalFormReductionExact as Reduction
import DASHI.GameTheory.FiniteMixedNashReceiptBindingExact as Binding
import DASHI.GameTheory.Nash1950CorrectedExistenceAlignmentExact as Nash1950

------------------------------------------------------------------------
-- FINITE MIXED BAYESIAN EXISTENCE VIA THE CORRECTED NASH CONSUMER
--
-- Once a finite common-prior Bayesian game is represented as its finite agent
-- normal form, no second fixed-point theorem is required for the mixed Bayesian
-- existence consumer.  The only theorem leaf is the same corrected Nash 1950
-- existence theorem for the exact finite normal-form receipt.
------------------------------------------------------------------------

record BayesianNash1950AlignmentCoordinates
    {G : Game.StrategicGame}
    (B : Bayesian.FiniteBayesianGame G)
    (U : Mixed.FiniteExpectedUtilitySurface G)
    (reduction : Reduction.FiniteBayesianNormalFormCoordinates B U) : Set₁ where
  constructor bayesian-nash1950-alignment-coordinates
  field
    ProfileIsFiniteStrategyProduct : Set
    profileIsFiniteStrategyProduct : ProfileIsFiniteStrategyProduct

    MixedStrategySimplexRealisation : Set
    mixedStrategySimplexRealisation : MixedStrategySimplexRealisation

    IndependentProductLawConstruction : Set
    independentProductLawConstruction : IndependentProductLawConstruction

    FiniteExpectedUtilityMatchesSourcePayoffExtension : Set
    finiteExpectedUtilityMatchesSourcePayoffExtension :
      FiniteExpectedUtilityMatchesSourcePayoffExtension

    exactGameReference : String
    profileProductReference : String
    simplexReference : String
    expectedUtilityReference : String

open BayesianNash1950AlignmentCoordinates public

normalFormNashCoordinates :
  ∀ {G}
    {B : Bayesian.FiniteBayesianGame G}
    {U : Mixed.FiniteExpectedUtilitySurface G}
    {reduction : Reduction.FiniteBayesianNormalFormCoordinates B U} →
  BayesianNash1950AlignmentCoordinates B U reduction →
  Nash1950.Nash1950ApplicationCoordinates
    (Reduction.bayesianNormalFormGame B U
      (Reduction.contingentExtensionality reduction))
    (Reduction.bayesianNormalFormExpectedUtility B U
      (Reduction.contingentExtensionality reduction))
normalFormNashCoordinates {B = B} {U = U} {reduction = reduction} coordinates =
  Nash1950.nash1950-application-coordinates
    (Reduction.finiteAgentNormalForm reduction)
    (ProfileIsFiniteStrategyProduct coordinates)
    (profileIsFiniteStrategyProduct coordinates)
    (MixedStrategySimplexRealisation coordinates)
    (mixedStrategySimplexRealisation coordinates)
    (IndependentProductLawConstruction coordinates)
    (independentProductLawConstruction coordinates)
    (FiniteExpectedUtilityMatchesSourcePayoffExtension coordinates)
    (finiteExpectedUtilityMatchesSourcePayoffExtension coordinates)
    (exactGameReference coordinates)
    (profileProductReference coordinates)
    (simplexReference coordinates)
    (expectedUtilityReference coordinates)

nashNormalFormImpliesMixedBayesian :
  ∀ {G}
    {B : Bayesian.FiniteBayesianGame G}
    {U : Mixed.FiniteExpectedUtilitySurface G}
    (reduction : Reduction.FiniteBayesianNormalFormCoordinates B U) →
  Binding.StandardFiniteMixedNashForReceipt
    (Reduction.bayesianNormalFormGame B U
      (Reduction.contingentExtensionality reduction))
    (Reduction.bayesianNormalFormExpectedUtility B U
      (Reduction.contingentExtensionality reduction))
    (Reduction.finiteAgentNormalForm reduction) →
  Reduction.FiniteMixedBayesianEquilibrium B U reduction
nashNormalFormImpliesMixedBayesian reduction bound =
  Reduction.finite-mixed-bayesian-equilibrium
    (Binding.equilibrium bound)
    (Binding.exactFiniteNormalForm bound)
    (Reduction.deviationUtilityPreservation reduction)
    "derived from corrected Nash equilibrium on the exact finite Bayesian agent normal form"

finiteMixedBayesianConditionalOnNash1950 :
  ∀ {G}
    {B : Bayesian.FiniteBayesianGame G}
    {U : Mixed.FiniteExpectedUtilitySurface G}
    (reduction : Reduction.FiniteBayesianNormalFormCoordinates B U)
    (coordinates : BayesianNash1950AlignmentCoordinates B U reduction) →
  Nash1950.Nash1950CorrectedExistenceClaim
    (Reduction.bayesianNormalFormGame B U
      (Reduction.contingentExtensionality reduction))
    (Reduction.bayesianNormalFormExpectedUtility B U
      (Reduction.contingentExtensionality reduction))
    (normalFormNashCoordinates coordinates)
  →
  Reduction.FiniteMixedBayesianExistenceConsumer B U reduction
finiteMixedBayesianConditionalOnNash1950 reduction coordinates =
  nashNormalFormImpliesMixedBayesian reduction

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data BayesianReductionMeansSecondFixedPointTheoremPermission : Set where

data MixedBayesianMeansPureBayesianPermission : Set where

data NashSourceAlignmentMeansBayesianProofCertifiedPermission : Set where

data AgentNormalFormMeansPosteriorSemanticsPermission : Set where

bayesianReductionDoesNotNeedSecondFixedPointTheorem :
  BayesianReductionMeansSecondFixedPointTheoremPermission → ⊥
bayesianReductionDoesNotNeedSecondFixedPointTheorem ()

mixedBayesianDoesNotCollapseToPureBayesian :
  MixedBayesianMeansPureBayesianPermission → ⊥
mixedBayesianDoesNotCollapseToPureBayesian ()

nashSourceAlignmentStillDoesNotCertifyBayesianExistence :
  NashSourceAlignmentMeansBayesianProofCertifiedPermission → ⊥
nashSourceAlignmentStillDoesNotCertifyBayesianExistence ()

normalFormReductionDoesNotInventPosteriorSemantics :
  AgentNormalFormMeansPosteriorSemanticsPermission → ⊥
normalFormReductionDoesNotInventPosteriorSemantics ()

record FiniteMixedBayesianViaNashBoundary : Set where
  constructor finite-mixed-bayesian-via-nash-boundary
  field
    finiteAgentNormalFormReductionExplicit : Bool
    exactNashFiniteReceiptReused : Bool
    secondFixedPointTheoremRequired : Bool
    pureBayesianEquilibriumIdentifiedWithMixedBayesian : Bool
    posteriorSemanticsInventedByReduction : Bool

canonicalFiniteMixedBayesianViaNashBoundary : FiniteMixedBayesianViaNashBoundary
canonicalFiniteMixedBayesianViaNashBoundary =
  finite-mixed-bayesian-via-nash-boundary true true false false false
