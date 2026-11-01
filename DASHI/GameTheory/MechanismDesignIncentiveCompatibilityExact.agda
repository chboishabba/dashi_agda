module DASHI.GameTheory.MechanismDesignIncentiveCompatibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- MECHANISM DESIGN / DIRECT-REVELATION INCENTIVES
--
-- Reports, private types, outcomes and utilities are distinct coordinates.
-- Dominant-strategy incentive compatibility says truthful reporting weakly
-- dominates every unilateral misreport while the other reports are held fixed.
-- It does not imply individual rationality, budget balance, efficiency,
-- empirical truthfulness or Bayesian incentive compatibility.
------------------------------------------------------------------------

record MechanismDesignProblem : Set₁ where
  constructor mechanism-design-problem
  field
    Agent Outcome ReportProfile : Set
    Type Report Utility : Agent → Set

    truthfulReport :
      (agent : Agent) →
      Type agent →
      Report agent

    reportAt :
      ReportProfile →
      (agent : Agent) →
      Report agent

    replaceReport :
      (reports : ReportProfile) →
      (agent : Agent) →
      Report agent →
      ReportProfile

    replacementInstalled :
      (reports : ReportProfile) →
      (agent : Agent) →
      (report : Report agent) →
      reportAt (replaceReport reports agent report) agent ≡ report

    DifferentAgent : Agent → Agent → Set

    replacementLeavesOthers :
      (reports : ReportProfile) →
      (agent : Agent) →
      (report : Report agent) →
      (other : Agent) →
      DifferentAgent agent other →
      reportAt (replaceReport reports agent report) other
      ≡ reportAt reports other

    mechanism : ReportProfile → Outcome

    utility :
      (agent : Agent) →
      Type agent →
      Outcome →
      Utility agent

    WeaklyPrefersUtility :
      (agent : Agent) →
      Utility agent → Utility agent → Set

    problemReference : String
    typeReference : String
    mechanismReference : String
    utilityReference : String

open MechanismDesignProblem public

truthfulProfileFor :
  (M : MechanismDesignProblem) →
  (reports : ReportProfile M) →
  (agent : Agent M) →
  Type M agent →
  ReportProfile M
truthfulProfileFor M reports agent type =
  replaceReport M reports agent (truthfulReport M agent type)

misreportProfileFor :
  (M : MechanismDesignProblem) →
  (reports : ReportProfile M) →
  (agent : Agent M) →
  Report M agent →
  ReportProfile M
misreportProfileFor = replaceReport

DominantStrategyTruthfulFor :
  (M : MechanismDesignProblem) →
  (agent : Agent M) →
  Set₁
DominantStrategyTruthfulFor M agent =
  (trueType : Type M agent) →
  (reports : ReportProfile M) →
  (alternative : Report M agent) →
  WeaklyPrefersUtility M agent
    (utility M agent trueType
      (mechanism M (truthfulProfileFor M reports agent trueType)))
    (utility M agent trueType
      (mechanism M (misreportProfileFor M reports agent alternative)))

record DominantStrategyIncentiveCompatible
    (M : MechanismDesignProblem) : Set₁ where
  constructor dominant-strategy-incentive-compatible
  field
    truthfulDominates :
      (agent : Agent M) →
      DominantStrategyTruthfulFor M agent

    dsicReference : String

open DominantStrategyIncentiveCompatible public

------------------------------------------------------------------------
-- Individual rationality and social-choice implementation are separate.
------------------------------------------------------------------------

record IndividualRationality
    (M : MechanismDesignProblem) : Set₁ where
  constructor individual-rationality
  field
    OutsideOption : Agent M → Set
    outsideUtility :
      (agent : Agent M) →
      Type M agent →
      OutsideOption agent →
      Utility M agent

    participationWeaklyPreferred :
      (agent : Agent M) →
      (trueType : Type M agent) →
      (reports : ReportProfile M) →
      (outside : OutsideOption agent) →
      WeaklyPrefersUtility M agent
        (utility M agent trueType
          (mechanism M (truthfulProfileFor M reports agent trueType)))
        (outsideUtility agent trueType outside)

    participationReference : String

open IndividualRationality public

record SocialChoiceImplementation
    (M : MechanismDesignProblem) : Set₁ where
  constructor social-choice-implementation
  field
    TypeProfile : Set
    typeAt : TypeProfile → (agent : Agent M) → Type M agent
    SocialChoiceOutcome : TypeProfile → Outcome M

    reportsForTypes : TypeProfile → ReportProfile M

    reportsTruthful :
      (types : TypeProfile) →
      (agent : Agent M) →
      reportAt M (reportsForTypes types) agent
      ≡ truthfulReport M agent (typeAt types agent)

    implementsChoice :
      (types : TypeProfile) →
      mechanism M (reportsForTypes types)
      ≡ SocialChoiceOutcome types

    implementationReference : String

open SocialChoiceImplementation public

------------------------------------------------------------------------
-- Additional mechanism properties stay independent.
------------------------------------------------------------------------

record MechanismPropertyBundle
    (M : MechanismDesignProblem) : Set₁ where
  constructor mechanism-property-bundle
  field
    BudgetBalance : Set
    Efficient : Set
    StrategyProof : Set
    BayesianIncentiveCompatible : Set

    propertyReference : String

open MechanismPropertyBundle public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data DSICMeansIndividualRationalityPermission : Set where

data DSICMeansBudgetBalancePermission : Set where

data DSICMeansEfficiencyPermission : Set where

data DSICMeansBayesianICPermission : Set where

data ReportMeansTrueTypePermission : Set where

data TruthfulEquilibriumMeansObservedHonestyPermission : Set where

data MechanismOutcomeMeansMoralOptimumPermission : Set where

data IncentiveCompatibilityMeansLegalAuthorityPermission : Set where

DSICDoesNotAutomaticallyGiveIndividualRationality :
  DSICMeansIndividualRationalityPermission → ⊥
DSICDoesNotAutomaticallyGiveIndividualRationality ()

DSICDoesNotAutomaticallyGiveBudgetBalance : DSICMeansBudgetBalancePermission → ⊥
DSICDoesNotAutomaticallyGiveBudgetBalance ()

DSICDoesNotAutomaticallyGiveEfficiency : DSICMeansEfficiencyPermission → ⊥
DSICDoesNotAutomaticallyGiveEfficiency ()

DSICDoesNotAutomaticallyGiveBayesianIC : DSICMeansBayesianICPermission → ⊥
DSICDoesNotAutomaticallyGiveBayesianIC ()

reportDoesNotBecomeTrueType : ReportMeansTrueTypePermission → ⊥
reportDoesNotBecomeTrueType ()

truthfulDominanceDoesNotProveObservedHonesty :
  TruthfulEquilibriumMeansObservedHonestyPermission → ⊥
truthfulDominanceDoesNotProveObservedHonesty ()

mechanismOutcomeDoesNotCreateMoralOptimum :
  MechanismOutcomeMeansMoralOptimumPermission → ⊥
mechanismOutcomeDoesNotCreateMoralOptimum ()

incentiveCompatibilityDoesNotCreateLegalAuthority :
  IncentiveCompatibilityMeansLegalAuthorityPermission → ⊥
incentiveCompatibilityDoesNotCreateLegalAuthority ()

record MechanismDesignBoundary : Set where
  constructor mechanism-design-boundary
  field
    privateTypeAndReportSeparated : Bool
    unilateralReportReplacementExplicit : Bool
    DSICExplicit : Bool
    individualRationalitySeparate : Bool
    socialChoiceImplementationSeparate : Bool
    budgetBalanceSeparate : Bool
    BayesianICSeparate : Bool
    truthfulDominanceAutomaticallyEmpiricalHonesty : Bool

canonicalMechanismDesignBoundary : MechanismDesignBoundary
canonicalMechanismDesignBoundary =
  mechanism-design-boundary true true true true true true true false
