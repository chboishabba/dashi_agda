module DASHI.Core.HorizonRobustInterventionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- HORIZON-ROBUST INTERVENTION
--
-- DASHI-original generic machinery.  This strengthens ordinary robustness by
-- quantifying over both still-live model hypotheses and declared horizon points.
-- It does not assign probabilities, discount rates, or political authority.
------------------------------------------------------------------------

record HorizonInterventionSystem
    (Hypothesis HorizonPoint Intervention Outcome : Set) : Set₁ where
  constructor horizon-intervention-system
  field
    baseline : Intervention
    predict : Hypothesis → HorizonPoint → Intervention → Outcome
    NoWorse : Outcome → Outcome → Set
    StrictlyBetter : Outcome → Outcome → Set

open HorizonInterventionSystem public

record RobustAcrossHypothesesAndHorizon
    {Hypothesis HorizonPoint Intervention Outcome : Set}
    (system : HorizonInterventionSystem Hypothesis HorizonPoint Intervention Outcome)
    (DeclaredHypothesis : Hypothesis → Set)
    (DeclaredHorizon : HorizonPoint → Set)
    (intervention : Intervention) : Set₁ where
  constructor robust-across-hypotheses-and-horizon
  field
    noWorse :
      (hypothesis : Hypothesis) →
      DeclaredHypothesis hypothesis →
      (point : HorizonPoint) →
      DeclaredHorizon point →
      NoWorse system
        (predict system hypothesis point intervention)
        (predict system hypothesis point (baseline system))

open RobustAcrossHypothesesAndHorizon public

record TerminalOnlyAssessment
    {Hypothesis HorizonPoint Intervention Outcome : Set}
    (system : HorizonInterventionSystem Hypothesis HorizonPoint Intervention Outcome)
    (terminalPoint : HorizonPoint)
    (intervention : Intervention) : Set₁ where
  constructor terminal-only-assessment
  field
    HypothesisReceipt : Set
    hypothesisReceipt : HypothesisReceipt
    terminalReference : String

open TerminalOnlyAssessment public

------------------------------------------------------------------------
-- Refinement in either live hypothesis set or horizon set preserves a proof
-- already universal over the wider declared surface.
------------------------------------------------------------------------

PredicateRefines : ∀ {A : Set} → (A → Set) → (A → Set) → Set
PredicateRefines stronger weaker = ∀ x → stronger x → weaker x

horizonRobustnessSurvivesRefinement :
  ∀ {Hypothesis HorizonPoint Intervention Outcome}
    {system : HorizonInterventionSystem Hypothesis HorizonPoint Intervention Outcome}
    {strongH weakH : Hypothesis → Set}
    {strongT weakT : HorizonPoint → Set}
    {intervention : Intervention} →
  PredicateRefines strongH weakH →
  PredicateRefines strongT weakT →
  RobustAcrossHypothesesAndHorizon system weakH weakT intervention →
  RobustAcrossHypothesesAndHorizon system strongH strongT intervention
horizonRobustnessSurvivesRefinement refineH refineT robust =
  robust-across-hypotheses-and-horizon
    λ hypothesis declaredH point declaredT →
      noWorse robust
        hypothesis
        (refineH hypothesis declaredH)
        point
        (refineT point declaredT)

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data TerminalBenefitImpliesHorizonRobustnessPermission : Set where

data ExpectedValueImpliesEveryHorizonPointNoWorsePermission : Set where

data ShortHorizonRobustnessImpliesLongHorizonRobustnessPermission : Set where

data HorizonRobustnessImpliesAuthorityPermission : Set where

data HorizonRobustnessImpliesEmpiricalTruthPermission : Set where

terminalBenefitDoesNotAutoPromoteToHorizonRobustness :
  TerminalBenefitImpliesHorizonRobustnessPermission → ⊥
terminalBenefitDoesNotAutoPromoteToHorizonRobustness ()

expectedValueDoesNotAutoPromoteToPointwiseHorizonSafety :
  ExpectedValueImpliesEveryHorizonPointNoWorsePermission → ⊥
expectedValueDoesNotAutoPromoteToPointwiseHorizonSafety ()

shortHorizonDoesNotAutoPromoteToLongHorizonRobustness :
  ShortHorizonRobustnessImpliesLongHorizonRobustnessPermission → ⊥
shortHorizonDoesNotAutoPromoteToLongHorizonRobustness ()

horizonRobustnessDoesNotCreateAuthority :
  HorizonRobustnessImpliesAuthorityPermission → ⊥
horizonRobustnessDoesNotCreateAuthority ()

horizonRobustnessDoesNotCreateEmpiricalTruth :
  HorizonRobustnessImpliesEmpiricalTruthPermission → ⊥
horizonRobustnessDoesNotCreateEmpiricalTruth ()

record HorizonRobustInterventionBoundary : Set where
  constructor horizon-robust-intervention-boundary
  field
    robustnessQuantifiesAcrossHypotheses : Bool
    robustnessQuantifiesAcrossHypothesesIsTrue :
      robustnessQuantifiesAcrossHypotheses ≡ true
    robustnessQuantifiesAcrossDeclaredHorizon : Bool
    robustnessQuantifiesAcrossDeclaredHorizonIsTrue :
      robustnessQuantifiesAcrossDeclaredHorizon ≡ true
    terminalOutcomeAloneCertifiesIntermediateStates : Bool
    terminalOutcomeAloneCertifiesIntermediateStatesIsFalse :
      terminalOutcomeAloneCertifiesIntermediateStates ≡ false
    robustnessEqualsAuthority : Bool
    robustnessEqualsAuthorityIsFalse : robustnessEqualsAuthority ≡ false

canonicalHorizonRobustInterventionBoundary : HorizonRobustInterventionBoundary
canonicalHorizonRobustInterventionBoundary =
  horizon-robust-intervention-boundary true refl true refl false refl false refl
