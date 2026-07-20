module DASHI.Physics.Closure.NSCompactGammaGalerkinLimitBridge where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Set₁)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption

------------------------------------------------------------------------
-- Actual finite-Galerkin to continuum witness surface.
--
-- The old bridge accepted two opaque scalar convergence witnesses.  That made
-- it possible to inhabit the continuum step without recording the energy and
-- time-derivative bounds, Aubin--Lions compactness, nonlinear identification,
-- packet convergence, differentiated compact-Gamma convergence, lower
-- semicontinuity, denominator handling, or solution identification.
--
-- The records below keep those obligations separate and named.  They remain
-- analytic interfaces: this module composes supplied proofs, but finite
-- numerical receipts cannot inhabit any of them by themselves.
------------------------------------------------------------------------

record SequentialOrderClosure
    (A : AbsorptionArithmetic) : Set₁ where
  field
    Converges :
      (Nat → Scalar A) → Scalar A → Set

    orderClosed :
      {left right : Nat → Scalar A} →
      {leftLimit rightLimit : Scalar A} →
      Converges left leftLimit →
      Converges right rightLimit →
      ((cutoff : Nat) → _≤_ A (left cutoff) (right cutoff)) →
      _≤_ A leftLimit rightLimit

open SequentialOrderClosure public

record GalerkinAnalyticSetting
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A) : Set₁ where
  field
    Time State GradientState NonlinearTerm Distribution Tangent : Set
    InitialDatum : Set

    galerkinSolution : Nat → Time → State
    continuumSolution : Time → State
    gradient : State → GradientState
    nonlinearTerm : State → NonlinearTerm
    projectedNonlinearTerm : Nat → NonlinearTerm → NonlinearTerm

    initialDatum : InitialDatum
    initialTrace : (Time → State) → InitialDatum

    energyAt : State → Scalar A
    integratedDissipation : Nat → Scalar A
    initialEnergy : Scalar A
    viscosity : Scalar A
    timeDerivativeSize : Nat → Scalar A

    packetEnergy : State → Scalar A
    compactGammaNumerator : State → Scalar A
    compactGammaTangentNumerator : State → Tangent → Scalar A
    absoluteLogDerivative : State → Tangent → Scalar A
    modulusBudget : State → Tangent → Scalar A

    UniformlyBounded : (Nat → Scalar A) → Set
    StrongL2Converges : (Nat → Nat) → Set
    WeakGradientConverges : (Nat → Nat) → Set
    DistributionallyConverges :
      (Nat → NonlinearTerm) → NonlinearTerm → Set
    PacketConvergesAtNeededTimes : (Nat → Nat) → Set
    ScalarConverges : (Nat → Scalar A) → Scalar A → Set
    LiminfBound : (Nat → Scalar A) → Scalar A → Set

    IsLerayHopfSolution : (Time → State) → Set
    IsStrongSolution : (Time → State) → Set
    SameSolutionPath : (Time → State) → (Time → State) → Set

    DivisionFreeContinuation : Time → Set

open GalerkinAnalyticSetting public

------------------------------------------------------------------------
-- 1. Uniform finite-dimensional estimates.
------------------------------------------------------------------------

record GalerkinUniformBounds
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A)
    (S : GalerkinAnalyticSetting A C) : Set₁ where
  field
    energyDissipationEstimate :
      (cutoff : Nat) →
      _≤_ A
        (integratedDissipation S cutoff)
        (initialEnergy S)

    uniformEnergyControl :
      UniformlyBounded S
        (λ cutoff → integratedDissipation S cutoff)

    uniformTimeDerivativeControl :
      UniformlyBounded S
        (timeDerivativeSize S)

open GalerkinUniformBounds public

------------------------------------------------------------------------
-- 2. Aubin--Lions subsequence compactness and weak derivative convergence.
------------------------------------------------------------------------

record GalerkinSubsequenceCompactness
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A)
    (S : GalerkinAnalyticSetting A C)
    (B : GalerkinUniformBounds A C S) : Set₁ where
  field
    subsequence : Nat → Nat

    subsequenceStrictlyIncreasing :
      (index : Nat) → Set

    aubinLionsStrongL2 :
      StrongL2Converges S subsequence

    weakDerivativeConvergence :
      WeakGradientConverges S subsequence

open GalerkinSubsequenceCompactness public

------------------------------------------------------------------------
-- 3. PDE convergence, nonlinear strong--weak identification, and path identity.
------------------------------------------------------------------------

record NavierStokesNonlinearLimit
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A)
    (S : GalerkinAnalyticSetting A C)
    (B : GalerkinUniformBounds A C S)
    (K : GalerkinSubsequenceCompactness A C S B) : Set₁ where
  field
    nonlinearLimitIdentification :
      DistributionallyConverges S
        (λ index →
          projectedNonlinearTerm S
            (subsequence K index)
            (nonlinearTerm S
              (galerkinSolution S (subsequence K index))))
        (nonlinearTerm S (continuumSolution S))

    initialDataIdentification :
      initialTrace S (continuumSolution S) ≡ initialDatum S

    lerayHopfIdentification :
      IsLerayHopfSolution S (continuumSolution S)

    strongSolutionIdentification :
      IsStrongSolution S (continuumSolution S)

    uniquenessOnRequiredInterval :
      (candidate : Time S → State S) →
      IsStrongSolution S candidate →
      initialTrace S candidate ≡ initialDatum S →
      SameSolutionPath S candidate (continuumSolution S)

open NavierStokesNonlinearLimit public

------------------------------------------------------------------------
-- Denominator handling for D log E.
------------------------------------------------------------------------

data DenominatorAlternative
    (A : AbsorptionArithmetic)
    (Continuation : Set)
    (energy : Scalar A) : Set where
  positiveDenominator : Positive A energy →
                        DenominatorAlternative A Continuation energy
  divisionFreeBranch : Continuation →
                       DenominatorAlternative A Continuation energy

------------------------------------------------------------------------
-- 4. Packet, numerator, tangent-response, and differentiated Gamma limits.
------------------------------------------------------------------------

record CompactGammaFunctionalLimit
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A)
    (S : GalerkinAnalyticSetting A C)
    (B : GalerkinUniformBounds A C S)
    (K : GalerkinSubsequenceCompactness A C S B)
    (N : NavierStokesNonlinearLimit A C S B K) : Set₁ where
  field
    packetEnergyConvergence :
      PacketConvergesAtNeededTimes S (subsequence K)

    tangent : Tangent S
    evaluationTime : Time S

    numeratorConvergence :
      ScalarConverges S
        (λ index →
          compactGammaNumerator S
            (galerkinSolution S
              (subsequence K index)
              evaluationTime))
        (compactGammaNumerator S
          (continuumSolution S evaluationTime))

    tangentNumeratorConvergence :
      ScalarConverges S
        (λ index →
          compactGammaTangentNumerator S
            (galerkinSolution S
              (subsequence K index)
              evaluationTime)
            tangent)
        (compactGammaTangentNumerator S
          (continuumSolution S evaluationTime)
          tangent)

    differentiatedFunctionalConvergence :
      Converges C
        (λ index →
          absoluteLogDerivative S
            (galerkinSolution S
              (subsequence K index)
              evaluationTime)
            tangent)
        (absoluteLogDerivative S
          (continuumSolution S evaluationTime)
          tangent)

    denominatorAlternative :
      (time : Time S) →
      DenominatorAlternative A
        (DivisionFreeContinuation S time)
        (packetEnergy S (continuumSolution S time))

open CompactGammaFunctionalLimit public

------------------------------------------------------------------------
-- 5. Lower semicontinuity of dissipation and the modulus budget.
------------------------------------------------------------------------

record BudgetLowerSemicontinuity
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A)
    (S : GalerkinAnalyticSetting A C)
    (B : GalerkinUniformBounds A C S)
    (K : GalerkinSubsequenceCompactness A C S B)
    (N : NavierStokesNonlinearLimit A C S B K)
    (G : CompactGammaFunctionalLimit A C S B K N) : Set₁ where
  field
    gradientNormLowerSemicontinuity :
      LiminfBound S
        (λ index →
          integratedDissipation S (subsequence K index))
        (integratedDissipation S 0)

    modulusBudgetConvergence :
      Converges C
        (λ index →
          modulusBudget S
            (galerkinSolution S
              (subsequence K index)
              (evaluationTime G))
            (tangent G))
        (modulusBudget S
          (continuumSolution S (evaluationTime G))
          (tangent G))

    modulusBudgetLowerSemicontinuity :
      LiminfBound S
        (λ index →
          modulusBudget S
            (galerkinSolution S
              (subsequence K index)
              (evaluationTime G))
            (tangent G))
        (modulusBudget S
          (continuumSolution S (evaluationTime G))
          (tangent G))

open BudgetLowerSemicontinuity public

------------------------------------------------------------------------
-- Fully witnessed compact-Gamma Galerkin family.
------------------------------------------------------------------------

record ActualGalerkinCompactGammaFamily
    (A : AbsorptionArithmetic)
    (C : SequentialOrderClosure A) : Set₁ where
  field
    setting : GalerkinAnalyticSetting A C
    uniformBounds : GalerkinUniformBounds A C setting
    compactness :
      GalerkinSubsequenceCompactness A C setting uniformBounds
    nonlinearLimit :
      NavierStokesNonlinearLimit A C setting uniformBounds compactness
    compactGammaLimit :
      CompactGammaFunctionalLimit A C setting uniformBounds compactness
        nonlinearLimit
    budgetLSC :
      BudgetLowerSemicontinuity A C setting uniformBounds compactness
        nonlinearLimit compactGammaLimit

    uniformCutoffLogModulus :
      (index : Nat) →
      _≤_ A
        (absoluteLogDerivative setting
          (galerkinSolution setting
            (subsequence compactness index)
            (evaluationTime compactGammaLimit))
          (tangent compactGammaLimit))
        (modulusBudget setting
          (galerkinSolution setting
            (subsequence compactness index)
            (evaluationTime compactGammaLimit))
          (tangent compactGammaLimit))

open ActualGalerkinCompactGammaFamily public

------------------------------------------------------------------------
-- The final order passage is now available only after all five analytic
-- witness bundles have been supplied.
------------------------------------------------------------------------

actualGalerkinLogModulusPassesToContinuum :
  (A : AbsorptionArithmetic) →
  (C : SequentialOrderClosure A) →
  (F : ActualGalerkinCompactGammaFamily A C) →
  _≤_ A
    (absoluteLogDerivative (setting F)
      (continuumSolution (setting F)
        (evaluationTime (compactGammaLimit F)))
      (tangent (compactGammaLimit F)))
    (modulusBudget (setting F)
      (continuumSolution (setting F)
        (evaluationTime (compactGammaLimit F)))
      (tangent (compactGammaLimit F)))
actualGalerkinLogModulusPassesToContinuum A C F =
  orderClosed C
    (differentiatedFunctionalConvergence (compactGammaLimit F))
    (modulusBudgetConvergence (budgetLSC F))
    (uniformCutoffLogModulus F)
