module DASHI.Physics.Closure.NSGalerkinCompactnessLimit where

open import Agda.Primitive using (Level; Set; Set₁; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- Actual Galerkin compactness and nonlinear-limit identification.
--
-- This module is deliberately proof-obligation oriented.  It does not hide
-- the analytic passage N -> infinity inside one generic convergence field.
-- A consumer must separately provide:
--
--   * uniform energy and time-derivative estimates;
--   * a subsequence and Aubin--Lions compactness;
--   * weak derivative and nonlinear distributional convergence;
--   * finite Fourier-packet convergence;
--   * compact-Gamma numerator and tangent-response convergence;
--   * lower semicontinuity of dissipation and modulus budgets;
--   * a division-free denominator alternative;
--   * initial-data and solution-class identification, including uniqueness
--     whenever a theorem needs a single path rather than a subsequence.
--
-- The records below are interfaces for the genuine analytic theorems.  The
-- only theorem proved here is that the five named witnesses assemble into a
-- complete Galerkin limit certificate.  There is no constructor that accepts
-- an undifferentiated statement such as "the Galerkin family converges".
------------------------------------------------------------------------

record GalerkinAnalyticSetting
    (ℓState ℓProp : Level) : Set (lsuc (ℓState ⊔ ℓProp)) where
  field
    Scalar : Set ℓState
    Time : Set ℓState
    State : Set ℓState
    Gradient : Set ℓState
    Distribution : Set ℓState
    Tangent : Set ℓState
    Packet : Set ℓState
    Budget : Set ℓState
    InitialDatum : Set ℓState
    SolutionClass : Set ℓState

    GalerkinState : Nat → Time → State
    GalerkinGradient : Nat → Time → Gradient
    GalerkinTimeDerivative : Nat → Time → Distribution
    GalerkinNonlinearity : Nat → Distribution
    GalerkinProjectionNonlinearity : Nat → Distribution

    LimitState : Time → State
    LimitGradient : Time → Gradient
    LimitNonlinearity : Distribution

    PacketEnergy : Packet → State → Scalar
    GammaNumerator : State → Scalar
    GammaNumeratorTangent : State → Tangent → Scalar
    GammaDenominator : Packet → State → Scalar
    ModulusBudget : Nat → Budget
    LimitModulusBudget : Budget

    _≤_ : Scalar → Scalar → Set ℓProp
    _<_ : Scalar → Scalar → Set ℓProp
    _≡S_ : Scalar → Scalar → Set ℓProp
    zero : Scalar

    AtInitialTime : Time → Set ℓProp
    IsSubsequence : (Nat → Nat) → Set ℓProp

    UniformInCutoff : (Nat → Set ℓProp) → Set ℓProp
    UniformEnergyEstimate : Set ℓProp
    UniformTimeDerivativeBound : Set ℓProp

    StrongL2TimeSpaceConvergence :
      (Nat → Nat) → (Time → State) → Set ℓProp
    WeakGradientL2Convergence :
      (Nat → Nat) → (Time → Gradient) → Set ℓProp
    WeakTimeDerivativeConvergence :
      (Nat → Nat) → Set ℓProp

    NonlinearDistributionalConvergence :
      (Nat → Nat) → Distribution → Set ℓProp
    ProjectedNonlinearDistributionalConvergence :
      (Nat → Nat) → Distribution → Set ℓProp
    StrongWeakProductIdentifiesLimit :
      (Nat → Nat) → Set ℓProp

    PacketEnergyConvergence :
      (Nat → Nat) → Packet → Set ℓProp
    PacketEnergyConvergenceAtNeededTimes :
      (Nat → Nat) → Packet → Set ℓProp

    GammaNumeratorConvergence :
      (Nat → Nat) → Set ℓProp
    GammaTangentResponseConvergence :
      (Nat → Nat) → Set ℓProp
    TangentFamilyCompactness :
      (Nat → Nat) → Set ℓProp

    DissipationLowerSemicontinuity :
      (Nat → Nat) → Set ℓProp
    BudgetLowerSemicontinuityProperty :
      (Nat → Nat) → Set ℓProp
    BudgetConvergenceProperty :
      (Nat → Nat) → Set ℓProp

    DenominatorPositiveOnInterval : Packet → Set ℓProp
    PacketEnergyZeroAlternative : Packet → Set ℓProp
    DivisionFreeGammaIdentity : Packet → Set ℓProp
    ExactContinuationAlternative : Packet → Set ℓProp

    InitialDataIdentified : InitialDatum → Set ℓProp
    LerayHopfSolution : SolutionClass → Set ℓProp
    StrongSolution : SolutionClass → Set ℓProp
    RepresentsLimitState : SolutionClass → Set ℓProp
    SolutionUniqueOnInterval : SolutionClass → Set ℓProp

open GalerkinAnalyticSetting public

------------------------------------------------------------------------
-- 1. Uniform estimates.
------------------------------------------------------------------------

record GalerkinUniformBounds
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    energyEstimate : UniformEnergyEstimate A
    timeDerivativeBound : UniformTimeDerivativeBound A

    energyUniformInCutoff :
      UniformInCutoff A (λ N → UniformEnergyEstimate A)

    timeDerivativeUniformInCutoff :
      UniformInCutoff A (λ N → UniformTimeDerivativeBound A)

open GalerkinUniformBounds public

------------------------------------------------------------------------
-- 2. Aubin--Lions subsequence compactness and Fourier packets.
------------------------------------------------------------------------

record GalerkinSubsequenceCompactness
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    (U : GalerkinUniformBounds A)
    : Set (ℓState ⊔ ℓProp) where
  field
    subsequence : Nat → Nat
    subsequenceStrict : IsSubsequence A subsequence

    aubinLionsStrongL2 :
      StrongL2TimeSpaceConvergence A subsequence (LimitState A)

    weakGradientConvergence :
      WeakGradientL2Convergence A subsequence (LimitGradient A)

    weakTimeDerivativeConvergence :
      WeakTimeDerivativeConvergence A subsequence

    finitePacketConvergence :
      (packet : Packet A) →
      PacketEnergyConvergence A subsequence packet

    finitePacketConvergenceAtNeededTimes :
      (packet : Packet A) →
      PacketEnergyConvergenceAtNeededTimes A subsequence packet

open GalerkinSubsequenceCompactness public

------------------------------------------------------------------------
-- 3. PDE and nonlinear-limit identification.
------------------------------------------------------------------------

record NavierStokesNonlinearLimit
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    (U : GalerkinUniformBounds A)
    (C : GalerkinSubsequenceCompactness A U)
    : Set (ℓState ⊔ ℓProp) where
  field
    strongWeakProductPassage :
      StrongWeakProductIdentifiesLimit A (subsequence C)

    convectionLimit :
      NonlinearDistributionalConvergence A
        (subsequence C)
        (LimitNonlinearity A)

    projectedConvectionLimit :
      ProjectedNonlinearDistributionalConvergence A
        (subsequence C)
        (LimitNonlinearity A)

    initialDatum : InitialDatum A
    solution : SolutionClass A

    initialDataIdentification :
      InitialDataIdentified A initialDatum

    lerayHopfIdentification :
      LerayHopfSolution A solution

    representsLimit :
      RepresentsLimitState A solution

    strongSolutionWhenRequired :
      StrongSolution A solution

    uniquenessWhenSinglePathRequired :
      SolutionUniqueOnInterval A solution

open NavierStokesNonlinearLimit public

------------------------------------------------------------------------
-- 4. Differentiated compact-Gamma functional limit.
------------------------------------------------------------------------

record CompactGammaFunctionalLimit
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    (U : GalerkinUniformBounds A)
    (C : GalerkinSubsequenceCompactness A U)
    (N : NavierStokesNonlinearLimit A U C)
    : Set (ℓState ⊔ ℓProp) where
  field
    tangentCompactness :
      TangentFamilyCompactness A (subsequence C)

    numeratorLimit :
      GammaNumeratorConvergence A (subsequence C)

    tangentResponseLimit :
      GammaTangentResponseConvergence A (subsequence C)

    denominatorPacket : Packet A

    denominatorPositiveBranch :
      DenominatorPositiveOnInterval A denominatorPacket

    zeroEnergyBranch :
      PacketEnergyZeroAlternative A denominatorPacket

    divisionFreeIdentity :
      DivisionFreeGammaIdentity A denominatorPacket

    exactContinuationAlternative :
      ExactContinuationAlternative A denominatorPacket

open CompactGammaFunctionalLimit public

------------------------------------------------------------------------
-- 5. Lower semicontinuity and modulus-budget passage.
------------------------------------------------------------------------

record BudgetLowerSemicontinuity
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    (U : GalerkinUniformBounds A)
    (C : GalerkinSubsequenceCompactness A U)
    (N : NavierStokesNonlinearLimit A U C)
    (G : CompactGammaFunctionalLimit A U C N)
    : Set (ℓState ⊔ ℓProp) where
  field
    dissipationLiminf :
      DissipationLowerSemicontinuity A (subsequence C)

    modulusBudgetLiminf :
      BudgetLowerSemicontinuityProperty A (subsequence C)

    modulusBudgetConvergence :
      BudgetConvergenceProperty A (subsequence C)

open BudgetLowerSemicontinuity public

------------------------------------------------------------------------
-- Complete certificate.  Every analytic layer is named and inspectable.
------------------------------------------------------------------------

record GalerkinCompactnessAndLimitCertificate
    {ℓState ℓProp : Level}
    (A : GalerkinAnalyticSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    uniformBounds : GalerkinUniformBounds A

    subsequenceCompactness :
      GalerkinSubsequenceCompactness A uniformBounds

    nonlinearLimit :
      NavierStokesNonlinearLimit A
        uniformBounds
        subsequenceCompactness

    compactGammaLimit :
      CompactGammaFunctionalLimit A
        uniformBounds
        subsequenceCompactness
        nonlinearLimit

    budgetLowerSemicontinuity :
      BudgetLowerSemicontinuity A
        uniformBounds
        subsequenceCompactness
        nonlinearLimit
        compactGammaLimit

open GalerkinCompactnessAndLimitCertificate public

assembleGalerkinCompactnessAndLimit :
  {ℓState ℓProp : Level} →
  (A : GalerkinAnalyticSetting ℓState ℓProp) →
  (U : GalerkinUniformBounds A) →
  (C : GalerkinSubsequenceCompactness A U) →
  (N : NavierStokesNonlinearLimit A U C) →
  (G : CompactGammaFunctionalLimit A U C N) →
  (B : BudgetLowerSemicontinuity A U C N G) →
  GalerkinCompactnessAndLimitCertificate A
assembleGalerkinCompactnessAndLimit A U C N G B = record
  { uniformBounds = U
  ; subsequenceCompactness = C
  ; nonlinearLimit = N
  ; compactGammaLimit = G
  ; budgetLowerSemicontinuity = B
  }

------------------------------------------------------------------------
-- Explicit projections used by downstream continuation arguments.
------------------------------------------------------------------------

certificateStrongL2 :
  {ℓState ℓProp : Level} →
  {A : GalerkinAnalyticSetting ℓState ℓProp} →
  (X : GalerkinCompactnessAndLimitCertificate A) →
  StrongL2TimeSpaceConvergence A
    (subsequence (subsequenceCompactness X))
    (LimitState A)
certificateStrongL2 X =
  aubinLionsStrongL2 (subsequenceCompactness X)

certificateNonlinearLimit :
  {ℓState ℓProp : Level} →
  {A : GalerkinAnalyticSetting ℓState ℓProp} →
  (X : GalerkinCompactnessAndLimitCertificate A) →
  NonlinearDistributionalConvergence A
    (subsequence (subsequenceCompactness X))
    (LimitNonlinearity A)
certificateNonlinearLimit X =
  convectionLimit (nonlinearLimit X)

certificateGammaTangentLimit :
  {ℓState ℓProp : Level} →
  {A : GalerkinAnalyticSetting ℓState ℓProp} →
  (X : GalerkinCompactnessAndLimitCertificate A) →
  GammaTangentResponseConvergence A
    (subsequence (subsequenceCompactness X))
certificateGammaTangentLimit X =
  tangentResponseLimit (compactGammaLimit X)

certificateDissipationLiminf :
  {ℓState ℓProp : Level} →
  {A : GalerkinAnalyticSetting ℓState ℓProp} →
  (X : GalerkinCompactnessAndLimitCertificate A) →
  DissipationLowerSemicontinuity A
    (subsequence (subsequenceCompactness X))
certificateDissipationLiminf X =
  dissipationLiminf (budgetLowerSemicontinuity X)

certificateContinuationAlternative :
  {ℓState ℓProp : Level} →
  {A : GalerkinAnalyticSetting ℓState ℓProp} →
  (X : GalerkinCompactnessAndLimitCertificate A) →
  ExactContinuationAlternative A
    (denominatorPacket (compactGammaLimit X))
certificateContinuationAlternative X =
  exactContinuationAlternative (compactGammaLimit X)
