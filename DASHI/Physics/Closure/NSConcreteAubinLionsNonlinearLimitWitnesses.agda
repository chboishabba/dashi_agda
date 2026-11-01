module DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses where

open import Agda.Primitive using (Level; Set; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.Closure.NSGalerkinCompactnessLimit

------------------------------------------------------------------------
-- Concrete Aubin--Lions and nonlinear-limit witness decomposition.
--
-- This module refines the bundled analytic interfaces in
-- NSGalerkinCompactnessLimit into the exact G1--G19 dependency chain.  The
-- analytic predicates are supplied by a model of the three-dimensional
-- periodic Navier--Stokes setting; this file proves that the individually
-- named witnesses assemble into the repository's canonical compactness and
-- limit certificate.  No finite computation is promoted to an analytic proof.
------------------------------------------------------------------------

record ConcreteGalerkinSetting
    (ℓState ℓProp : Level) : Set (lsuc (ℓState ⊔ ℓProp)) where
  field
    analytic : GalerkinAnalyticSetting ℓState ℓProp

    VectorField TestField TensorField NegativeState Shell : Set ℓState

    viscosity : Scalar analytic
    initialField : InitialDatum analytic

    project≤ : Nat → VectorField → VectorField
    laplacian stokes : VectorField → VectorField
    convection : VectorField → VectorField → VectorField
    timeDerivative : (Time analytic → VectorField) → Time analytic → VectorField

    galerkinPath : Nat → Time analytic → VectorField
    limitPath : Time analytic → VectorField
    tangentPath : Nat → Time analytic → Tangent analytic
    limitTangent : Time analytic → Tangent analytic

    tensorProduct : VectorField → VectorField → TensorField
    shellProjection : Shell → VectorField → VectorField

    halfL2Energy : VectorField → Scalar analytic
    integratedGradientEnergy : (Time analytic → VectorField) → Scalar analytic
    hMinusOneSize : VectorField → Scalar analytic

    packetNumerator : Shell → VectorField → Scalar analytic
    differentiatedPacketNumerator :
      Shell → VectorField → Tangent analytic → Scalar analytic
    differentiatedLogEnergy :
      Shell → VectorField → Tangent analytic → Scalar analytic
    compactGammaModulus :
      Shell → VectorField → Tangent analytic → Budget analytic

    SmoothGlobalGalerkinSolution : Nat → Set ℓProp
    UniqueGalerkinSolution : Nat → Set ℓProp
    GalerkinEquation : Nat → Set ℓProp
    GalerkinInitialCondition : Nat → Set ℓProp

    ExactEnergyIdentity : Nat → Set ℓProp
    NonlinearHMinusOneEstimate : Set ℓProp
    NonlinearLFourThirdBound : Set ℓProp
    TimeDerivativeLFourThirdBound : Set ℓProp

    AubinLionsExtraction : (Nat → Nat) → Set ℓProp
    StrongL2Convergence : (Nat → Nat) → Set ℓProp
    WeakH1Convergence : (Nat → Nat) → Set ℓProp
    WeakStarLInfinityL2Convergence : (Nat → Nat) → Set ℓProp
    NegativeSobolevTimeConvergence : (Nat → Nat) → Set ℓProp

    FiniteShellUniformConvergence : (Nat → Nat) → Shell → Set ℓProp
    ShellEnergyUniformConvergence : (Nat → Nat) → Shell → Set ℓProp

    ProductL1Convergence : (Nat → Nat) → Set ℓProp
    ProductDistributionalConvergence : (Nat → Nat) → Set ℓProp
    NonlinearTestFieldConvergence : (Nat → Nat) → TestField → Set ℓProp

    InitialTraceWeakL2 : Set ℓProp
    InitialTraceNegativeStrong : Set ℓProp
    DissipationLiminfProperty : (Nat → Nat) → Set ℓProp
    LerayHopfEnergyInequality : Set ℓProp

    NumeratorConvergence : (Nat → Nat) → Shell → Set ℓProp
    DifferentiatedNumeratorConvergence : (Nat → Nat) → Shell → Set ℓProp
    PositiveDenominatorBranch : (Nat → Nat) → Shell → Set ℓProp
    DifferentiatedLogEnergyConvergence : (Nat → Nat) → Shell → Set ℓProp
    ZeroDenominatorContinuation : Shell → Set ℓProp
    ModulusBudgetLiminfProperty : (Nat → Nat) → Shell → Set ℓProp
    CutoffEstimatePasses : (Nat → Nat) → Shell → Set ℓProp

    WeakStrongUniqueness : Set ℓProp
    SelectedPathIdentified : Set ℓProp

open ConcreteGalerkinSetting public

------------------------------------------------------------------------
-- G1--G4: finite-dimensional existence and uniform estimates.
------------------------------------------------------------------------

record G1FiniteDimensionalExistence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    smoothGlobal : (N : Nat) → SmoothGlobalGalerkinSolution S N
    unique : (N : Nat) → UniqueGalerkinSolution S N
    equation : (N : Nat) → GalerkinEquation S N
    initialCondition : (N : Nat) → GalerkinInitialCondition S N

open G1FiniteDimensionalExistence public

record G2ExactGalerkinEnergy
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    exactIdentity : (N : Nat) → ExactEnergyIdentity S N
    uniformEnergyEstimate : UniformEnergyEstimate (analytic S)
    energyUniformInCutoff :
      UniformInCutoff (analytic S)
        (λ N → UniformEnergyEstimate (analytic S))

open G2ExactGalerkinEnergy public

record G3NonlinearHMinusOneEstimate
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    pointwiseEstimate : NonlinearHMinusOneEstimate S
    integratedFourThirdBound : NonlinearLFourThirdBound S

open G3NonlinearHMinusOneEstimate public

record G4UniformTimeDerivativeEstimate
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    fourThirdBound : TimeDerivativeLFourThirdBound S
    repositoryBound : UniformTimeDerivativeBound (analytic S)
    timeDerivativeUniformInCutoff :
      UniformInCutoff (analytic S)
        (λ N → UniformTimeDerivativeBound (analytic S))

open G4UniformTimeDerivativeEstimate public

------------------------------------------------------------------------
-- G5--G7: Aubin--Lions, negative-time compactness, and finite shells.
------------------------------------------------------------------------

record G5AubinLionsCompactness
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    subsequence : Nat → Nat
    strict : IsSubsequence (analytic S) subsequence
    extraction : AubinLionsExtraction S subsequence
    strongL2 : StrongL2Convergence S subsequence
    weakH1 : WeakH1Convergence S subsequence
    weakStarLInfinityL2 : WeakStarLInfinityL2Convergence S subsequence
    repositoryStrongL2 :
      StrongL2TimeSpaceConvergence (analytic S) subsequence
        (LimitState (analytic S))
    repositoryWeakGradient :
      WeakGradientL2Convergence (analytic S) subsequence
        (LimitGradient (analytic S))
    repositoryWeakTimeDerivative :
      WeakTimeDerivativeConvergence (analytic S) subsequence

open G5AubinLionsCompactness public

record G6NegativeSobolevTimeCompactness
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    continuousNegativeLimit :
      NegativeSobolevTimeConvergence S (subsequence G5)

open G6NegativeSobolevTimeCompactness public

record G7FiniteShellUniformConvergence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    shellUniform :
      (K : Shell S) → FiniteShellUniformConvergence S (subsequence G5) K
    energyUniform :
      (K : Shell S) → ShellEnergyUniformConvergence S (subsequence G5) K
    repositoryPacket :
      (K : Packet (analytic S)) →
      PacketEnergyConvergence (analytic S) (subsequence G5) K
    repositoryPacketAtTimes :
      (K : Packet (analytic S)) →
      PacketEnergyConvergenceAtNeededTimes (analytic S) (subsequence G5) K

open G7FiniteShellUniformConvergence public

------------------------------------------------------------------------
-- G8--G12: nonlinear identification and Leray--Hopf limit.
------------------------------------------------------------------------

record G8ProductConvergence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    strongL1Product : ProductL1Convergence S (subsequence G5)
    distributionalProduct : ProductDistributionalConvergence S (subsequence G5)
    repositoryStrongWeakProduct :
      StrongWeakProductIdentifiesLimit (analytic S) (subsequence G5)

open G8ProductConvergence public

record G9NonlinearTermConvergence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    againstTests :
      (φ : TestField S) → NonlinearTestFieldConvergence S (subsequence G5) φ
    convectionDistribution :
      NonlinearDistributionalConvergence (analytic S)
        (subsequence G5) (LimitNonlinearity (analytic S))
    projectedConvectionDistribution :
      ProjectedNonlinearDistributionalConvergence (analytic S)
        (subsequence G5) (LimitNonlinearity (analytic S))

open G9NonlinearTermConvergence public

record G10InitialTraceIdentification
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    weakL2 : InitialTraceWeakL2 S
    negativeStrong : InitialTraceNegativeStrong S
    repositoryInitial : InitialDataIdentified (analytic S) (initialField S)

open G10InitialTraceIdentification public

record G11DissipationLowerSemicontinuity
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    liminf : DissipationLiminfProperty S (subsequence G5)
    repositoryLiminf :
      DissipationLowerSemicontinuity (analytic S) (subsequence G5)

open G11DissipationLowerSemicontinuity public

record G12LerayHopfLimit
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    solution : SolutionClass (analytic S)
    energyInequality : LerayHopfEnergyInequality S
    repositoryLerayHopf : LerayHopfSolution (analytic S) solution
    representsLimit : RepresentsLimitState (analytic S) solution

open G12LerayHopfLimit public

------------------------------------------------------------------------
-- G13--G18: compact-Gamma functional convergence and cutoff passage.
------------------------------------------------------------------------

record G13NumeratorConvergence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    : Set (ℓState ⊔ ℓProp) where
  field
    shell : Shell S
    finiteSumLimit : NumeratorConvergence S (subsequence G5) shell
    repositoryNumerator :
      GammaNumeratorConvergence (analytic S) (subsequence G5)

open G13NumeratorConvergence public

record G14DifferentiatedNumeratorConvergence
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    (G13 : G13NumeratorConvergence S G5)
    : Set (ℓState ⊔ ℓProp) where
  field
    tangentCompactness : TangentFamilyCompactness (analytic S) (subsequence G5)
    differentiatedFiniteSum :
      DifferentiatedNumeratorConvergence S (subsequence G5) (shell G13)
    repositoryTangentResponse :
      GammaTangentResponseConvergence (analytic S) (subsequence G5)

open G14DifferentiatedNumeratorConvergence public

record G15PositiveDenominatorBranch
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    (G13 : G13NumeratorConvergence S G5)
    : Set (ℓState ⊔ ℓProp) where
  field
    eventualHalfLowerBound :
      PositiveDenominatorBranch S (subsequence G5) (shell G13)
    logDerivativeLimit :
      DifferentiatedLogEnergyConvergence S (subsequence G5) (shell G13)
    denominatorPacket : Packet (analytic S)
    repositoryPositive :
      DenominatorPositiveOnInterval (analytic S) denominatorPacket

open G15PositiveDenominatorBranch public

record G16ZeroDenominatorAlternative
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G13 : G13NumeratorConvergence S _)
    : Set (ℓState ⊔ ℓProp) where
  field
    directContinuation : ZeroDenominatorContinuation S (shell G13)
    denominatorPacket : Packet (analytic S)
    repositoryZero : PacketEnergyZeroAlternative (analytic S) denominatorPacket
    repositoryDivisionFree : DivisionFreeGammaIdentity (analytic S) denominatorPacket
    repositoryExactContinuation :
      ExactContinuationAlternative (analytic S) denominatorPacket

open G16ZeroDenominatorAlternative public

record G17ModulusBudgetLowerSemicontinuity
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    (G13 : G13NumeratorConvergence S G5)
    : Set (ℓState ⊔ ℓProp) where
  field
    liminf : ModulusBudgetLiminfProperty S (subsequence G5) (shell G13)
    repositoryLiminf :
      BudgetLowerSemicontinuityProperty (analytic S) (subsequence G5)
    repositoryConvergence :
      BudgetConvergenceProperty (analytic S) (subsequence G5)

open G17ModulusBudgetLowerSemicontinuity public

record G18PassageOfCutoffEstimate
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G5 : G5AubinLionsCompactness S)
    (G13 : G13NumeratorConvergence S G5)
    : Set (ℓState ⊔ ℓProp) where
  field
    cutoffToLimit : CutoffEstimatePasses S (subsequence G5) (shell G13)

open G18PassageOfCutoffEstimate public

------------------------------------------------------------------------
-- G19: weak--strong uniqueness and selected-path identification.
------------------------------------------------------------------------

record G19SolutionIdentification
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    (G12 : G12LerayHopfLimit S)
    : Set (ℓState ⊔ ℓProp) where
  field
    weakStrongUniqueness : WeakStrongUniqueness S
    selectedPath : SelectedPathIdentified S
    repositoryStrong : StrongSolution (analytic S) (solution G12)
    repositoryUnique : SolutionUniqueOnInterval (analytic S) (solution G12)

open G19SolutionIdentification public

------------------------------------------------------------------------
-- Complete G1--G19 certificate and adapter to the existing canonical surface.
------------------------------------------------------------------------

record ConcreteAubinLionsNonlinearLimitCertificate
    {ℓState ℓProp : Level}
    (S : ConcreteGalerkinSetting ℓState ℓProp)
    : Set (ℓState ⊔ ℓProp) where
  field
    g1 : G1FiniteDimensionalExistence S
    g2 : G2ExactGalerkinEnergy S
    g3 : G3NonlinearHMinusOneEstimate S
    g4 : G4UniformTimeDerivativeEstimate S
    g5 : G5AubinLionsCompactness S
    g6 : G6NegativeSobolevTimeCompactness S g5
    g7 : G7FiniteShellUniformConvergence S g5
    g8 : G8ProductConvergence S g5
    g9 : G9NonlinearTermConvergence S g5
    g10 : G10InitialTraceIdentification S
    g11 : G11DissipationLowerSemicontinuity S g5
    g12 : G12LerayHopfLimit S
    g13 : G13NumeratorConvergence S g5
    g14 : G14DifferentiatedNumeratorConvergence S g5 g13
    g15 : G15PositiveDenominatorBranch S g5 g13
    g16 : G16ZeroDenominatorAlternative S g13
    g17 : G17ModulusBudgetLowerSemicontinuity S g5 g13
    g18 : G18PassageOfCutoffEstimate S g5 g13
    g19 : G19SolutionIdentification S g12

open ConcreteAubinLionsNonlinearLimitCertificate public

toCanonicalGalerkinCertificate :
  {ℓState ℓProp : Level} →
  {S : ConcreteGalerkinSetting ℓState ℓProp} →
  ConcreteAubinLionsNonlinearLimitCertificate S →
  GalerkinCompactnessAndLimitCertificate (analytic S)
toCanonicalGalerkinCertificate {S = S} X =
  assembleGalerkinCompactnessAndLimit (analytic S) U C N G B
  where
    U : GalerkinUniformBounds (analytic S)
    U = record
      { energyEstimate = uniformEnergyEstimate (g2 X)
      ; timeDerivativeBound = repositoryBound (g4 X)
      ; energyUniformInCutoff = energyUniformInCutoff (g2 X)
      ; timeDerivativeUniformInCutoff = timeDerivativeUniformInCutoff (g4 X)
      }

    C : GalerkinSubsequenceCompactness (analytic S) U
    C = record
      { subsequence = subsequence (g5 X)
      ; subsequenceStrict = strict (g5 X)
      ; aubinLionsStrongL2 = repositoryStrongL2 (g5 X)
      ; weakGradientConvergence = repositoryWeakGradient (g5 X)
      ; weakTimeDerivativeConvergence = repositoryWeakTimeDerivative (g5 X)
      ; finitePacketConvergence = repositoryPacket (g7 X)
      ; finitePacketConvergenceAtNeededTimes = repositoryPacketAtTimes (g7 X)
      }

    N : NavierStokesNonlinearLimit (analytic S) U C
    N = record
      { strongWeakProductPassage = repositoryStrongWeakProduct (g8 X)
      ; convectionLimit = convectionDistribution (g9 X)
      ; projectedConvectionLimit = projectedConvectionDistribution (g9 X)
      ; initialDatum = initialField S
      ; solution = solution (g12 X)
      ; initialDataIdentification = repositoryInitial (g10 X)
      ; lerayHopfIdentification = repositoryLerayHopf (g12 X)
      ; representsLimit = representsLimit (g12 X)
      ; strongSolutionWhenRequired = repositoryStrong (g19 X)
      ; uniquenessWhenSinglePathRequired = repositoryUnique (g19 X)
      }

    G : CompactGammaFunctionalLimit (analytic S) U C N
    G = record
      { tangentCompactness = tangentCompactness (g14 X)
      ; numeratorLimit = repositoryNumerator (g13 X)
      ; tangentResponseLimit = repositoryTangentResponse (g14 X)
      ; denominatorPacket = denominatorPacket (g15 X)
      ; denominatorPositiveBranch = repositoryPositive (g15 X)
      ; zeroEnergyBranch = repositoryZero (g16 X)
      ; divisionFreeIdentity = repositoryDivisionFree (g16 X)
      ; exactContinuationAlternative = repositoryExactContinuation (g16 X)
      }

    B : BudgetLowerSemicontinuity (analytic S) U C N G
    B = record
      { dissipationLiminf = repositoryLiminf (g11 X)
      ; modulusBudgetLiminf = repositoryLiminf (g17 X)
      ; modulusBudgetConvergence = repositoryConvergence (g17 X)
      }
