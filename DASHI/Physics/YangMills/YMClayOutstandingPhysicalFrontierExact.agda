{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.YMClayVaryingCarrierTransportParityExact as Varying
import DASHI.Physics.YangMills.YMClayF3SprintConstructionFrontierExact as F3
import DASHI.Physics.YangMills.YMClayPhysicalStressOSCommonCoreWitnessExact as F4
import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact as CommonCore
import DASHI.Physics.YangMills.YMClayDirectSourceOSMassGapFrontierExact as Direct

------------------------------------------------------------------------
-- STRONG FINITE-GAP / RECOVERY FRONTIER.
--
-- This record remains the canonical compatibility carrier for the route
-- finite transfer gap -> physical recovery -> continuum gap -> YM/OS weld.
-- It is NOT the unique terminal mass-gap route: the direct source/OS route in
-- YMClayDirectSourceOSMassGapFrontierExact bypasses dense-L2 normalization,
-- Delta*a_k finite-gap calibration and P_a/E_a Mosco recovery.
--
-- F1: source localization + Wilson/R295 same-object/L2 weld + beta/a
--     trajectory calibration. Full R339 magnitude equality is not primitive.
--
-- F3: finish the existing Sprint111-122 physical sampling/interpolation,
--     quotient/gauge, norm/residual, energy-recovery and measure-convergence
--     construction program; abstract Mosco recovery is already compiler-owned.
--
-- F4: construct physical stress/OS common-core data and closure
--     identifications. Evolution equality is derived downstream from
--     same-generator + Stone/OS uniqueness rather than assumed as a primitive.
------------------------------------------------------------------------

record LiteralWilsonUniformGapTrajectory : Set₁ where
  field
    Cutoff : Set
    Volume : Set
    Coupling : Set
    Scalar : Set

    FiniteState : Volume → Cutoff → Set
    VacuumOrthogonal :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Set

    normSq :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Scalar
    transferCrossMagnitude :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Scalar
    energy :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Scalar

    betaTrajectory : Cutoff → Coupling
    latticeSpacing : Cutoff → Scalar

    LessEqual : Scalar → Scalar → Set
    multiply : Scalar → Scalar → Scalar
    subtract : Scalar → Scalar → Scalar
    one : Scalar

    decorrelationConstant : Cutoff → Scalar

    gap : Scalar
    Positive : Scalar → Set
    gapPositive : Positive gap

    literalWilsonDecorrelatorBound :
      (volume : Volume) → (cutoff : Cutoff) →
      (state : FiniteState volume cutoff) →
      VacuumOrthogonal volume cutoff state →
      LessEqual
        (transferCrossMagnitude volume cutoff state)
        (multiply (decorrelationConstant cutoff)
          (normSq volume cutoff state))

    trajectoryGapFitsLiteralWilsonReduction :
      (cutoff : Cutoff) →
      LessEqual
        (multiply gap (latticeSpacing cutoff))
        (subtract one (decorrelationConstant cutoff))

    literalWilsonFiniteGap :
      (volume : Volume) → (cutoff : Cutoff) →
      (state : FiniteState volume cutoff) →
      VacuumOrthogonal volume cutoff state →
      LessEqual
        (multiply gap (normSq volume cutoff state))
        (energy volume cutoff state)

open LiteralWilsonUniformGapTrajectory public

UniformRGTransferCoercivity : Set₁
UniformRGTransferCoercivity = LiteralWilsonUniformGapTrajectory

record PhysicalContinuumLimitWitness : Set₁ where
  field
    -- Explicit upstream construction package from the existing Sprint111-122
    -- map/estimate program. Receipts do not inhabit this field.
    constructionInputs : F3.PhysicalF3ConstructionInputs

    embeddingFamily : Varying.EmbeddingOnlyCarrierFamily
    recoverySystem : Recovery.VacuumOrthogonalRecoverySystem

    PhysicalWilsonCutoffFamilyIsRecoveryFamily : Set
    physicalWilsonCutoffFamilyIsRecoveryFamily :
      PhysicalWilsonCutoffFamilyIsRecoveryFamily

    ContinuumMeasureConstructed : Set
    continuumMeasureConstructed : ContinuumMeasureConstructed

    ContinuumHamiltonianVacuumConstructed : Set
    continuumHamiltonianVacuumConstructed :
      ContinuumHamiltonianVacuumConstructed

    ActualEmbeddedVacuumGraphOrMoscoLimit : Set
    actualEmbeddedVacuumGraphOrMoscoLimit :
      ActualEmbeddedVacuumGraphOrMoscoLimit

open PhysicalContinuumLimitWitness public

------------------------------------------------------------------------
-- Derived F4 output ABI.
--
-- Kept for downstream compatibility, but it is no longer a primitive field of
-- OutstandingPhysicalFrontier.
------------------------------------------------------------------------

record YMOSSameObjectWitness (Time Vector : Set) : Set₁ where
  field
    ymEvolution : Time → Vector → Vector
    osEvolution : Time → Vector → Vector

    CommonInvariantCore : Set
    commonInvariantCore : CommonInvariantCore

    YMGeneratorOnCore : Set
    ymGeneratorOnCore : YMGeneratorOnCore

    OSGeneratorOnCore : Set
    osGeneratorOnCore : OSGeneratorOnCore

    evolutionsEqual : ymEvolution ≡ osEvolution

open YMOSSameObjectWitness public

physicalStressOSBuildsYMOSSameObjectWitness :
  (witness : F4.PhysicalStressOSCommonCoreWitness) →
  YMOSSameObjectWitness
    (F4.Time witness)
    (CommonCore.Vector (F4.calculus witness))
physicalStressOSBuildsYMOSSameObjectWitness witness = record
  { YMOSSameObjectWitness.ymEvolution = F4.ymEvolution witness
  ; YMOSSameObjectWitness.osEvolution = F4.osEvolution witness
  ; YMOSSameObjectWitness.CommonInvariantCore =
      CommonCore.Core (F4.calculus witness)
  ; YMOSSameObjectWitness.commonInvariantCore =
      F4.reconstructedCoreWitness witness
  ; YMOSSameObjectWitness.YMGeneratorOnCore =
      F4.SelectedYMGeneratorOnCore witness
  ; YMOSSameObjectWitness.ymGeneratorOnCore =
      F4.selectedYMGeneratorOnCore witness
  ; YMOSSameObjectWitness.OSGeneratorOnCore =
      F4.ReconstructedOSGeneratorOnCore witness
  ; YMOSSameObjectWitness.osGeneratorOnCore =
      F4.reconstructedOSGeneratorOnCore witness
  ; YMOSSameObjectWitness.evolutionsEqual =
      F4.physicalSameEvolution witness
  }

------------------------------------------------------------------------
-- Historical decomposed CMP116 source leaves remain optional producer data.
------------------------------------------------------------------------

record CMP116PhysicalSourceResiduals : Set₁ where
  field
    CovarianceRootCertificate : Set
    covarianceRootCertificate : CovarianceRootCertificate
    RootLocalization : Set
    rootLocalization : RootLocalization
    GaussianPushforward : Set
    gaussianPushforward : GaussianPushforward
    WilsonHessianIdentification : Set
    wilsonHessianIdentification : WilsonHessianIdentification
    LocalPhysicalActivityConstruction : Set
    localPhysicalActivityConstruction : LocalPhysicalActivityConstruction
    SpectatorSupportSubset : Set
    spectatorSupportSubset : SpectatorSupportSubset
    FluctuationSupportSubset : Set
    fluctuationSupportSubset : FluctuationSupportSubset
    ActivityStronglyMeasurable : Set
    activityStronglyMeasurable : ActivityStronglyMeasurable
    RawPointwiseDecay : Set
    rawPointwiseDecay : RawPointwiseDecay
    AmplitudeNonnegativeAndAtMostOne : Set
    amplitudeNonnegativeAndAtMostOne : AmplitudeNonnegativeAndAtMostOne
    WeightNonnegative : Set
    weightNonnegative : WeightNonnegative
    ActiveSupportSubsetOmega : Set
    activeSupportSubsetOmega : ActiveSupportSubsetOmega
    ActiveSupportSubsetSkeleton : Set
    activeSupportSubsetSkeleton : ActiveSupportSubsetSkeleton
    WeightDominationByAppendixFHoleWeight : Set
    weightDominationByAppendixFHoleWeight : WeightDominationByAppendixFHoleWeight
    ProbabilityLaw : Set
    probabilityLaw : ProbabilityLaw
    HolesPairwiseDisjoint : Set
    holesPairwiseDisjoint : HolesPairwiseDisjoint
    NoEdgesBetweenHoles : Set
    noEdgesBetweenHoles : NoEdgesBetweenHoles
    HolesNonempty : Set
    holesNonempty : HolesNonempty
    AppendixFGeometricSmallness : Set
    appendixFGeometricSmallness : AppendixFGeometricSmallness
    RootedHsharpRemainderIdentity : Set
    rootedHsharpRemainderIdentity : RootedHsharpRemainderIdentity
    HalfBudget : Set
    halfBudget : HalfBudget
    ProfileBound : Set
    profileBound : ProfileBound
    PositiveDecayAndCouplingConstants : Set
    positiveDecayAndCouplingConstants : PositiveDecayAndCouplingConstants
    CouplingSmallness : Set
    couplingSmallness : CouplingSmallness
    CouplingRecursion : Set
    couplingRecursion : CouplingRecursion
    IRExponentialBound : Set
    irExponentialBound : IRExponentialBound

open CMP116PhysicalSourceResiduals public

record OutstandingPhysicalFrontier : Set₁ where
  field
    f1LiteralWilsonUniformGap : LiteralWilsonUniformGapTrajectory
    f3PhysicalContinuumLimit : PhysicalContinuumLimitWitness
    f4PhysicalStressOSCommonCore :
      F4.PhysicalStressOSCommonCoreWitness

open OutstandingPhysicalFrontier public

literalFinitePhysicalFormStillOpen : Bool
literalFinitePhysicalFormStillOpen = false

literalFinitePhysicalFormStillOpenIsFalse :
  literalFinitePhysicalFormStillOpen ≡ false
literalFinitePhysicalFormStillOpenIsFalse = refl

vacuumSectorResolventCompilerStillOpenMathematically : Bool
vacuumSectorResolventCompilerStillOpenMathematically = false

vacuumSectorResolventCompilerStillOpenMathematicallyIsFalse :
  vacuumSectorResolventCompilerStillOpenMathematically ≡ false
vacuumSectorResolventCompilerStillOpenMathematicallyIsFalse = refl

f2PrimitiveResearchPayment : Bool
f2PrimitiveResearchPayment = false

f2PrimitiveResearchPaymentIsFalse :
  f2PrimitiveResearchPayment ≡ false
f2PrimitiveResearchPaymentIsFalse = refl

varyingCarrierEmbeddingsRemainF3Data : Bool
varyingCarrierEmbeddingsRemainF3Data = true

varyingCarrierEmbeddingsRemainF3DataIsTrue :
  varyingCarrierEmbeddingsRemainF3Data ≡ true
varyingCarrierEmbeddingsRemainF3DataIsTrue = refl

f1TrajectoryUniformCRequired : Bool
f1TrajectoryUniformCRequired = false

f1TrajectoryUniformCRequiredIsFalse :
  f1TrajectoryUniformCRequired ≡ false
f1TrajectoryUniformCRequiredIsFalse = refl

f1PerStepTransferDefectForm : Bool
f1PerStepTransferDefectForm = true

f1PerStepTransferDefectFormIsTrue :
  f1PerStepTransferDefectForm ≡ true
f1PerStepTransferDefectFormIsTrue = refl

fullR339MagnitudeEqualityPrimitive : Bool
fullR339MagnitudeEqualityPrimitive = false

fullR339MagnitudeEqualityPrimitiveIsFalse :
  fullR339MagnitudeEqualityPrimitive ≡ false
fullR339MagnitudeEqualityPrimitiveIsFalse = refl

f4EvolutionEqualityPrimitive : Bool
f4EvolutionEqualityPrimitive = false

f4EvolutionEqualityPrimitiveIsFalse :
  f4EvolutionEqualityPrimitive ≡ false
f4EvolutionEqualityPrimitiveIsFalse = refl

f1Level : ProofLevel
f1Level = conditional

varyingCarrierTransportCompilerLevel : ProofLevel
varyingCarrierTransportCompilerLevel = standardImported

f3Level : ProofLevel
f3Level = F3.physicalF3ConstructionLevel

f4Level : ProofLevel
f4Level = F4.physicalStressOSCommonCoreLevel

cmp116PhysicalSourceResidualsLevel : ProofLevel
cmp116PhysicalSourceResidualsLevel = conditional

strongFiniteGapRecoveryFrontierIsOnlyTerminalRoute : Bool
strongFiniteGapRecoveryFrontierIsOnlyTerminalRoute = false

strongFiniteGapRecoveryFrontierIsOnlyTerminalRouteIsFalse :
  strongFiniteGapRecoveryFrontierIsOnlyTerminalRoute ≡ false
strongFiniteGapRecoveryFrontierIsOnlyTerminalRouteIsFalse = refl

directSourceOSRouteAvailable : Bool
directSourceOSRouteAvailable = true

directSourceOSRouteAvailableIsTrue :
  directSourceOSRouteAvailable ≡ true
directSourceOSRouteAvailableIsTrue = refl

directSourceRouteRequiresPaEaMosco : Bool
directSourceRouteRequiresPaEaMosco =
  Direct.paEaMoscoRecoveryMandatoryForDirectSourceRoute

unconditionalPhysicalFrontierClosed : Bool
unconditionalPhysicalFrontierClosed = false

unconditionalPhysicalFrontierClosedIsFalse :
  unconditionalPhysicalFrontierClosed ≡ false
unconditionalPhysicalFrontierClosedIsFalse = refl
