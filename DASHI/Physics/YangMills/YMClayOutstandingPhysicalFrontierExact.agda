{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery
import DASHI.Physics.YangMills.YMClayVaryingCarrierTransportParityExact as Varying

------------------------------------------------------------------------
-- Exact residual frontier after the 2026-09-17 Aristotle varying-carrier
-- tranche.
--
-- Paid generically / by verified Lean donor:
--   * literal finite q_a/H_a construction;
--   * vacuum-sector spectral consequences;
--   * varying-Hilbert transport through isometric embeddings (old F2).
--
-- Surviving physical inputs:
--   F1 literal Wilson uniform gap on the actual continuum trajectory;
--   F3 embedded literal-Wilson graph/Mosco limit and continuum H/Omega;
--   F4 same physical YM and OS evolution / generator weld.
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
    inverseLatticeSpacing : Cutoff → Scalar

    LessEqual : Scalar → Scalar → Set
    StrictLess : Scalar → Scalar → Set
    multiply : Scalar → Scalar → Scalar
    subtract : Scalar → Scalar → Scalar
    one : Scalar

    decorrelationConstant : Scalar
    decorrelationStrictlyBelowOne : StrictLess decorrelationConstant one

    gap : Scalar
    Positive : Scalar → Set
    gapPositive : Positive gap

    -- Exact finite leaf isolated by Aristotle UniformGapReduction:
    --   |<P0 psi,P1 psi>| <= c ||psi||^2.
    literalWilsonDecorrelatorBound :
      (volume : Volume) → (cutoff : Cutoff) →
      (state : FiniteState volume cutoff) →
      VacuumOrthogonal volume cutoff state →
      LessEqual
        (transferCrossMagnitude volume cutoff state)
        (multiply decorrelationConstant (normSq volume cutoff state))

    -- The chosen positive Delta is below a_k^-1 (1-c) for every cutoff.
    trajectoryGapFitsLiteralWilsonReduction :
      (cutoff : Cutoff) →
      LessEqual gap
        (multiply
          (inverseLatticeSpacing cutoff)
          (subtract one decorrelationConstant))

    -- Same-object finite physical consequence, retained explicitly rather than
    -- inferred from status metadata.
    literalWilsonFiniteGap :
      (volume : Volume) → (cutoff : Cutoff) →
      (state : FiniteState volume cutoff) →
      VacuumOrthogonal volume cutoff state →
      LessEqual
        (multiply gap (normSq volume cutoff state))
        (energy volume cutoff state)

open LiteralWilsonUniformGapTrajectory public

-- Backward-compatible name for old consumers.  Its content is now the actual
-- literal Wilson trajectory estimate rather than a generic RG form record.
UniformRGTransferCoercivity : Set₁
UniformRGTransferCoercivity = LiteralWilsonUniformGapTrajectory

record PhysicalContinuumLimitWitness : Set₁ where
  field
    -- Old F2 is compiler-owned.  The embeddings remain real data because F3's
    -- embedded graph limit needs them, but no independent Hamiltonian/vacuum
    -- compatibility fields are charged here.
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
    actualEmbeddedVacuumGraphOrMoscoLimit : ActualEmbeddedVacuumGraphOrMoscoLimit

open PhysicalContinuumLimitWitness public

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

-- Historical decomposed CMP116 source leaves remain available as optional F1
-- producers.  They are not mandatory terminal architecture after merged #987 /
-- R387, so this record is deliberately not a field of OutstandingPhysicalFrontier.
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

    Time : Set
    Vector : Set
    f4YMOSSameObject : YMOSSameObjectWitness Time Vector

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

-- F2 was a structural mismatch, not a remaining physical theorem.  Aristotle's
-- varying-carrier theorem pays it with isometric embeddings; the embedding
-- family itself is retained under F3 where the actual graph limit consumes it.
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

f1Level : ProofLevel
f1Level = conditional

varyingCarrierTransportCompilerLevel : ProofLevel
varyingCarrierTransportCompilerLevel = standardImported

f3Level : ProofLevel
f3Level = conditional

f4Level : ProofLevel
f4Level = conditional

cmp116PhysicalSourceResidualsLevel : ProofLevel
cmp116PhysicalSourceResidualsLevel = conditional

unconditionalPhysicalFrontierClosed : Bool
unconditionalPhysicalFrontierClosed = false

unconditionalPhysicalFrontierClosedIsFalse :
  unconditionalPhysicalFrontierClosed ≡ false
unconditionalPhysicalFrontierClosedIsFalse = refl
