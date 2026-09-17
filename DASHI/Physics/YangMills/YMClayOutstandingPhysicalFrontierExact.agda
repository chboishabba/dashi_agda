{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanVacuumOrthogonalMoscoRecoveryExact as Recovery

------------------------------------------------------------------------
-- Exact residual frontier after the 2026-09-17 Aristotle donor comparison.
--
-- The literal finite q_a/H_a construction and generic vacuum-sector resolvent
-- machinery are no longer physical gaps.  The surviving problem is the actual
-- RG/continuum/same-object mathematics below.
------------------------------------------------------------------------

record UniformRGTransferCoercivity : Set₁ where
  field
    Cutoff : Set
    Volume : Set
    Coupling : Set
    Mass : Set

    FiniteState : Volume → Cutoff → Set
    VacuumOrthogonal :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Set

    normSq :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Mass
    energy :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteState volume cutoff → Mass

    betaTrajectory : Cutoff → Coupling

    LessEqual : Mass → Mass → Set
    multiply : Mass → Mass → Mass

    gap : Mass
    Positive : Mass → Set
    gapPositive : Positive gap

    -- This is F1.  The same positive physical mass must survive every cutoff
    -- and volume on the actual beta(a) RG trajectory.
    uniformCoercivityAlongRGTrajectory :
      (volume : Volume) → (cutoff : Cutoff) →
      (state : FiniteState volume cutoff) →
      VacuumOrthogonal volume cutoff state →
      LessEqual
        (multiply gap (normSq volume cutoff state))
        (energy volume cutoff state)

open UniformRGTransferCoercivity public

record VaryingHilbertCommonCarrier : Set₁ where
  field
    Cutoff : Set
    Volume : Set
    CommonCarrier : Set
    FiniteCarrier : Volume → Cutoff → Set

    embed :
      (volume : Volume) → (cutoff : Cutoff) →
      FiniteCarrier volume cutoff → CommonCarrier

    IsometricEmbedding :
      (volume : Volume) → (cutoff : Cutoff) → Set
    isometricEmbedding :
      (volume : Volume) → (cutoff : Cutoff) →
      IsometricEmbedding volume cutoff

    HamiltonianCompatibility :
      (volume : Volume) → (cutoff : Cutoff) → Set
    hamiltonianCompatibility :
      (volume : Volume) → (cutoff : Cutoff) →
      HamiltonianCompatibility volume cutoff

    VacuumCompatibility :
      (volume : Volume) → (cutoff : Cutoff) → Set
    vacuumCompatibility :
      (volume : Volume) → (cutoff : Cutoff) →
      VacuumCompatibility volume cutoff

open VaryingHilbertCommonCarrier public

record PhysicalContinuumLimitWitness : Set₁ where
  field
    recoverySystem : Recovery.VacuumOrthogonalRecoverySystem

    PhysicalWilsonCutoffFamilyIsRecoveryFamily : Set
    physicalWilsonCutoffFamilyIsRecoveryFamily :
      PhysicalWilsonCutoffFamilyIsRecoveryFamily

    ContinuumMeasureConstructed : Set
    continuumMeasureConstructed : ContinuumMeasureConstructed

    ContinuumHamiltonianVacuumConstructed : Set
    continuumHamiltonianVacuumConstructed :
      ContinuumHamiltonianVacuumConstructed

    ActualVacuumGraphOrMoscoLimit : Set
    actualVacuumGraphOrMoscoLimit : ActualVacuumGraphOrMoscoLimit

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

    RawPointwiseDecay : Set
    rawPointwiseDecay : RawPointwiseDecay

    AppendixFGeometryProfileSmallness : Set
    appendixFGeometryProfileSmallness : AppendixFGeometryProfileSmallness

open CMP116PhysicalSourceResiduals public

record OutstandingPhysicalFrontier : Set₁ where
  field
    f1UniformRGTransferCoercivity : UniformRGTransferCoercivity
    f2VaryingHilbertCommonCarrier : VaryingHilbertCommonCarrier
    f3PhysicalContinuumLimit : PhysicalContinuumLimitWitness

    Time : Set
    Vector : Set
    f4YMOSSameObject : YMOSSameObjectWitness Time Vector

open OutstandingPhysicalFrontier public

-- Status recut: these are the exact remaining conceptual fronts.
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

f1Level : ProofLevel
f1Level = conditional

f2Level : ProofLevel
f2Level = conditional

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
