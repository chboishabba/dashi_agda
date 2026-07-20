module DASHI.Moonshine.PenumbralSQModuleLift where

-- Explicit module-level form of the singular-theta/Borcherds construction.
-- The weight-zero module SQ(W) is assembled coefficientwise from Fock factors
-- built with exterior and symmetric powers.  Infinite products are admitted
-- only after each finite grade is proved to stabilise.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.GradedRepresentation as GR
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.SingularThetaBorcherdsBridge

record LambdaRingModuleCarrier
  (G Scalar : Set)
  (group : GR.Group G) : Setω where
  field
    VirtualModule : Set
    zeroVirtual : VirtualModule
    tensorUnit : VirtualModule
    addVirtual : VirtualModule → VirtualModule → VirtualModule
    negateVirtual : VirtualModule → VirtualModule
    tensorVirtual : VirtualModule → VirtualModule → VirtualModule

    exteriorPower : Nat → VirtualModule → VirtualModule
    symmetricPower : Nat → VirtualModule → VirtualModule

    trace : G → VirtualModule → Scalar

    TraceAdditive : G → VirtualModule → VirtualModule → Set
    TraceMultiplicative : G → VirtualModule → VirtualModule → Set
    ExteriorPowerTraceLaw : G → Nat → VirtualModule → Set
    SymmetricPowerTraceLaw : G → Nat → VirtualModule → Set
    TensorUnitLaw : VirtualModule → Set

    traceAdditive :
      (g : G) →
      (u v : VirtualModule) →
      TraceAdditive g u v

    traceMultiplicative :
      (g : G) →
      (u v : VirtualModule) →
      TraceMultiplicative g u v

    exteriorPowerTraceLaw :
      (g : G) →
      (n : Nat) →
      (u : VirtualModule) →
      ExteriorPowerTraceLaw g n u

    symmetricPowerTraceLaw :
      (g : G) →
      (n : Nat) →
      (u : VirtualModule) →
      SymmetricPowerTraceLaw g n u

    tensorUnitLaw :
      (u : VirtualModule) → TensorUnitLaw u

record HalfWeightModuleInput
  (G Scalar : Set)
  (group : GR.Group G)
  (modules : LambdaRingModuleCarrier G Scalar group) : Setω where
  field
    positiveIndex : Nat
    Positive : Nat → Set
    positiveIndexWitness : Positive positiveIndex

    bosonicGrade : Nat → LambdaRingModuleCarrier.VirtualModule modules
    fermionicGrade : Nat → LambdaRingModuleCarrier.VirtualModule modules

    zeroModeBosonic : LambdaRingModuleCarrier.VirtualModule modules
    zeroModeFermionic : LambdaRingModuleCarrier.VirtualModule modules

    RationalCharacter :
      LambdaRingModuleCarrier.VirtualModule modules → Set
    bosonicCharactersRational :
      (n : Nat) → RationalCharacter (bosonicGrade n)
    fermionicCharactersRational :
      (n : Nat) → RationalCharacter (fermionicGrade n)

record FockFactorConstruction
  (G Scalar : Set)
  (group : GR.Group G)
  (modules : LambdaRingModuleCarrier G Scalar group)
  (input : HalfWeightModuleInput G Scalar group modules) : Setω where
  field
    factor : Nat → LambdaRingModuleCarrier.VirtualModule modules

    FactorDefinition :
      Nat → LambdaRingModuleCarrier.VirtualModule modules → Set

    factorDefinition :
      (n : Nat) →
      FactorDefinition n (factor n)

    factorUsesExteriorPowers :
      (n : Nat) → Set
    factorUsesSymmetricPowers :
      (n : Nat) → Set

    exteriorPowerWitness :
      (n : Nat) → factorUsesExteriorPowers n
    symmetricPowerWitness :
      (n : Nat) → factorUsesSymmetricPowers n

record CompletedFockProduct
  (G Scalar : Set)
  (group : GR.Group G)
  (modules : LambdaRingModuleCarrier G Scalar group)
  {input : HalfWeightModuleInput G Scalar group modules}
  (factors : FockFactorConstruction G Scalar group modules input)
  : Setω where
  field
    finiteTensorProduct :
      Nat → LambdaRingModuleCarrier.VirtualModule modules

    finiteProductStartsAtTensorUnit :
      finiteTensorProduct 0 ≡
      LambdaRingModuleCarrier.tensorUnit modules

    FiniteProductCorrect : Nat → Set
    finiteProductCorrect :
      (cutoff : Nat) → FiniteProductCorrect cutoff

    CompletedModule : Set
    completedProduct : CompletedModule

    GradePiece :
      CompletedModule → Nat →
      LambdaRingModuleCarrier.VirtualModule modules → Set

    gradePiece :
      Nat → LambdaRingModuleCarrier.VirtualModule modules

    stabilisationCutoff : Nat → Nat
    CoefficientwiseStabilises :
      (grade cutoff : Nat) → Set

    stabilisationWitness :
      (grade : Nat) →
      CoefficientwiseStabilises grade (stabilisationCutoff grade)

    completedGradeCorrect :
      (grade : Nat) →
      GradePiece completedProduct grade (gradePiece grade)

record SQModuleLift
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier)
  (borcherds :
    BorcherdsProductRealization halfCarrier zeroCarrier thetaLift)
  : Setω where
  field
    G : Set
    group : GR.Group G
    Scalar : Set
    modules : LambdaRingModuleCarrier G Scalar group
    input : HalfWeightModuleInput G Scalar group modules
    factors : FockFactorConstruction G Scalar group modules input
    completion : CompletedFockProduct G Scalar group modules factors

    halfForm : VectorValuedModularCarrier.Vector halfCarrier
    halfFormWeaklyHolomorphic :
      VectorValuedModularCarrier.weaklyHolomorphic halfCarrier halfForm

    twinedWeightZeroFunction :
      G → WeightZeroModularCarrier.ModularFunction zeroCarrier

    identityFunctionIsThetaLift :
      twinedWeightZeroFunction (GR.Group.identity group)
      ≡ SingularThetaLift.lift thetaLift halfForm

    ProductTraceAgreement : G → Nat → Set
    productTraceAgreement :
      (g : G) →
      (n : Nat) →
      ProductTraceAgreement g n

    WeightZeroModule : Set
    weightZeroModule : WeightZeroModule

    GradeRealization :
      WeightZeroModule → Nat →
      LambdaRingModuleCarrier.VirtualModule modules → Set

    gradeRealization :
      (n : Nat) →
      GradeRealization weightZeroModule n
        (CompletedFockProduct.gradePiece completion n)

    CandidateWeightZeroModule : Set
    SameEquivariantTrace : CandidateWeightZeroModule → Set
    EquivalentModule : CandidateWeightZeroModule → WeightZeroModule → Set

    uniqueness :
      (candidate : CandidateWeightZeroModule) →
      SameEquivariantTrace candidate →
      EquivalentModule candidate weightZeroModule

record SQModuleLiftBoundary : Set where
  field
    formalInfiniteTensorNeedsCoefficientwiseStabilisation : ⊤
    emptyTensorProductUsesTensorUnit : ⊤
    exteriorAndSymmetricPowerTraceLawsRequired : ⊤
    productIdentityDoesNotConstructCompletionAutomatically : ⊤
    uniquenessIsUpToChosenModuleEquivalence : ⊤
    noConformalFieldTheoryConstructionClaim : ⊤

sqModuleLiftBoundary : SQModuleLiftBoundary
sqModuleLiftBoundary = record
  { formalInfiniteTensorNeedsCoefficientwiseStabilisation = tt
  ; emptyTensorProductUsesTensorUnit = tt
  ; exteriorAndSymmetricPowerTraceLawsRequired = tt
  ; productIdentityDoesNotConstructCompletionAutomatically = tt
  ; uniquenessIsUpToChosenModuleEquivalence = tt
  ; noConformalFieldTheoryConstructionClaim = tt
  }
