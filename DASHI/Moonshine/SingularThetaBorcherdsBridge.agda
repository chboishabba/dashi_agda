module DASHI.Moonshine.SingularThetaBorcherdsBridge where

-- Function-level and module-level translation from rational weight-one-half
-- moonshine to weight-zero moonshine.  The analytic singular theta lift, the
-- Borcherds product expansion, and the finite-group module construction are
-- kept as separate proof obligations.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.GradedRepresentation as GR
open import DASHI.Moonshine.PenumbralVectorValuedForm

record WeightZeroModularCarrier : Set₁ where
  field
    Scalar : Set
    ModularFunction : Set
    ProductExpansion : Set
    DivisorDatum : Set

    weightZero : ModularFunction → Set
    meromorphic : ModularFunction → Set
    normalizedAtCusp : ModularFunction → Set
    productOf : ModularFunction → ProductExpansion → Set
    divisorOf : ModularFunction → DivisorDatum → Set

record SingularThetaLift
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier) : Set₁ where
  field
    lift :
      VectorValuedModularCarrier.Vector halfCarrier →
      WeightZeroModularCarrier.ModularFunction zeroCarrier

    LiftDefined :
      VectorValuedModularCarrier.Vector halfCarrier → Set
    liftDefined :
      (form : VectorValuedModularCarrier.Vector halfCarrier) →
      VectorValuedModularCarrier.weaklyHolomorphic halfCarrier form →
      LiftDefined form

    outputHasWeightZero :
      (form : VectorValuedModularCarrier.Vector halfCarrier) →
      VectorValuedModularCarrier.weaklyHolomorphic halfCarrier form →
      WeightZeroModularCarrier.weightZero zeroCarrier (lift form)

record BorcherdsProductRealization
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (thetaLift : SingularThetaLift halfCarrier zeroCarrier) : Set₁ where
  field
    productExpansion :
      VectorValuedModularCarrier.Vector halfCarrier →
      WeightZeroModularCarrier.ProductExpansion zeroCarrier

    divisorDatum :
      VectorValuedModularCarrier.Vector halfCarrier →
      WeightZeroModularCarrier.DivisorDatum zeroCarrier

    borcherdsProductLaw :
      (form : VectorValuedModularCarrier.Vector halfCarrier) →
      WeightZeroModularCarrier.productOf zeroCarrier
        (SingularThetaLift.lift thetaLift form)
        (productExpansion form)

    divisorLaw :
      (form : VectorValuedModularCarrier.Vector halfCarrier) →
      WeightZeroModularCarrier.divisorOf zeroCarrier
        (SingularThetaLift.lift thetaLift form)
        (divisorDatum form)

record EquivariantModuleProduct
  (G : Set)
  (group : GR.Group G)
  (halfModule weightZeroModule : Set)
  (HalfTrace WeightZeroTrace : G → Nat → Set)
  : Setω where
  field
    buildWeightZeroModule : halfModule → weightZeroModule

    ProductCoefficient : halfModule → Nat → Set
    WeightZeroGrade : weightZeroModule → Nat → Set

    productCoefficientsDetermineGrades :
      (module : halfModule) →
      (n : Nat) →
      ProductCoefficient module n →
      WeightZeroGrade (buildWeightZeroModule module) n

    equivariantTraceCompatibility :
      (g : G) →
      (module : halfModule) →
      (n : Nat) →
      HalfTrace g n →
      WeightZeroTrace g n

record ModularProductModuleBridge
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier) : Setω where
  field
    thetaLift : SingularThetaLift halfCarrier zeroCarrier
    borcherds :
      BorcherdsProductRealization halfCarrier zeroCarrier thetaLift

    G : Set
    group : GR.Group G
    HalfModule WeightZeroModule : Set
    HalfTrace WeightZeroTrace : G → Nat → Set

    moduleProduct :
      EquivariantModuleProduct G group HalfModule WeightZeroModule
        HalfTrace WeightZeroTrace

record SingularThetaBorcherdsBoundary : Set where
  field
    analyticLiftAndModuleLiftAreDistinct : ⊤
    productExpansionRequiresConvergenceAndDivisorProof : ⊤
    weightZeroOutputDoesNotImplyGenusZero : ⊤
    inverseTraceConstructionNotAutomatic : ⊤
    noGeneralizedMoonshineEquivalenceClaim : ⊤

singularThetaBorcherdsBoundary : SingularThetaBorcherdsBoundary
singularThetaBorcherdsBoundary = record
  { analyticLiftAndModuleLiftAreDistinct = tt
  ; productExpansionRequiresConvergenceAndDivisorProof = tt
  ; weightZeroOutputDoesNotImplyGenusZero = tt
  ; inverseTraceConstructionNotAutomatic = tt
  ; noGeneralizedMoonshineEquivalenceClaim = tt
  }
