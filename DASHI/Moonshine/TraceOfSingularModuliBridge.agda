module DASHI.Moonshine.TraceOfSingularModuliBridge where

-- Arithmetic translation from weight-zero modular functions to half-integral
-- weight coefficients by stabilizer-weighted traces over CM classes.  This is
-- distinct from the singular-theta/Borcherds product lift and is not assumed to
-- be its inverse.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Unit using (⊤; tt)
import DASHI.Moonshine.GradedRepresentation as GR
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.SingularThetaBorcherdsBridge

record CMArithmetic : Set₁ where
  field
    Discriminant : Set
    BinaryQuadraticForm : Set
    CMPoint : Set
    Class : Discriminant → Set

    representative :
      {D : Discriminant} → Class D → BinaryQuadraticForm
    discriminantOf : BinaryQuadraticForm → Discriminant
    cmPoint : BinaryQuadraticForm → CMPoint

    NegativeDiscriminant : Discriminant → Set
    PositiveDefinite : BinaryQuadraticForm → Set
    Primitive : BinaryQuadraticForm → Set

    representativeHasDiscriminant :
      {D : Discriminant} →
      (class : Class D) →
      discriminantOf (representative class) ≡ D

    representativePositiveDefinite :
      {D : Discriminant} →
      (class : Class D) →
      PositiveDefinite (representative class)

    representativePrimitive :
      {D : Discriminant} →
      (class : Class D) →
      Primitive (representative class)

record SingularModuliScalar
  (zeroCarrier : WeightZeroModularCarrier)
  (cm : CMArithmetic) : Set₁ where
  field
    Scalar : Set
    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar

    evaluate :
      WeightZeroModularCarrier.ModularFunction zeroCarrier →
      CMArithmetic.CMPoint cm → Scalar

    inverseStabilizerWeight :
      CMArithmetic.BinaryQuadraticForm cm → Scalar

    sumOverClasses :
      (D : CMArithmetic.Discriminant cm) →
      (CMArithmetic.Class cm D → Scalar) → Scalar

    SumIsFinite : CMArithmetic.Discriminant cm → Set
    sumIsFinite :
      (D : CMArithmetic.Discriminant cm) →
      SumIsFinite D

singularModulusTerm :
  (zeroCarrier : WeightZeroModularCarrier) →
  (cm : CMArithmetic) →
  (scalar : SingularModuliScalar zeroCarrier cm) →
  WeightZeroModularCarrier.ModularFunction zeroCarrier →
  {D : CMArithmetic.Discriminant cm} →
  CMArithmetic.Class cm D →
  SingularModuliScalar.Scalar scalar
singularModulusTerm zeroCarrier cm scalar function class =
  SingularModuliScalar.multiply scalar
    (SingularModuliScalar.inverseStabilizerWeight scalar
      (CMArithmetic.representative cm class))
    (SingularModuliScalar.evaluate scalar function
      (CMArithmetic.cmPoint cm
        (CMArithmetic.representative cm class)))

traceOfSingularModuli :
  (zeroCarrier : WeightZeroModularCarrier) →
  (cm : CMArithmetic) →
  (scalar : SingularModuliScalar zeroCarrier cm) →
  WeightZeroModularCarrier.ModularFunction zeroCarrier →
  CMArithmetic.Discriminant cm →
  SingularModuliScalar.Scalar scalar
traceOfSingularModuli zeroCarrier cm scalar function D =
  SingularModuliScalar.sumOverClasses scalar D
    (singularModulusTerm zeroCarrier cm scalar function)

record SingularModuliNormalization
  (zeroCarrier : WeightZeroModularCarrier)
  (cm : CMArithmetic)
  (scalar : SingularModuliScalar zeroCarrier cm) : Set₁ where
  field
    OrientationConvention : Set
    BranchConvention : Set
    StabilizerConvention : Set
    ConstantTermCorrection : Set

    orientationConvention : OrientationConvention
    branchConvention : BranchConvention
    stabilizerConvention : StabilizerConvention
    constantTermCorrection : ConstantTermCorrection

record TraceOfSingularModuliLift
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (cm : CMArithmetic)
  (scalar : SingularModuliScalar zeroCarrier cm)
  (normalization :
    SingularModuliNormalization zeroCarrier cm scalar) : Setω where
  field
    sourceFunction :
      WeightZeroModularCarrier.ModularFunction zeroCarrier
    targetForm : VectorValuedModularCarrier.Vector halfCarrier

    weakHolomorphy :
      VectorValuedModularCarrier.weaklyHolomorphic halfCarrier targetForm

    Index : Set
    indexDiscriminant :
      Index → CMArithmetic.Discriminant cm
    indexResidue : Index → Nat
    indexExponent :
      Index → VectorValuedModularCarrier.FormalExponent halfCarrier

    scalarTransport :
      SingularModuliScalar.Scalar scalar →
      VectorValuedModularCarrier.Scalar halfCarrier

    coefficientAsSingularModuliTrace :
      (index : Index) →
      VectorValuedModularCarrier.coefficient halfCarrier targetForm
        (indexResidue index) (indexExponent index)
      ≡
      scalarTransport
        (traceOfSingularModuli zeroCarrier cm scalar sourceFunction
          (indexDiscriminant index))

record TwinedSingularModuliLift
  (halfCarrier : VectorValuedModularCarrier)
  (zeroCarrier : WeightZeroModularCarrier)
  (cm : CMArithmetic)
  (scalar : SingularModuliScalar zeroCarrier cm)
  (normalization :
    SingularModuliNormalization zeroCarrier cm scalar) : Setω where
  field
    G : Set
    group : GR.Group G

    weightZeroTwining :
      G → WeightZeroModularCarrier.ModularFunction zeroCarrier
    halfWeightTwining :
      G → VectorValuedModularCarrier.Vector halfCarrier

    liftForElement :
      (g : G) →
      TraceOfSingularModuliLift
        halfCarrier zeroCarrier cm scalar normalization

    LiftUsesTwinedFunctions : G → Set
    liftUsesTwinedFunctions :
      (g : G) → LiftUsesTwinedFunctions g

record TraceOfSingularModuliBoundary : Set where
  field
    cmClassFinitenessRequired : ⊤
    inverseStabilizerWeightsRequired : ⊤
    orientationAndBranchConventionsRequired : ⊤
    constantTermCorrectionsTrackedSeparately : ⊤
    traceLiftIsNotDeclaredInverseToBorcherdsLift : ⊤
    noCoefficientFieldClaimWithoutArithmeticProof : ⊤

traceOfSingularModuliBoundary : TraceOfSingularModuliBoundary
traceOfSingularModuliBoundary = record
  { cmClassFinitenessRequired = tt
  ; inverseStabilizerWeightsRequired = tt
  ; orientationAndBranchConventionsRequired = tt
  ; constantTermCorrectionsTrackedSeparately = tt
  ; traceLiftIsNotDeclaredInverseToBorcherdsLift = tt
  ; noCoefficientFieldClaimWithoutArithmeticProof = tt
  }
