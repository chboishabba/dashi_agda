module DASHI.Moonshine.PenumbralWeightTranslationClosure where

-- Bidirectional penumbral weight translation.  The SQ/Borcherds direction and
-- the trace-of-singular-moduli direction coexist over the same group and form
-- carriers, but round-trip identities are optional witnesses rather than
-- definitional equalities.

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Unit using (⊤; tt)
open import DASHI.Moonshine.PenumbralVectorValuedForm
open import DASHI.Moonshine.SingularThetaBorcherdsBridge
open import DASHI.Moonshine.PenumbralSQModuleLift
open import DASHI.Moonshine.TraceOfSingularModuliBridge

data OptionalWitness (Proposition : Set) : Set where
  noWitness : OptionalWitness Proposition
  witnessed : Proposition → OptionalWitness Proposition

record PenumbralWeightTranslationClosure : Setω where
  field
    halfCarrier : VectorValuedModularCarrier
    zeroCarrier : WeightZeroModularCarrier

    thetaLift : SingularThetaLift halfCarrier zeroCarrier
    borcherds :
      BorcherdsProductRealization halfCarrier zeroCarrier thetaLift
    sqModuleLift :
      SQModuleLift halfCarrier zeroCarrier thetaLift borcherds

    cmArithmetic : CMArithmetic
    singularScalar : SingularModuliScalar zeroCarrier cmArithmetic
    normalization :
      SingularModuliNormalization
        zeroCarrier cmArithmetic singularScalar
    singularModuliLift :
      TwinedSingularModuliLift
        halfCarrier zeroCarrier cmArithmetic singularScalar normalization

    SameFiniteGroup : Set
    sameFiniteGroup : SameFiniteGroup

    ForwardThenReverseAgreement : Set
    ReverseThenForwardAgreement : Set

    forwardThenReverseAgreement :
      OptionalWitness ForwardThenReverseAgreement
    reverseThenForwardAgreement :
      OptionalWitness ReverseThenForwardAgreement

    AvatarDiagramCommutes : Set
    avatarDiagramCommutation :
      OptionalWitness AvatarDiagramCommutes

record PenumbralWeightTranslationBoundary : Set where
  field
    forwardAndReverseArrowsShareCarriers : ⊤
    sameGroupWitnessDoesNotImplySameModule : ⊤
    roundTripsAreOptionalTheorems : ⊤
    diagramCommutationIsNotAssumed : ⊤
    noCategoricalEquivalenceClaim : ⊤

penumbralWeightTranslationBoundary :
  PenumbralWeightTranslationBoundary
penumbralWeightTranslationBoundary = record
  { forwardAndReverseArrowsShareCarriers = tt
  ; sameGroupWitnessDoesNotImplySameModule = tt
  ; roundTripsAreOptionalTheorems = tt
  ; diagramCommutationIsNotAssumed = tt
  ; noCategoricalEquivalenceClaim = tt
  }
