module DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact as Cutset
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- SCALING MODEL IDENTIFIABILITY
--
-- A source-amplitude x material-regime sweep is necessary, but a sufficiently
-- flexible source-dependent additive residual can mimic a multiplicative
-- constitutive coefficient over a finite design.  Model-class separation is a
-- separate coordinate, not something the word "scaling" pays automatically.
------------------------------------------------------------------------

data ScalingModelClass : Set where
  sourceIndependentAdditiveResidual : ScalingModelClass
  sourceDependentAdditiveResidual : ScalingModelClass
  multiplicativeConstitutiveCoefficient : ScalingModelClass

data FiniteSweepSignature : Set where
  sourceIndependentRegimeOffset : FiniteSweepSignature
  sourceScaledRegimeDifference : FiniteSweepSignature

data ModelInterpretation : Set where
  additiveInterpretation : ModelInterpretation
  constitutiveInterpretation : ModelInterpretation

sweepSignature : ScalingModelClass → FiniteSweepSignature
sweepSignature sourceIndependentAdditiveResidual = sourceIndependentRegimeOffset
sweepSignature sourceDependentAdditiveResidual = sourceScaledRegimeDifference
sweepSignature multiplicativeConstitutiveCoefficient = sourceScaledRegimeDifference

interpretation : ScalingModelClass → ModelInterpretation
interpretation sourceIndependentAdditiveResidual = additiveInterpretation
interpretation sourceDependentAdditiveResidual = additiveInterpretation
interpretation multiplicativeConstitutiveCoefficient = constitutiveInterpretation

sourceDependentAdditiveVsMultiplicativeCollision :
  sweepSignature sourceDependentAdditiveResidual
    ≡ sweepSignature multiplicativeConstitutiveCoefficient
sourceDependentAdditiveVsMultiplicativeCollision = refl

finiteScalingSignatureDoesNotFixInterpretation :
  interpretation sourceDependentAdditiveResidual
    ≡ interpretation multiplicativeConstitutiveCoefficient → ⊥
finiteScalingSignatureDoesNotFixInterpretation ()

------------------------------------------------------------------------
-- Extra discriminator coordinates.
------------------------------------------------------------------------

data ModelClassDiscriminator : Set where
  zeroSourceInterceptControl : ModelClassDiscriminator
  independentOrderParameterAxis : ModelClassDiscriminator
  explicitModelFormAuthority : ModelClassDiscriminator
  outOfSampleScalingPoint : ModelClassDiscriminator
  signCrossingLocalization : ModelClassDiscriminator

producerForDiscriminator : ModelClassDiscriminator → Search.ProducerClass
producerForDiscriminator zeroSourceInterceptControl = Search.discriminatorProducer
producerForDiscriminator independentOrderParameterAxis = Search.discriminatorProducer
producerForDiscriminator explicitModelFormAuthority = Search.propositionSourceProducer
producerForDiscriminator outOfSampleScalingPoint = Search.empiricalEvidenceProducer
producerForDiscriminator signCrossingLocalization = Search.discriminatorProducer

record ScalingModelSeparationReceipt : Set₁ where
  constructor scaling-model-separation-receipt
  field
    upstreamCutset : Cutset.MaterialEffectiveNegativeGDiscriminationReceipt

    ZeroSourceInterceptReceipt : Set
    zeroSourceInterceptReceipt : ZeroSourceInterceptReceipt

    IndependentOrderParameterReceipt : Set
    independentOrderParameterReceipt : IndependentOrderParameterReceipt

    ModelFormAuthorityReceipt : Set
    modelFormAuthorityReceipt : ModelFormAuthorityReceipt

    OutOfSampleScalingReceipt : Set
    outOfSampleScalingReceipt : OutOfSampleScalingReceipt

    SignCrossingLocalizationReceipt : Set
    signCrossingLocalizationReceipt : SignCrossingLocalizationReceipt

open ScalingModelSeparationReceipt public

------------------------------------------------------------------------
-- Attribution: model-class separation is internal proof-search logic; any
-- external model form used downstream must separately carry source entitlement.
------------------------------------------------------------------------

internalAttributionShape : Shape.RequiredAttributionShape
internalAttributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

record ScalingModelDiscriminatorBoundary : Set where
  constructor scaling-model-discriminator-boundary
  field
    twoAxisFiniteSweepUniquelyIdentifiesConstitutiveModel : Bool
    sourceDependentAdditiveCanMimicMultiplicativeSignature : Bool
    zeroSourceControlMayHelpSeparateModelClasses : Bool
    independentOrderParameterAxisRequiredForStrongerSeparation : Bool
    externalModelFormNeedsSeparateSourceEntitlement : Bool
    outOfSampleCheckRequiredForPromotion : Bool
    scalingModelSeparationAutomaticallyProvesNegativeG : Bool
    internalSeparationTheoremNeedsFreshExternalCitation : Bool

canonicalScalingModelDiscriminatorBoundary : ScalingModelDiscriminatorBoundary
canonicalScalingModelDiscriminatorBoundary =
  scaling-model-discriminator-boundary
    false true true true true true false false
