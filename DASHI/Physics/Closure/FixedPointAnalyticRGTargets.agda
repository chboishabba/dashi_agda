module DASHI.Physics.Closure.FixedPointAnalyticRGTargets where

open import Agda.Primitive using (Level; Setω; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List)

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Envelope

------------------------------------------------------------------------
-- Theorem-facing analytic targets for the fixed-point RG/CFT lane.
--
-- These records state the stronger objects requested by the roadmap without
-- manufacturing instances from the finite three-point carrier.  A future
-- analytic model must supply the laws explicitly.

record AdditiveNormedTangent
  {ℓs ℓt : Level}
  (Scalar : Set ℓs)
  (Tangent : Set ℓt)
  : Set (lsuc (ℓs ⊔ ℓt)) where
  field
    zeroˢ : Scalar
    oneˢ : Scalar
    _+ˢ_ : Scalar → Scalar → Scalar
    _*ˢ_ : Scalar → Scalar → Scalar

    zeroᵀ : Tangent
    _+ᵀ_ : Tangent → Tangent → Tangent
    _·_ : Scalar → Tangent → Tangent
    norm : Tangent → Scalar
    distance : Tangent → Tangent → Scalar

    additiveAssociative :
      (x y z : Tangent) →
      (x +ᵀ y) +ᵀ z ≡ x +ᵀ (y +ᵀ z)
    additiveCommutative :
      (x y : Tangent) →
      x +ᵀ y ≡ y +ᵀ x
    additiveUnit :
      (x : Tangent) →
      zeroᵀ +ᵀ x ≡ x

    scalarUnit :
      (x : Tangent) →
      oneˢ · x ≡ x
    scalarDistributes :
      (a : Scalar) (x y : Tangent) →
      a · (x +ᵀ y) ≡ (a · x) +ᵀ (a · y)

    NormAtMost : Scalar → Scalar → Set
    normZero : norm zeroᵀ ≡ zeroˢ
    triangle :
      (x y : Tangent) →
      NormAtMost (norm (x +ᵀ y)) (norm x +ˢ norm y)

open AdditiveNormedTangent public

record FrechetLinearizedSemigroup
  {ℓs ℓt ℓtime : Level}
  (Scalar : Set ℓs)
  (Tangent : Set ℓt)
  (Time : Set ℓtime)
  (T : AdditiveNormedTangent Scalar Tangent)
  : Setω where
  field
    zeroTime : Time
    _+time_ : Time → Time → Time
    flow : Time → Tangent → Tangent
    derivative : Tangent → Tangent
    generator : Tangent → Tangent

    zeroTimeLaw :
      (x : Tangent) →
      flow zeroTime x ≡ x
    semigroupLaw :
      (s t : Time) (x : Tangent) →
      flow (s +time t) x ≡ flow t (flow s x)

    derivativeAdditive :
      (x y : Tangent) →
      derivative (AdditiveNormedTangent._+ᵀ_ T x y)
      ≡
      AdditiveNormedTangent._+ᵀ_ T (derivative x) (derivative y)

    FrechetRemainderControlled : Set
    GeneratorLimitExists : Set
    StronglyContinuous : Set

open FrechetLinearizedSemigroup public

record PhysicalScalingSpectrum
  {ℓs ℓo : Level}
  (Scalar : Set ℓs)
  (Operator : Set ℓo)
  : Set (lsuc (ℓs ⊔ ℓo)) where
  field
    scalingDimension : Operator → Scalar
    anomalousDimension : Operator → Scalar
    RGTransform : Operator → Operator
    ScalingEigenEquation : Operator → Set
    spectrumComplete : Set
    spectrumPhysicalNormalization : Set

open PhysicalScalingSpectrum public

record LocalOPECrossing
  {ℓs ℓx ℓo : Level}
  (Scalar : Set ℓs)
  (Position : Set ℓx)
  (Operator : Set ℓo)
  : Setω where
  field
    coefficient :
      Operator → Operator → Operator → Position → Position → Scalar
    product :
      Operator → Operator → Position → Position → Operator
    correlation2 : Operator → Operator → Position → Position → Scalar
    correlation4 :
      Operator → Operator → Operator → Operator →
      Position → Position → Position → Position → Scalar

    Locality : Set
    OPEConverges : Set
    CrossingSymmetry : Set
    AssociativityInCommonDomain : Set

open LocalOPECrossing public

record ContinuumRGControl
  (M : Envelope.DepthKernelModel)
  (E : Envelope.ContinuousDepthEnvelope M)
  : Setω where
  field
    coarseGrain : Envelope.Stream → Envelope.Stream
    fixedStream : Envelope.Stream
    RGIterate : Nat → Envelope.Stream → Envelope.Stream

    fixedPointLaw : coarseGrain fixedStream ≡ fixedStream
    iterateCompatibility : Set
    finiteSemigroupDepthCompatibility : Set
    envelopeIntertwinesRG : Set
    convergenceToFixedPoint : Set
    scalingTransportAcrossDepth : Set

open ContinuumRGControl public

record StressTensorConformalWard
  {ℓs ℓx ℓo ℓt : Level}
  (Scalar : Set ℓs)
  (Position : Set ℓx)
  (Operator : Set ℓo)
  (StressTensor : Set ℓt)
  : Setω where
  field
    stressInsertion : StressTensor → Position → Operator
    correlation : List Operator → List Position → Scalar
    divergenceFree : Set
    traceCondition : Set
    translationWard : Set
    dilationWard : Set
    specialConformalWard : Set
    wardCompatibleWithOPE : Set

open StressTensorConformalWard public

record FixedPointAnalyticRGCFTRoute : Setω where
  field
    Scalar : Set
    Tangent : Set
    Time : Set
    Position : Set
    Operator : Set
    StressTensor : Set

    tangent : AdditiveNormedTangent Scalar Tangent
    linearizedSemigroup :
      FrechetLinearizedSemigroup Scalar Tangent Time tangent
    physicalSpectrum : PhysicalScalingSpectrum Scalar Operator
    localOPE : LocalOPECrossing Scalar Position Operator

    depthModel : Envelope.DepthKernelModel
    continuousEnvelope : Envelope.ContinuousDepthEnvelope depthModel
    continuumRG : ContinuumRGControl depthModel continuousEnvelope

    conformalWard :
      StressTensorConformalWard
        Scalar Position Operator StressTensor

    claimBoundary : List String

open FixedPointAnalyticRGCFTRoute public
