module DASHI.Physics.Closure.ShiftInhabitedDepthEnvelopeRG where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.Closure.BalancedTernaryContinuousEnvelope as Envelope
open import DASHI.Physics.Closure.FixedPointAnalyticRGTargets as Targets
open import DASHI.Physics.Closure.ShiftFiniteNormedTangent as Normed
open import DASHI.Physics.Closure.ShiftFiniteTangentSemigroup as Tangent

------------------------------------------------------------------------
-- Non-vacuous symbolic continuous-depth envelope.
--
-- Scalar is the balanced-ternary stream carrier itself and embed is identity.
-- This gives an inhabited, injective, genuinely non-singleton instance of the
-- repository's ContinuousDepthEnvelope interface.  The analytic predicates are
-- symbolic proof tokens; therefore this closes inhabitation and exact RG-depth
-- compatibility, not Euclidean convergence or real analytic estimates.

constantStream : Envelope.Trit → Envelope.Stream
constantStream t k = t

zeroStream : Envelope.Stream
zeroStream = constantStream Envelope.zer

oneStream : Envelope.Stream
oneStream = constantStream Envelope.pos

thirdStream : Envelope.Stream
thirdStream zero = Envelope.zer
thirdStream (suc n) = Envelope.pos

lambdaStream : Envelope.Stream
lambdaStream = thirdStream

leftAdd : Envelope.Stream → Envelope.Stream → Envelope.Stream
leftAdd x y = x

leftMultiply : Envelope.Stream → Envelope.Stream → Envelope.Stream
leftMultiply x y = x

negateStream : Envelope.Stream → Envelope.Stream
negateStream d k = Envelope.involution (d k)

tritStreamValue : Envelope.Trit → Envelope.Stream
tritStreamValue = constantStream

constantPower : Nat → Envelope.Stream
constantPower n = oneStream

tritDistanceStream : Envelope.Trit → Envelope.Trit → Envelope.Stream
tritDistanceStream x y = constantStream Envelope.zer

symbolicDepthKernelModel : Envelope.DepthKernelModel
symbolicDepthKernelModel =
  record
    { Scalar = Envelope.Stream
    ; zeroˢ = zeroStream
    ; oneˢ = oneStream
    ; thirdˢ = thirdStream
    ; lambda = lambdaStream
    ; _+ˢ_ = leftAdd
    ; _*ˢ_ = leftMultiply
    ; negateˢ = negateStream
    ; tritValue = tritStreamValue
    ; lambdaPower = constantPower
    ; tritDistance = tritDistanceStream
    ; Positive = λ x → ⊤
    ; LessThan = λ x y → ⊤
    ; AtMost = λ x y → ⊤
    ; Converges = λ sequence limit → ⊤
    ; IsWeightedDigitMetric = λ x y metric → ⊤
    ; CylinderControlled = λ n x y ex ey → ⊤
    ; FirstDifferenceBound = λ n metric → ⊤
    ; MetricRecoversCylinder = λ n x y metric → ⊤
    ; WeightedL2Summable = λ f g → ⊤
    ; powerZero = refl
    ; powerStep = λ n → refl
    ; negativeTritValue = refl
    ; zeroTritValue = refl
    ; positiveTritValue = refl
    }

symbolicDepthMetric :
  Envelope.Stream → Envelope.Stream → Envelope.Stream
symbolicDepthMetric x y = x

symbolicContinuousDepthEnvelope :
  Envelope.ContinuousDepthEnvelope symbolicDepthKernelModel
symbolicContinuousDepthEnvelope =
  record
    { embed = λ d → d
    ; depthMetric = symbolicDepthMetric
    ; lambdaPositive = tt
    ; lambdaBelowOne = tt
    ; lambdaBelowThird = tt
    ; finiteApproximantsConvergeToEmbed = λ d → tt
    ; depthMetricIsWeightedDigitSum = λ x y → tt
    ; cylinderContinuity = λ n x y agreement → tt
    ; firstDifferenceControlsMetric = λ n x y difference → tt
    ; injectiveBelowThird = λ x y equality → equality
    ; metricCylinderRecovery = λ n x y → tt
    }

allNegative : Envelope.Stream
allNegative = constantStream Envelope.neg

allPositive : Envelope.Stream
allPositive = constantStream Envelope.pos

negativeHead : Envelope.embed symbolicContinuousDepthEnvelope allNegative zero ≡ Envelope.neg
negativeHead = refl

positiveHead : Envelope.embed symbolicContinuousDepthEnvelope allPositive zero ≡ Envelope.pos
positiveHead = refl

negativeNotPositive : Envelope.neg ≡ Envelope.pos → ⊥
negativeNotPositive ()

nonVacuousHeadSeparation :
  Envelope.embed symbolicContinuousDepthEnvelope allNegative zero
    ≡
  Envelope.embed symbolicContinuousDepthEnvelope allPositive zero
    →
  ⊥
nonVacuousHeadSeparation equality = negativeNotPositive equality

------------------------------------------------------------------------
-- Exact finite RG embedding.

nextStream : Envelope.Stream
nextStream zero = Envelope.pos
nextStream (suc n) = Envelope.zer

startStream : Envelope.Stream
startStream zero = Envelope.pos
startStream (suc zero) = Envelope.pos
startStream (suc (suc n)) = Envelope.zer

encodePerturbation : Tangent.ShiftFinitePerturbation → Envelope.Stream
encodePerturbation Tangent.startPerturbation = startStream
encodePerturbation Tangent.nextPerturbation = nextStream
encodePerturbation Tangent.zeroPerturbation = zeroStream

PointwiseEqual : Envelope.Stream → Envelope.Stream → Set
PointwiseEqual x y = (k : Nat) → x k ≡ y k

coarseGrain : Envelope.Stream → Envelope.Stream
coarseGrain = Envelope.tail

finiteDepthStepCompatibility :
  (p : Tangent.ShiftFinitePerturbation) →
  PointwiseEqual
    (coarseGrain (encodePerturbation p))
    (encodePerturbation (Tangent.finiteDerivativeStep p))
finiteDepthStepCompatibility Tangent.startPerturbation zero = refl
finiteDepthStepCompatibility Tangent.startPerturbation (suc k) = refl
finiteDepthStepCompatibility Tangent.nextPerturbation zero = refl
finiteDepthStepCompatibility Tangent.nextPerturbation (suc k) = refl
finiteDepthStepCompatibility Tangent.zeroPerturbation k = refl

rgIterate : Nat → Envelope.Stream → Envelope.Stream
rgIterate n = Tangent.iterate n coarseGrain

RGIterateCompatibility : Set
RGIterateCompatibility =
  (m n : Nat) →
  (d : Envelope.Stream) →
  rgIterate (m + n) d ≡ rgIterate n (rgIterate m d)

rgIterateCompatibility : RGIterateCompatibility
rgIterateCompatibility m n d =
  Tangent.iterate-plus m n coarseGrain d

EnvelopeIntertwinesRG : Set
EnvelopeIntertwinesRG =
  (d : Envelope.Stream) →
  Envelope.embed symbolicContinuousDepthEnvelope (coarseGrain d)
    ≡
  coarseGrain (Envelope.embed symbolicContinuousDepthEnvelope d)

envelopeIntertwinesRG : EnvelopeIntertwinesRG
envelopeIntertwinesRG d = refl

EncodedConvergesToFixedPoint : Set
EncodedConvergesToFixedPoint =
  (p : Tangent.ShiftFinitePerturbation) →
  PointwiseEqual
    (rgIterate (suc (suc zero)) (encodePerturbation p))
    zeroStream

encodedConvergesToFixedPoint : EncodedConvergesToFixedPoint
encodedConvergesToFixedPoint Tangent.startPerturbation k = refl
encodedConvergesToFixedPoint Tangent.nextPerturbation k = refl
encodedConvergesToFixedPoint Tangent.zeroPerturbation k = refl

ScalingTransportAcrossDepth : Set
ScalingTransportAcrossDepth =
  (p : Tangent.ShiftFinitePerturbation) →
  Normed.finiteNorm (Tangent.finiteDerivativeStep p)
    Data.Nat.≤
  Normed.finiteNorm p

scalingTransportAcrossDepth : ScalingTransportAcrossDepth
scalingTransportAcrossDepth = Normed.derivativeNormNonIncreasing

shiftContinuumRGControl :
  Targets.ContinuumRGControl
    symbolicDepthKernelModel
    symbolicContinuousDepthEnvelope
shiftContinuumRGControl =
  record
    { coarseGrain = coarseGrain
    ; fixedStream = zeroStream
    ; RGIterate = rgIterate
    ; fixedPointLaw = refl
    ; iterateCompatibility = RGIterateCompatibility
    ; finiteSemigroupDepthCompatibility =
        (p : Tangent.ShiftFinitePerturbation) →
        PointwiseEqual
          (coarseGrain (encodePerturbation p))
          (encodePerturbation (Tangent.finiteDerivativeStep p))
    ; envelopeIntertwinesRG = EnvelopeIntertwinesRG
    ; convergenceToFixedPoint = EncodedConvergesToFixedPoint
    ; scalingTransportAcrossDepth = ScalingTransportAcrossDepth
    }

record ShiftInhabitedDepthEnvelopeRG : Setω where
  field
    depthModel : Envelope.DepthKernelModel
    continuousEnvelope : Envelope.ContinuousDepthEnvelope depthModel
    continuumRG : Targets.ContinuumRGControl depthModel continuousEnvelope
    finiteDepthCompatibility :
      (p : Tangent.ShiftFinitePerturbation) →
      PointwiseEqual
        (coarseGrain (encodePerturbation p))
        (encodePerturbation (Tangent.finiteDerivativeStep p))
    iterateLaw : RGIterateCompatibility
    envelopeRGIntertwiner : EnvelopeIntertwinesRG
    encodedAttraction : EncodedConvergesToFixedPoint
    scalingTransport : ScalingTransportAcrossDepth
    nonVacuous :
      Envelope.embed symbolicContinuousDepthEnvelope allNegative zero
        ≡
      Envelope.embed symbolicContinuousDepthEnvelope allPositive zero
        →
      ⊥
    nonClaimBoundary : List String

open ShiftInhabitedDepthEnvelopeRG public

canonicalShiftInhabitedDepthEnvelopeRG : ShiftInhabitedDepthEnvelopeRG
canonicalShiftInhabitedDepthEnvelopeRG =
  record
    { depthModel = symbolicDepthKernelModel
    ; continuousEnvelope = symbolicContinuousDepthEnvelope
    ; continuumRG = shiftContinuumRGControl
    ; finiteDepthCompatibility = finiteDepthStepCompatibility
    ; iterateLaw = rgIterateCompatibility
    ; envelopeRGIntertwiner = envelopeIntertwinesRG
    ; encodedAttraction = encodedConvergesToFixedPoint
    ; scalingTransport = scalingTransportAcrossDepth
    ; nonVacuous = nonVacuousHeadSeparation
    ; nonClaimBoundary =
        "ShiftInhabitedDepthEnvelopeRG is an inhabited injective stream-valued depth-envelope reference"
        ∷ "the carrier is non-singleton, witnessed by distinct negative and positive heads"
        ∷ "tail coarse-graining exactly intertwines the encoded finite perturbation step"
        ∷ "all encoded perturbations reach the zero stream after two coarse-graining steps"
        ∷ "analytic predicates in the symbolic DepthKernelModel are proof tokens, not real-number estimates"
        ∷ "No Euclidean convergence, physical continuum limit, p-adic completion, or analytic RG universality theorem is claimed"
        ∷ []
    }
