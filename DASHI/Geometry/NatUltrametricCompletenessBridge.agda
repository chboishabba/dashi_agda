module DASHI.Geometry.NatUltrametricCompletenessBridge where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties as NatP
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)
open import Ultrametric as UMetric
open import DASHI.Geometry.CompleteUltrametric as CU
open import DASHI.Geometry.CompleteUltrametricNat as CUN

one : Nat
one = suc zero

onePositive : zero < one
onePositive = s≤s z≤n

data CompletenessLayer : Set where
  natDiscrete qqCarrier noCarrier surrealCarrier hilbertCarrier : CompletenessLayer

layerCompletenessSupported : CompletenessLayer → Bool
layerCompletenessSupported natDiscrete = true
layerCompletenessSupported qqCarrier = false
layerCompletenessSupported noCarrier = false
layerCompletenessSupported surrealCarrier = false
layerCompletenessSupported hilbertCarrier = false

qqCompletenessUnsupported :
  layerCompletenessSupported qqCarrier ≡ false
qqCompletenessUnsupported = refl

noCompletenessUnsupported :
  layerCompletenessSupported noCarrier ≡ false
noCompletenessUnsupported = refl

surrealCompletenessUnsupported :
  layerCompletenessSupported surrealCarrier ≡ false
surrealCompletenessUnsupported = refl

hilbertCompletenessUnsupported :
  layerCompletenessSupported hilbertCarrier ≡ false
hilbertCompletenessUnsupported = refl

record ZeroDistanceEqualityVariables
    {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    zeroDistanceLeft : S
    zeroDistanceRight : S
    zeroDistanceProof :
      UMetric.Ultrametric.d U zeroDistanceLeft zeroDistanceRight ≡ zero
    zeroDistanceEquality :
      zeroDistanceLeft ≡ zeroDistanceRight

ZeroDistanceEqualityLaw :
  ∀ {S : Set} (U : UMetric.Ultrametric S) → Set
ZeroDistanceEqualityLaw {S} U =
  ∀ {x y : S} →
  UMetric.Ultrametric.d U x y ≡ zero →
  x ≡ y

record CauchyStabilizesAtThresholdOne
    {S : Set} (U : UMetric.Ultrametric S)
    (c : CU.Cauchy U) : Set₁ where
  field
    threshold : Nat
    thresholdIsOne : threshold ≡ one
    thresholdPositive : zero < threshold

    stabilizationIndex : Nat
    stabilizationIndexIsCauchyOne :
      stabilizationIndex ≡ proj₁ (CU.Cauchy.cauchy c one onePositive)

    limitCandidate : S
    limitCandidateIsSeqAtIndex :
      limitCandidate ≡ CU.Cauchy.seq c stabilizationIndex

    stabilizedAtThresholdOne :
      ∀ m n →
      stabilizationIndex ≤ m →
      stabilizationIndex ≤ n →
      UMetric.Ultrametric.d U
        (CU.Cauchy.seq c m)
        (CU.Cauchy.seq c n)
      < one

    stabilizedDistanceToLimitAtOne :
      ∀ n →
      stabilizationIndex ≤ n →
      UMetric.Ultrametric.d U (CU.Cauchy.seq c n) limitCandidate < one

    stabilizedDistanceToLimitIsZero :
      ∀ n →
      stabilizationIndex ≤ n →
      UMetric.Ultrametric.d U (CU.Cauchy.seq c n) limitCandidate ≡ zero

canonicalCauchyStabilizesAtThresholdOne :
  ∀ {S : Set} (U : UMetric.Ultrametric S) →
  (c : CU.Cauchy U) →
  CauchyStabilizesAtThresholdOne U c
canonicalCauchyStabilizesAtThresholdOne U c =
  let
    N = proj₁ (CU.Cauchy.cauchy c one onePositive)
    cauchy1 = proj₂ (CU.Cauchy.cauchy c one onePositive)
    seqN = CU.Cauchy.seq c N

    toLimit<one :
      ∀ n →
      N ≤ n →
      UMetric.Ultrametric.d U (CU.Cauchy.seq c n) seqN < one
    toLimit<one n N≤n =
      subst (λ t → t < one)
        (UMetric.Ultrametric.symmetric U
          (CU.Cauchy.seq c N)
          (CU.Cauchy.seq c n))
        (cauchy1 N n NatP.≤-refl N≤n)
  in
  record
    { threshold = one
    ; thresholdIsOne = refl
    ; thresholdPositive = onePositive
    ; stabilizationIndex = N
    ; stabilizationIndexIsCauchyOne = refl
    ; limitCandidate = seqN
    ; limitCandidateIsSeqAtIndex = refl
    ; stabilizedAtThresholdOne =
        λ m n N≤m N≤n → cauchy1 m n N≤m N≤n
    ; stabilizedDistanceToLimitAtOne = toLimit<one
    ; stabilizedDistanceToLimitIsZero =
        λ n N≤n → NatP.n<1⇒n≡0 (toLimit<one n N≤n)
    }

record NatToNonNatCompletenessOrder
    {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    sourceUltrametric : UMetric.Ultrametric S
    sourceUltrametricIsInput : sourceUltrametric ≡ U

    sourceCompletenessLayer : CompletenessLayer
    sourceCompletenessLayerIsNatDiscrete :
      sourceCompletenessLayer ≡ natDiscrete

    natCompletenessProof : CU.Complete sourceUltrametric
    natCompletenessProofIsCompleteNatUltrametric :
      natCompletenessProof ≡ CUN.completeNatUltrametric sourceUltrametric

    qqPromotionTarget : CompletenessLayer
    qqPromotionTargetIsQQ : qqPromotionTarget ≡ qqCarrier
    qqPromotionPredecessor : CompletenessLayer
    qqPromotionPredecessorIsNatDiscrete :
      qqPromotionPredecessor ≡ natDiscrete
    qqPromotionBlocker : Bool
    qqPromotionBlockerIsUnsupported :
      qqPromotionBlocker ≡ layerCompletenessSupported qqCarrier
    qqPromotionBlockerIsFalse : qqPromotionBlocker ≡ false

    noPromotionTarget : CompletenessLayer
    noPromotionTargetIsNo : noPromotionTarget ≡ noCarrier
    noPromotionPredecessor : CompletenessLayer
    noPromotionPredecessorIsNatDiscrete :
      noPromotionPredecessor ≡ natDiscrete
    noPromotionBlocker : Bool
    noPromotionBlockerIsUnsupported :
      noPromotionBlocker ≡ layerCompletenessSupported noCarrier
    noPromotionBlockerIsFalse : noPromotionBlocker ≡ false

    surrealPromotionTarget : CompletenessLayer
    surrealPromotionTargetIsSurreal :
      surrealPromotionTarget ≡ surrealCarrier
    surrealPromotionPredecessor : CompletenessLayer
    surrealPromotionPredecessorIsNatDiscrete :
      surrealPromotionPredecessor ≡ natDiscrete
    surrealPromotionBlocker : Bool
    surrealPromotionBlockerIsUnsupported :
      surrealPromotionBlocker ≡ layerCompletenessSupported surrealCarrier
    surrealPromotionBlockerIsFalse : surrealPromotionBlocker ≡ false

    hilbertPromotionTarget : CompletenessLayer
    hilbertPromotionTargetIsHilbert :
      hilbertPromotionTarget ≡ hilbertCarrier
    hilbertPromotionPredecessor : CompletenessLayer
    hilbertPromotionPredecessorIsNatDiscrete :
      hilbertPromotionPredecessor ≡ natDiscrete
    hilbertPromotionBlocker : Bool
    hilbertPromotionBlockerIsUnsupported :
      hilbertPromotionBlocker ≡ layerCompletenessSupported hilbertCarrier
    hilbertPromotionBlockerIsFalse : hilbertPromotionBlocker ≡ false

canonicalNatToNonNatCompletenessOrder :
  ∀ {S : Set} (U : UMetric.Ultrametric S) →
  NatToNonNatCompletenessOrder U
canonicalNatToNonNatCompletenessOrder U =
  record
    { sourceUltrametric = U
    ; sourceUltrametricIsInput = refl
    ; sourceCompletenessLayer = natDiscrete
    ; sourceCompletenessLayerIsNatDiscrete = refl
    ; natCompletenessProof = CUN.completeNatUltrametric U
    ; natCompletenessProofIsCompleteNatUltrametric = refl
    ; qqPromotionTarget = qqCarrier
    ; qqPromotionTargetIsQQ = refl
    ; qqPromotionPredecessor = natDiscrete
    ; qqPromotionPredecessorIsNatDiscrete = refl
    ; qqPromotionBlocker = false
    ; qqPromotionBlockerIsUnsupported = refl
    ; qqPromotionBlockerIsFalse = refl
    ; noPromotionTarget = noCarrier
    ; noPromotionTargetIsNo = refl
    ; noPromotionPredecessor = natDiscrete
    ; noPromotionPredecessorIsNatDiscrete = refl
    ; noPromotionBlocker = false
    ; noPromotionBlockerIsUnsupported = refl
    ; noPromotionBlockerIsFalse = refl
    ; surrealPromotionTarget = surrealCarrier
    ; surrealPromotionTargetIsSurreal = refl
    ; surrealPromotionPredecessor = natDiscrete
    ; surrealPromotionPredecessorIsNatDiscrete = refl
    ; surrealPromotionBlocker = false
    ; surrealPromotionBlockerIsUnsupported = refl
    ; surrealPromotionBlockerIsFalse = refl
    ; hilbertPromotionTarget = hilbertCarrier
    ; hilbertPromotionTargetIsHilbert = refl
    ; hilbertPromotionPredecessor = natDiscrete
    ; hilbertPromotionPredecessorIsNatDiscrete = refl
    ; hilbertPromotionBlocker = false
    ; hilbertPromotionBlockerIsUnsupported = refl
    ; hilbertPromotionBlockerIsFalse = refl
    }

record NatUltrametricCompletenessBridge
    {S : Set} (U : UMetric.Ultrametric S) : Set₁ where
  field
    dependencyOrder : NatToNonNatCompletenessOrder U

    discreteLayerComplete : CU.Complete U
    discreteLayerCompleteIsLoadBearing :
      discreteLayerComplete ≡ CUN.completeNatUltrametric U

    cauchyStabilizationReceipt :
      (c : CU.Cauchy U) → CauchyStabilizesAtThresholdOne U c

    zeroDistanceEqualityRequired :
      Set
    zeroDistanceEqualityRequiredIsLaw :
      zeroDistanceEqualityRequired ≡ ZeroDistanceEqualityLaw U

    qqCompletenessPromoted : Bool
    qqCompletenessPromotedIsFalse : qqCompletenessPromoted ≡ false

    noCompletenessPromoted : Bool
    noCompletenessPromotedIsFalse : noCompletenessPromoted ≡ false

    surrealCompletenessPromoted : Bool
    surrealCompletenessPromotedIsFalse : surrealCompletenessPromoted ≡ false

    hilbertCompletenessPromoted : Bool
    hilbertCompletenessPromotedIsFalse : hilbertCompletenessPromoted ≡ false

canonicalNatUltrametricCompletenessBridge :
  ∀ {S : Set} (U : UMetric.Ultrametric S) →
  NatUltrametricCompletenessBridge U
canonicalNatUltrametricCompletenessBridge U =
  record
    { dependencyOrder = canonicalNatToNonNatCompletenessOrder U
    ; discreteLayerComplete = CUN.completeNatUltrametric U
    ; discreteLayerCompleteIsLoadBearing = refl
    ; cauchyStabilizationReceipt =
        canonicalCauchyStabilizesAtThresholdOne U
    ; zeroDistanceEqualityRequired = ZeroDistanceEqualityLaw U
    ; zeroDistanceEqualityRequiredIsLaw = refl
    ; qqCompletenessPromoted = false
    ; qqCompletenessPromotedIsFalse = refl
    ; noCompletenessPromoted = false
    ; noCompletenessPromotedIsFalse = refl
    ; surrealCompletenessPromoted = false
    ; surrealCompletenessPromotedIsFalse = refl
    ; hilbertCompletenessPromoted = false
    ; hilbertCompletenessPromotedIsFalse = refl
    }

natDiscreteCompleteness :
  ∀ {S : Set} (U : UMetric.Ultrametric S) → CU.Complete U
natDiscreteCompleteness U =
  NatUltrametricCompletenessBridge.discreteLayerComplete
    (canonicalNatUltrametricCompletenessBridge U)
