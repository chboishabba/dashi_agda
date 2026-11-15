module DASHI.Governance.SituatedCortisolScaleIndexedAssayExact where

-- DASHI mathematical owner: discrete scale-indexed assay operator.
-- Empirical methods: hair scalp growth ~1cm/month is ONLY approximate;
-- salivary/serum snapshots, 24h urine and hair segments are not
-- interchangeable units nor deterministic transforms of each other.
-- Physiology owners remain DASHI.Biology.StressPhysiologyCascadeExact
-- and DASHI.Biology.MultiscaleAllostaticBodyHyperformalismExact.
open import DASHI.Core.Prelude
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.SituatedCortisolTrajectoryAdmissionExact as Personal

data AssayScale : Set where
  pointWindow dailyWindow monthlySegmentWindow : AssayScale

data SampleSubstrate : AssayScale → Set where
  salivaSample : SampleSubstrate pointWindow
  serumSample : SampleSubstrate pointWindow
  urineCollection : SampleSubstrate dailyWindow
  scalpHairSegment : SampleSubstrate monthlySegmentWindow

data DiscreteTime : Set where
  instantA instantB : DiscreteTime

data WindowWeight : Set where
  noWeight included : WindowWeight

-- A source-specific filter kernel is needed; a merely named substrate
-- does not determine weighting, delay, washout, hair growth or assay error.
record ScaleKernel (scale : AssayScale) : Set₁ where
  constructor scale-kernel
  field
    weight : DiscreteTime → Nat
    temporalAlignmentReviewed : Set
    sampleProtocolReviewed : Set
    calibrationReviewed : Set

open ScaleKernel public

trajectory : Set
trajectory = DiscreteTime → Nat

applyKernel : ∀ {scale} → ScaleKernel scale → trajectory → Nat
applyKernel k x =
  weight k instantA * x instantA + weight k instantB * x instantB

-- Two time-localized trajectories can have the same long-window
-- integrated value; an acute point measurement is not recovered from
-- a temporal aggregate. Numbers are deliberately synthetic.
data History : Set where
  surgeEarly surgeLate : History

history : History → trajectory
history surgeEarly instantA = 2
history surgeEarly instantB = 0
history surgeLate instantA = 0
history surgeLate instantB = 2

twoPointIntegral : History → Nat
twoPointIntegral h = history h instantA + history h instantB

acutePoint : History → Nat
acutePoint h = history h instantA

sameIntegralDifferentAcutePoint :
  NF.NonFactorabilityWitness twoPointIntegral acutePoint
sameIntegralDifferentAcutePoint =
  NF.nonFactorabilityWitness surgeEarly surgeLate refl (λ ())

longWindowCannotIdentifyAcuteSurge :
  NF.FactorsThrough twoPointIntegral acutePoint → ⊥
longWindowCannotIdentifyAcuteSurge =
  NF.witnessRulesOutEveryFlatFactorisation
    sameIntegralDifferentAcutePoint

-- This only encodes a very small exact discrete integration example.
-- Saliva/serum/urine/hair represent different empirically calibrated
-- transfer functions; no direct universal coercion is provided.
salivaNotHair :
  pointWindow ≡ monthlySegmentWindow → ⊥
salivaNotHair ()

urineNotPoint :
  dailyWindow ≡ pointWindow → ⊥
urineNotPoint ()

record CrossScaleTransport
  (source target : AssayScale) : Set₁ where
  constructor cross-scale-transport
  field
    translate : ScaleKernel source → ScaleKernel target
    sourceAndTargetProtocolsAligned : Set
    temporalTransferEmpiricallyValidated : Set
    individualGrowthOrRecoveryLagReviewed : Set

-- An external receipt must inhabit the transport requirements;
-- this module constructs no hair-to-saliva inverse transfer.
