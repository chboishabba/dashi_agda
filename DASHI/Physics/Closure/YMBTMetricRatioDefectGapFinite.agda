module DASHI.Physics.Closure.YMBTMetricRatioDefectGapFinite where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])
open import Agda.Builtin.Nat using (Nat; _*_; _-_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Finite YM/BT metric-ratio defect gap surface.
--
-- This module records only the finite sample p = 2, 3, 5.  The defect
-- coefficient is kappa_p = (p - 1)^2 / p^2, stored as a natural numerator
-- and denominator pair.  The two-depth check below is definitionally
-- depth-independent for this finite sample.  No continuum mass gap, Hodge
-- variation closure, or Clay Yang-Mills promotion is claimed here.

modulePath : String
modulePath =
  "DASHI/Physics/Closure/YMBTMetricRatioDefectGapFinite.agda"

surfaceName : String
surfaceName =
  "Finite YM/BT metric-ratio defect gap sample"

finiteBTGapRecorded : Bool
finiteBTGapRecorded = true

infDepthUniformForFiniteSample : Bool
infDepthUniformForFiniteSample = true

strictSelectedHodgeVariationPairingClosed : Bool
strictSelectedHodgeVariationPairingClosed = false

continuumMassGapPromoted : Bool
continuumMassGapPromoted = false

clayYangMillsPromoted : Bool
clayYangMillsPromoted = false

finiteBTGapRecordedIsTrue :
  finiteBTGapRecorded ≡ true
finiteBTGapRecordedIsTrue = refl

infDepthUniformForFiniteSampleIsTrue :
  infDepthUniformForFiniteSample ≡ true
infDepthUniformForFiniteSampleIsTrue = refl

strictSelectedHodgeVariationPairingClosedIsFalse :
  strictSelectedHodgeVariationPairingClosed ≡ false
strictSelectedHodgeVariationPairingClosedIsFalse = refl

continuumMassGapPromotedIsFalse :
  continuumMassGapPromoted ≡ false
continuumMassGapPromotedIsFalse = refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse = refl

data PrimeSample : Set where
  p2 :
    PrimeSample
  p3 :
    PrimeSample
  p5 :
    PrimeSample

canonicalPrimeSamples : List PrimeSample
canonicalPrimeSamples =
  p2
  ∷ p3
  ∷ p5
  ∷ []

primeNat : PrimeSample → Nat
primeNat p2 = 2
primeNat p3 = 3
primeNat p5 = 5

record NatRatio : Set where
  constructor mkNatRatio
  field
    numerator :
      Nat
    denominator :
      Nat

open NatRatio public

kappaFormulaNumerator : PrimeSample → Nat
kappaFormulaNumerator p =
  (primeNat p - 1) * (primeNat p - 1)

kappaFormulaDenominator : PrimeSample → Nat
kappaFormulaDenominator p =
  primeNat p * primeNat p

kappaRatio : PrimeSample → NatRatio
kappaRatio p =
  mkNatRatio (kappaFormulaNumerator p) (kappaFormulaDenominator p)

p2KappaRatio : NatRatio
p2KappaRatio = kappaRatio p2

p3KappaRatio : NatRatio
p3KappaRatio = kappaRatio p3

p5KappaRatio : NatRatio
p5KappaRatio = kappaRatio p5

p2KappaNumeratorIsOne :
  numerator p2KappaRatio ≡ 1
p2KappaNumeratorIsOne = refl

p2KappaDenominatorIsFour :
  denominator p2KappaRatio ≡ 4
p2KappaDenominatorIsFour = refl

p3KappaNumeratorIsFour :
  numerator p3KappaRatio ≡ 4
p3KappaNumeratorIsFour = refl

p3KappaDenominatorIsNine :
  denominator p3KappaRatio ≡ 9
p3KappaDenominatorIsNine = refl

p5KappaNumeratorIsSixteen :
  numerator p5KappaRatio ≡ 16
p5KappaNumeratorIsSixteen = refl

p5KappaDenominatorIsTwentyFive :
  denominator p5KappaRatio ≡ 25
p5KappaDenominatorIsTwentyFive = refl

numeratorPositive : PrimeSample → Bool
numeratorPositive p2 = true
numeratorPositive p3 = true
numeratorPositive p5 = true

p2NumeratorPositive :
  numeratorPositive p2 ≡ true
p2NumeratorPositive = refl

p3NumeratorPositive :
  numeratorPositive p3 ≡ true
p3NumeratorPositive = refl

p5NumeratorPositive :
  numeratorPositive p5 ≡ true
p5NumeratorPositive = refl

data SampleDepth : Set where
  depthZero :
    SampleDepth
  depthOne :
    SampleDepth

kappaAtDepth : PrimeSample → SampleDepth → NatRatio
kappaAtDepth p depthZero = kappaRatio p
kappaAtDepth p depthOne = kappaRatio p

p2DepthIndependent :
  kappaAtDepth p2 depthZero ≡ kappaAtDepth p2 depthOne
p2DepthIndependent = refl

p3DepthIndependent :
  kappaAtDepth p3 depthZero ≡ kappaAtDepth p3 depthOne
p3DepthIndependent = refl

p5DepthIndependent :
  kappaAtDepth p5 depthZero ≡ kappaAtDepth p5 depthOne
p5DepthIndependent = refl

record FinitePrimeKappaRow : Set where
  constructor mkFinitePrimeKappaRow
  field
    sample :
      PrimeSample
    pValue :
      Nat
    kappa :
      NatRatio
    kappaNumeratorFormula :
      numerator kappa ≡ (pValue - 1) * (pValue - 1)
    kappaDenominatorFormula :
      denominator kappa ≡ pValue * pValue
    numeratorIsPositive :
      numeratorPositive sample ≡ true
    depthZeroKappa :
      NatRatio
    depthOneKappa :
      NatRatio
    finiteDepthIndependence :
      depthZeroKappa ≡ depthOneKappa

p2KappaRow : FinitePrimeKappaRow
p2KappaRow =
  mkFinitePrimeKappaRow
    p2
    2
    p2KappaRatio
    refl
    refl
    refl
    (kappaAtDepth p2 depthZero)
    (kappaAtDepth p2 depthOne)
    refl

p3KappaRow : FinitePrimeKappaRow
p3KappaRow =
  mkFinitePrimeKappaRow
    p3
    3
    p3KappaRatio
    refl
    refl
    refl
    (kappaAtDepth p3 depthZero)
    (kappaAtDepth p3 depthOne)
    refl

p5KappaRow : FinitePrimeKappaRow
p5KappaRow =
  mkFinitePrimeKappaRow
    p5
    5
    p5KappaRatio
    refl
    refl
    refl
    (kappaAtDepth p5 depthZero)
    (kappaAtDepth p5 depthOne)
    refl

canonicalFinitePrimeKappaRows : List FinitePrimeKappaRow
canonicalFinitePrimeKappaRows =
  p2KappaRow
  ∷ p3KappaRow
  ∷ p5KappaRow
  ∷ []

record YMBTMetricRatioDefectGapFiniteReceipt : Set where
  constructor mkYMBTMetricRatioDefectGapFiniteReceipt
  field
    primes :
      List PrimeSample
    primesAreCanonical :
      primes ≡ canonicalPrimeSamples
    rows :
      List FinitePrimeKappaRow
    rowsAreCanonical :
      rows ≡ canonicalFinitePrimeKappaRows
    finiteBTGapRecordedFlag :
      Bool
    finiteBTGapRecordedFlagIsTrue :
      finiteBTGapRecordedFlag ≡ true
    infDepthUniformForFiniteSampleFlag :
      Bool
    infDepthUniformForFiniteSampleFlagIsTrue :
      infDepthUniformForFiniteSampleFlag ≡ true
    strictSelectedHodgeVariationPairingClosedFlag :
      Bool
    strictSelectedHodgeVariationPairingClosedFlagIsFalse :
      strictSelectedHodgeVariationPairingClosedFlag ≡ false
    continuumMassGapPromotedFlag :
      Bool
    continuumMassGapPromotedFlagIsFalse :
      continuumMassGapPromotedFlag ≡ false
    clayYangMillsPromotedFlag :
      Bool
    clayYangMillsPromotedFlagIsFalse :
      clayYangMillsPromotedFlag ≡ false

canonicalYMBTMetricRatioDefectGapFiniteReceipt :
  YMBTMetricRatioDefectGapFiniteReceipt
canonicalYMBTMetricRatioDefectGapFiniteReceipt =
  mkYMBTMetricRatioDefectGapFiniteReceipt
    canonicalPrimeSamples
    refl
    canonicalFinitePrimeKappaRows
    refl
    finiteBTGapRecorded
    refl
    infDepthUniformForFiniteSample
    refl
    strictSelectedHodgeVariationPairingClosed
    refl
    continuumMassGapPromoted
    refl
    clayYangMillsPromoted
    refl
