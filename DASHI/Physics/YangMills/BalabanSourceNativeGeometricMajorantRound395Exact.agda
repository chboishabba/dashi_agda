{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanSourceNativeGeometricMajorantRound395Exact where

------------------------------------------------------------------------
-- ROUND395 / SOURCE-NATIVE GEOMETRIC MAJORANT WITHOUT q <= 1/2
--
-- The historical `SourceExponentialShellMajorant` contains the useful theorem
--
--     shellValue(d) <= A * q^d
--
-- but packages it together with the stronger dyadic-normalization condition
-- `q <= 1/2`.  R387 proves the spectral consumer does not require that
-- strengthening.  This owner therefore exposes the exact consumer-facing
-- geometric majorant separately.
--
-- The historical dyadic record still compiles into this carrier, so no old
-- proof is discarded; it is simply no longer the mandatory source ABI.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong; subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteInfluenceRowMassPowerExact as Power
import DASHI.Physics.YangMills.BalabanExponentialToDyadicShellCoarseningExact as Dyadic

record SourceNativeGeometricMajorant : Set₁ where
  field
    shellValue : Nat → ℚ
    amplitude ratio : ℚ
    amplitudeNonnegative : 0ℚ ≤ amplitude
    ratioNonnegative : 0ℚ ≤ ratio

    sourceNativeGeometricBound : ∀ depth →
      shellValue depth ≤ amplitude * Power.rationalPower ratio depth

open SourceNativeGeometricMajorant public

-- The two historical rational-power implementations have the same recursion.
-- This lemma is representation transport only; it adds no analytic estimate.
dyadicPowerIsPower : ∀ base depth →
  Dyadic.rationalPower base depth ≡ Power.rationalPower base depth
dyadicPowerIsPower base zero = refl
dyadicPowerIsPower base (suc depth) =
  cong (λ value → value * base) (dyadicPowerIsPower base depth)

fromDyadicMajorant :
  Dyadic.SourceExponentialShellMajorant → SourceNativeGeometricMajorant
fromDyadicMajorant dataSet = record
  { shellValue = Dyadic.shellValue dataSet
  ; amplitude = Dyadic.amplitude dataSet
  ; ratio = Dyadic.sourcePerShellDecay (Dyadic.criterion dataSet)
  ; amplitudeNonnegative = Dyadic.amplitudeNonnegative dataSet
  ; ratioNonnegative = Dyadic.sourceDecayNonnegative (Dyadic.criterion dataSet)
  ; sourceNativeGeometricBound = λ depth →
      subst
        (λ power →
          Dyadic.shellValue dataSet depth
          ≤ Dyadic.amplitude dataSet * power)
        (dyadicPowerIsPower
          (Dyadic.sourcePerShellDecay (Dyadic.criterion dataSet)) depth)
        (Dyadic.sourceExponentialShellBound dataSet depth)
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round395SourceNativeMajorantCompilerLevel : ProofLevel
round395SourceNativeMajorantCompilerLevel = machineChecked

fastRatioAtMostHalfRequired : Bool
fastRatioAtMostHalfRequired = false

fastRatioAtMostHalfRequiredIsFalse :
  fastRatioAtMostHalfRequired ≡ false
fastRatioAtMostHalfRequiredIsFalse = refl

dyadicMajorantStillOptionalProducer : Bool
dyadicMajorantStillOptionalProducer = true

dyadicMajorantStillOptionalProducerIsTrue :
  dyadicMajorantStillOptionalProducer ≡ true
dyadicMajorantStillOptionalProducerIsTrue = refl

sourceNativeGeometricBoundIsPrimitiveInterface : Bool
sourceNativeGeometricBoundIsPrimitiveInterface = true

sourceNativeGeometricBoundIsPrimitiveInterfaceIsTrue :
  sourceNativeGeometricBoundIsPrimitiveInterface ≡ true
sourceNativeGeometricBoundIsPrimitiveInterfaceIsTrue = refl

dyadicNormalizationIsMandatoryArchitecture : Bool
dyadicNormalizationIsMandatoryArchitecture = false

dyadicNormalizationIsMandatoryArchitectureIsFalse :
  dyadicNormalizationIsMandatoryArchitecture ≡ false
dyadicNormalizationIsMandatoryArchitectureIsFalse = refl

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
