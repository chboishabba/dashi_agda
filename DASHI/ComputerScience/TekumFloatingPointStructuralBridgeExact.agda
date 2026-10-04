module DASHI.ComputerScience.TekumFloatingPointStructuralBridgeExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

import DASHI.Foundations.BinaryFloatingPoint as Binary
import DASHI.Foundations.RadixScaledExactFormat as Generic
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime

tekumScaledExactFormat : Generic.ScaledExactFormat
tekumScaledExactFormat =
  Generic.scaledExactFormat
    Generic.radix3
    Binary.orientationRole
    Binary.scaleTransportRole
    Binary.localRefinementRole

tekumOrientationRoleMatchesBF16SignRole :
  Generic.orientationRole tekumScaledExactFormat
  ≡ Binary.bf16SignRole
tekumOrientationRoleMatchesBF16SignRole = refl

tekumScaleRoleMatchesBF16ExponentRole :
  Generic.scaleRole tekumScaledExactFormat
  ≡ Binary.bf16ExponentRole
tekumScaleRoleMatchesBF16ExponentRole = refl

tekumRefinementRoleMatchesBF16FractionRole :
  Generic.refinementRole tekumScaledExactFormat
  ≡ Binary.bf16FractionRole
tekumRefinementRoleMatchesBF16FractionRole = refl

-- A Tekum width n devotes three trits to regime.  The remaining n-3 payload
-- is allocated between explicit exponent and fraction by the regime.
record TekumPayloadAllocation (n : Nat) : Set where
  constructor tekumPayloadAllocation
  field
    regime : Regime.RegimeCode
    payloadWidth : Nat
    payloadWidthIsNMinusRegime : payloadWidth + 3 ≡ n
    exponentWidth : Nat
    fractionWidth : Nat
    exponentWidthIsRegimeDriven :
      exponentWidth ≡ Regime.exponentCount regime
    payloadConserved :
      exponentWidth + fractionWidth ≡ payloadWidth
open TekumPayloadAllocation public

record FloatTekumStructuralComparison : Set where
  constructor floatTekumStructuralComparison
  field
    bf16UsesOrientationRole : Bool
    tekumUsesOrientationRole : Bool
    bf16UsesScaleTransportRole : Bool
    tekumRegimeExponentUseScaleTransportRole : Bool
    bf16UsesLocalRefinementRole : Bool
    tekumFractionUsesLocalRefinementRole : Bool
    bf16WidthAllocationFixed : Bool
    tekumWidthAllocationRegimeDependent : Bool

canonicalFloatTekumStructuralComparison : FloatTekumStructuralComparison
canonicalFloatTekumStructuralComparison =
  floatTekumStructuralComparison
    true true true true true true true true

centralRegimeAtWidth8 :
  TekumPayloadAllocation 8
centralRegimeAtWidth8 =
  tekumPayloadAllocation
    Regime.r0
    5
    refl
    0
    5
    refl
    refl

outerRegimeAtWidth8 :
  TekumPayloadAllocation 8
outerRegimeAtWidth8 =
  tekumPayloadAllocation
    Regime.rp7
    5
    refl
    5
    0
    refl
    refl

centralRegimeGivesAllFivePayloadTritsToFraction :
  fractionWidth centralRegimeAtWidth8 ≡ 5
centralRegimeGivesAllFivePayloadTritsToFraction = refl

outerRegimeGivesAllFivePayloadTritsToExponent :
  exponentWidth outerRegimeAtWidth8 ≡ 5
outerRegimeGivesAllFivePayloadTritsToExponent = refl

centralAndOuterHaveSamePayloadWidth :
  payloadWidth centralRegimeAtWidth8
  ≡ payloadWidth outerRegimeAtWidth8
centralAndOuterHaveSamePayloadWidth = refl
