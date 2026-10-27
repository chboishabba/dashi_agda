module DASHI.Unified.GrapheneTOERootDirectValidation where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.EverythingTOESymmetryResolved369 as TOE
import DASHI.Unifier as Unifier
import DASHI.Unified.GraphenePhysicalNonPromotionTOEExact as Source

-- Validate direct proof consumption from both canonical TOE roots.
toeQTM : Source.syntheticQTMCountsAsMeasuredFit ≡ false
toeQTM = TOE.toeSyntheticQTMIsNotMeasured
unifierQTM : Source.syntheticQTMCountsAsMeasuredFit ≡ false
unifierQTM = Unifier.toeSyntheticQTMIsNotMeasured

toeEntropy : Source.syntheticMaxwellCountsAsMeasuredEntropy ≡ false
toeEntropy = TOE.toeSyntheticEntropyIsNotMeasured
unifierEntropy : Source.syntheticMaxwellCountsAsMeasuredEntropy ≡ false
unifierEntropy = Unifier.toeSyntheticEntropyIsNotMeasured

toeWEC : Source.positiveEulerianCountsAsFullWEC ≡ false
toeWEC = TOE.toePositiveEulerianIsNotFullWEC
unifierWEC : Source.positiveEulerianCountsAsFullWEC ≡ false
unifierWEC = Unifier.toePositiveEulerianIsNotFullWEC
