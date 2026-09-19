{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2D2TransportGeneratedRecurrenceValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayLevel2D2TransportGeneratedRecurrenceExact as Generated
import DASHI.Physics.YangMills.YMClayLevel2D2PhysicalMinCutExact as D2

physicalOneStepIsDefinitional :
  Generated.independentPhysicalOneStepRecurrenceProofRequired ≡ false
physicalOneStepIsDefinitional =
  Generated.independentPhysicalOneStepRecurrenceProofRequiredIsFalse

afOneStepIsDefinitional :
  Generated.independentAFOneStepRecurrenceProofRequired ≡ false
afOneStepIsDefinitional =
  Generated.independentAFOneStepRecurrenceProofRequiredIsFalse

commonUVNormalizationRemains :
  Generated.commonUVNormalizationStillPhysical ≡ true
commonUVNormalizationRemains =
  Generated.commonUVNormalizationStillPhysicalIsTrue

d2MinCutNoPhysicalOneStepLeaf :
  D2.independentPhysicalOneStepRecurrenceRequired ≡ false
d2MinCutNoPhysicalOneStepLeaf =
  D2.independentPhysicalOneStepRecurrenceRequiredIsFalse

d2MinCutNoAFOneStepLeaf :
  D2.independentAFOneStepRecurrenceRequired ≡ false
d2MinCutNoAFOneStepLeaf =
  D2.independentAFOneStepRecurrenceRequiredIsFalse
