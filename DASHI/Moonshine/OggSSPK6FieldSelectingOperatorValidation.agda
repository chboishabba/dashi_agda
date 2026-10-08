module DASHI.Moonshine.OggSSPK6FieldSelectingOperatorValidation where

------------------------------------------------------------------------
-- RED-FIRST validation surface for the post-no-go K6 field selector.
--
-- The production owner must expose one independently sourced F3-linear
-- endomorphism of the existing X6 carrier, a literal witness that it breaks
-- the swap01 symmetry responsible for the current field non-canonicity, and a
-- degree-six/cyclic generator receipt.  Merely naming GF(729) is insufficient.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.OggSSPK6FieldSelectingOperatorExact as Target

validationRequiredMinimalPolynomialDegree :
  Target.minimalPolynomialDegree Target.canonicalAcquisitionTarget ≡ 6
validationRequiredMinimalPolynomialDegree = refl

validationRequiredCyclicSpanDimension :
  Target.cyclicSpanDimension Target.canonicalAcquisitionTarget ≡ 6
validationRequiredCyclicSpanDimension = refl

validationCurrentSourceLocatedIsFalse :
  Target.independentlyOwnedOperatorLocated Target.canonicalAcquisitionTarget ≡ false
validationCurrentSourceLocatedIsFalse = refl
