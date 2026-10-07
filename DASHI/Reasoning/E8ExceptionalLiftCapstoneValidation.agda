module DASHI.Reasoning.E8ExceptionalLiftCapstoneValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.E8ExceptionalLiftCapstoneExact as Lift

e6SectorPaid :
  Lift.e6SectorSameObjectActionReceiptTyped Lift.canonicalExceptionalLiftBoundary ≡ true
e6SectorPaid = refl

mixed27Typed :
  Lift.sixMixed27FibresTyped Lift.canonicalExceptionalLiftBoundary ≡ true
mixed27Typed = refl

mixed27TransitivityTyped :
  Lift.sixMixed27TransitivityReceiptsTyped Lift.canonicalExceptionalLiftBoundary ≡ true
mixed27TransitivityTyped = refl

schlafliTyped :
  Lift.schlafli27RecognitionReceiptTyped Lift.canonicalExceptionalLiftBoundary ≡ true
schlafliTyped = refl

fullTernary240NotPromoted :
  Lift.fullTernary240SameActionRecognitionPaid Lift.canonicalExceptionalLiftBoundary ≡ false
fullTernary240NotPromoted = refl

albert27NotPromoted :
  Lift.albert27SameActionRecognitionPaid Lift.canonicalExceptionalLiftBoundary ≡ false
albert27NotPromoted = refl
