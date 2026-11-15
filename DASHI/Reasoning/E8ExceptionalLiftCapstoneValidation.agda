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

minusculeSameObjectTyped :
  Lift.minuscule27SameObjectReceiptTyped Lift.canonicalExceptionalLiftBoundary ≡ true
minusculeSameObjectTyped = refl

minusculeActionIntertwinerTyped :
  Lift.minuscule27ActionIntertwinerReceiptTyped Lift.canonicalExceptionalLiftBoundary ≡ true
minusculeActionIntertwinerTyped = refl

minusculeRelationIntertwinerTyped :
  Lift.minuscule27RelationIntertwinerReceiptTyped Lift.canonicalExceptionalLiftBoundary ≡ true
minusculeRelationIntertwinerTyped = refl

typedTernaryChartPaid :
  Lift.typedTernary27SixPlusFifteenPlusSixChartPaidInAgda Lift.canonicalExceptionalLiftBoundary ≡ true
typedTernaryChartPaid = refl

typedTernarySchlafliProducerRecorded :
  Lift.typedTernary27SchlafliLeanProducerSourceWritten Lift.canonicalExceptionalLiftBoundary ≡ true
typedTernarySchlafliProducerRecorded = refl

typedTernaryMinusculeProducerRecorded :
  Lift.typedTernary27MinusculeRelationLeanProducerSourceWritten Lift.canonicalExceptionalLiftBoundary ≡ true
typedTernaryMinusculeProducerRecorded = refl

a5SixObjectProducerRecorded :
  Lift.a5SixObjectS6LeanProducerSourceWritten Lift.canonicalExceptionalLiftBoundary ≡ true
a5SixObjectProducerRecorded = refl

rawTernaryE6ActionNotInvented :
  Lift.independentRawTernary27E6ActionPaid Lift.canonicalExceptionalLiftBoundary ≡ false
rawTernaryE6ActionNotInvented = refl

selectedStabilizerWeldNotInvented :
  Lift.selectedQ2StabilizerA5SameObjectPaid Lift.canonicalExceptionalLiftBoundary ≡ false
selectedStabilizerWeldNotInvented = refl

leanMinusculeProducerSourceWritten :
  Lift.leanMinuscule27ProducerSourceWritten Lift.canonicalExceptionalLiftBoundary ≡ true
leanMinusculeProducerSourceWritten = refl

agdaMinusculeKernelNotManufactured :
  Lift.agdaMinuscule27SameObjectKernelPaidHere Lift.canonicalExceptionalLiftBoundary ≡ false
agdaMinusculeKernelNotManufactured = refl

fullTernary240NotPromoted :
  Lift.fullTernary240SameActionRecognitionPaid Lift.canonicalExceptionalLiftBoundary ≡ false
fullTernary240NotPromoted = refl

albertAlgebraNotPromoted :
  Lift.albert27AlgebraRecognitionPaid Lift.canonicalExceptionalLiftBoundary ≡ false
albertAlgebraNotPromoted = refl
