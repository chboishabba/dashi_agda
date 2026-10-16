module DASHI.Biology.SignedSSPWeaveRefineAt369FixedDepthNoGoValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.SignedSSPWeaveRefineAt369FixedDepthNoGoExact as Cut

_ : Cut.currentRichAddressHasFixedDepthThree Cut.canonicalBoundary ≡ true
_ = refl

_ : Cut.everyCurrentAddressStepPreservesDepth Cut.canonicalBoundary ≡ true
_ = refl

_ : Cut.currentRefineInstructionCarriesChildChoice Cut.canonicalBoundary ≡ false
_ = refl

_ : Cut.literalDepthRefinementExpressibleByCurrentStepType Cut.canonicalBoundary ≡ false
_ = refl

_ : Cut.variableDepthAddressRepairConstructed Cut.canonicalBoundary ≡ true
_ = refl

_ : Cut.explicitThreeWayChildChoiceTyped Cut.canonicalBoundary ≡ true
_ = refl

_ : Cut.childChoiceChangesRefinedAddress Cut.canonicalBoundary ≡ true
_ = refl

_ : Cut.variableDepthRepairMigratedIntoRichCompiler Cut.canonicalBoundary ≡ false
_ = refl

_ : Cut.sourceSemanticsSelectsChildHere Cut.canonicalBoundary ≡ false
_ = refl
