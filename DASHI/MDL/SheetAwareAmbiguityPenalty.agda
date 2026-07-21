module DASHI.MDL.SheetAwareAmbiguityPenalty where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- MDL accounting must charge for unresolved source identity, not only for
-- visible reconstruction error.

record ReconstructionScore : Set where
  constructor reconstructionScore
  field
    modelDescriptionCost : Nat
    residualDescriptionCost : Nat
    unresolvedSheetCost : Nat

open ReconstructionScore public

totalCost : ReconstructionScore → Nat
totalCost score =
  modelDescriptionCost score +
  residualDescriptionCost score +
  unresolvedSheetCost score

record ReconstructionModel : Set where
  constructor reconstructionModel
  field
    modelName : String
    score : ReconstructionScore
    storesSheetLabel : Bool
    preservesDisplayedSourceIdentity : Bool

open ReconstructionModel public

-- A deliberately small exact comparison for the displayed three-point fibre.
-- The one-sheet model is syntactically cheaper but leaves two unresolved source
-- alternatives.  The sheet-aware model spends one extra unit on the model and
-- eliminates the ambiguity penalty.
oneSheetScore : ReconstructionScore
oneSheetScore = reconstructionScore 1 0 2

threeSheetScore : ReconstructionScore
threeSheetScore = reconstructionScore 2 0 0

oneSheetTotal : totalCost oneSheetScore ≡ 3
oneSheetTotal = refl

threeSheetTotal : totalCost threeSheetScore ≡ 2
threeSheetTotal = refl

oneSheetModel : ReconstructionModel
oneSheetModel =
  reconstructionModel
    "visible target only"
    oneSheetScore
    false
    false

threeSheetModel : ReconstructionModel
threeSheetModel =
  reconstructionModel
    "visible target plus balanced three-sheet label"
    threeSheetScore
    true
    true

record AmbiguityPenaltyPolicy : Set where
  constructor ambiguityPenaltyPolicy
  field
    chargeUnresolvedAlternatives : Nat → Nat
    zeroAlternativesCostZero : chargeUnresolvedAlternatives 0 ≡ 0
    interpretation : String

linearAmbiguityPenalty : AmbiguityPenaltyPolicy
linearAmbiguityPenalty =
  ambiguityPenaltyPolicy
    (λ alternatives → alternatives)
    refl
    "each unresolved source alternative contributes one unit to the selected reference score"

record SheetAwareMDLReceipt : Set where
  constructor sheetAwareMDLReceipt
  field
    modelCostSeparatedFromResidual : Bool
    ambiguityCostSeparatedFromResidual : Bool
    oneSheetReferenceTotalChecked : Bool
    threeSheetReferenceTotalChecked : Bool
    simplerVisibleModelAlwaysPreferred : Bool
    simplerVisibleModelAlwaysPreferredIsFalse :
      simplerVisibleModelAlwaysPreferred ≡ false
    universalCostScaleClaimed : Bool
    universalCostScaleClaimedIsFalse : universalCostScaleClaimed ≡ false
    interpretation : String

sheetAwareMDLReceipt : SheetAwareMDLReceipt
sheetAwareMDLReceipt =
  sheetAwareMDLReceipt
    true true true true
    false refl
    false refl
    "the selected finite reference charges unresolved sheet identity separately; the numerical costs are a checked example, not a universal coding theorem"
