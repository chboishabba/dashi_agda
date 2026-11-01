module DASHI.Foundations.Base369CirclePhaseRegression where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Base369 using (TriTruth; tri-low; tri-mid; tri-high)
open import DASHI.Foundations.Base369CirclePhase

------------------------------------------------------------------------
-- Compact import/check surface for the generated-expression and circle-
-- refinement tranche.

fortyFiveGenerated : eval369 fortyFiveExpr ≡ 45
fortyFiveGenerated = fortyFiveExpr-value

allExpressionsStayOnThreeLattice :
  (e : Expr369) →
  MultipleOfThree (eval369 e)
allExpressionsStayOnThreeLattice = eval369-is-multiple-of-three

triLowCommonRefinement :
  hexTo18 (triToHex tri-low) ≡ nonaryTo18 (triToNonary tri-low)
triLowCommonRefinement = tri-common-refinement-commutes tri-low

triMidCommonRefinement :
  hexTo18 (triToHex tri-mid) ≡ nonaryTo18 (triToNonary tri-mid)
triMidCommonRefinement = tri-common-refinement-commutes tri-mid

triHighCommonRefinement :
  hexTo18 (triToHex tri-high) ≡ nonaryTo18 (triToNonary tri-high)
triHighCommonRefinement = tri-common-refinement-commutes tri-high

record Base369CirclePhaseReceipt : Set where
  field
    expression45Checks :
      eval369 fortyFiveExpr ≡ 45

    generatedCarrierClosedOnThreeLattice :
      (e : Expr369) →
      MultipleOfThree (eval369 e)

    sixNineHaveCommonTriadicRefinement :
      (t : TriTruth) →
      hexTo18 (triToHex t) ≡ nonaryTo18 (triToNonary t)

base369CirclePhaseReceipt : Base369CirclePhaseReceipt
base369CirclePhaseReceipt =
  record
    { expression45Checks = fortyFiveExpr-value
    ; generatedCarrierClosedOnThreeLattice = eval369-is-multiple-of-three
    ; sixNineHaveCommonTriadicRefinement = tri-common-refinement-commutes
    }
