module DASHI.Physics.Closure.ZetaQ21MinusOneReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ZetaK21ComputationReceipt as ZetaK21

------------------------------------------------------------------------
-- Zeta_{Q(sqrt(21))}(-1) receipt.
--
-- This is a narrow wrapper around the existing finite Dirichlet/Bernoulli
-- computation receipt.  It records the exact value zeta_{Q(sqrt(21))}(-1)
-- = 1/3 from B_{2,chi21}=8 and keeps the result arithmetic-only.

data ZetaQ21MinusOneStatus : Set where
  zetaQ21MinusOneExactArithmeticDiagnostic :
    ZetaQ21MinusOneStatus

data ZetaQ21MinusOneBlocker : Set where
  noHilbertVolumeExtractionFromThisValue :
    ZetaQ21MinusOneBlocker

  noDeg23ConstantExtractionFromThisValue :
    ZetaQ21MinusOneBlocker

  noPhysicalPromotionFromArithmeticDiagnostic :
    ZetaQ21MinusOneBlocker

canonicalZetaQ21MinusOneBlockers :
  List ZetaQ21MinusOneBlocker
canonicalZetaQ21MinusOneBlockers =
  noHilbertVolumeExtractionFromThisValue
  ∷ noDeg23ConstantExtractionFromThisValue
  ∷ noPhysicalPromotionFromArithmeticDiagnostic
  ∷ []

data ZetaQ21MinusOnePromotion : Set where

zetaQ21MinusOnePromotionImpossibleHere :
  ZetaQ21MinusOnePromotion →
  ⊥
zetaQ21MinusOnePromotionImpossibleHere ()

zetaQ21MinusOneFormulaLabel : String
zetaQ21MinusOneFormulaLabel =
  "zeta_{Q(sqrt(21))}(-1)=zeta(-1)*L(-1,chi21)=(-1/12)*(-4)=1/3"

record ZetaQ21MinusOneReceipt : Setω where
  field
    status :
      ZetaQ21MinusOneStatus

    zetaK21Computation :
      ZetaK21.ZetaK21ComputationReceipt

    zetaK21ComputationArithmeticComplete :
      ZetaK21.arithmeticDiagnosticComplete zetaK21Computation ≡ true

    b2Chi21 :
      Nat

    b2Chi21IsEight :
      b2Chi21 ≡ 8

    lMinusOneChi21Label :
      String

    lMinusOneChi21LabelIsCanonical :
      lMinusOneChi21Label ≡ "L(-1,chi21)=-4"

    zetaQ21MinusOneNumerator :
      Nat

    zetaQ21MinusOneNumeratorIsOne :
      zetaQ21MinusOneNumerator ≡ 1

    zetaQ21MinusOneDenominator :
      Nat

    zetaQ21MinusOneDenominatorIsThree :
      zetaQ21MinusOneDenominator ≡ 3

    zetaQ21MinusOneFormula :
      String

    zetaQ21MinusOneFormulaIsCanonical :
      zetaQ21MinusOneFormula ≡ zetaQ21MinusOneFormulaLabel

    arithmeticDiagnosticOnly :
      Bool

    arithmeticDiagnosticOnlyIsTrue :
      arithmeticDiagnosticOnly ≡ true

    hilbertVolumeDerived :
      Bool

    hilbertVolumeDerivedIsFalse :
      hilbertVolumeDerived ≡ false

    physicalPromotionConstructed :
      Bool

    physicalPromotionConstructedIsFalse :
      physicalPromotionConstructed ≡ false

    blockers :
      List ZetaQ21MinusOneBlocker

    blockersAreCanonical :
      blockers ≡ canonicalZetaQ21MinusOneBlockers

    promotionFlags :
      List ZetaQ21MinusOnePromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open ZetaQ21MinusOneReceipt public

canonicalZetaQ21MinusOneReceipt :
  ZetaQ21MinusOneReceipt
canonicalZetaQ21MinusOneReceipt =
  record
    { status =
        zetaQ21MinusOneExactArithmeticDiagnostic
    ; zetaK21Computation =
        ZetaK21.canonicalZetaK21ComputationReceipt
    ; zetaK21ComputationArithmeticComplete =
        refl
    ; b2Chi21 =
        8
    ; b2Chi21IsEight =
        refl
    ; lMinusOneChi21Label =
        "L(-1,chi21)=-4"
    ; lMinusOneChi21LabelIsCanonical =
        refl
    ; zetaQ21MinusOneNumerator =
        1
    ; zetaQ21MinusOneNumeratorIsOne =
        refl
    ; zetaQ21MinusOneDenominator =
        3
    ; zetaQ21MinusOneDenominatorIsThree =
        refl
    ; zetaQ21MinusOneFormula =
        zetaQ21MinusOneFormulaLabel
    ; zetaQ21MinusOneFormulaIsCanonical =
        refl
    ; arithmeticDiagnosticOnly =
        true
    ; arithmeticDiagnosticOnlyIsTrue =
        refl
    ; hilbertVolumeDerived =
        false
    ; hilbertVolumeDerivedIsFalse =
        refl
    ; physicalPromotionConstructed =
        false
    ; physicalPromotionConstructedIsFalse =
        refl
    ; blockers =
        canonicalZetaQ21MinusOneBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "The exact arithmetic value zeta_{Q(sqrt(21))}(-1)=1/3 is recorded from B_{2,chi21}=8"
        ∷ "This wrapper consumes ZetaK21ComputationReceipt rather than recomputing a parent surface"
        ∷ "No Hilbert volume, deg23, or physical promotion is derived here"
        ∷ []
    }

zetaQ21MinusOneIsOneThird :
  zetaQ21MinusOneDenominator canonicalZetaQ21MinusOneReceipt ≡ 3
zetaQ21MinusOneIsOneThird =
  refl

zetaQ21MinusOneNoPhysicalPromotion :
  physicalPromotionConstructed canonicalZetaQ21MinusOneReceipt ≡ false
zetaQ21MinusOneNoPhysicalPromotion =
  refl
