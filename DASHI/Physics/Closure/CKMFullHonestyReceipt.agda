module DASHI.Physics.Closure.CKMFullHonestyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Paper 6 CKM full honesty receipt.
--
-- This receipt records the six-quantity CKM status without promoting the
-- carrier table to a physical CKM derivation.  Arithmetic rows are marked as
-- carrier arithmetic; alpha-product and unitarity-triangle rows retain their
-- leading-order/derived labels.

data CKMQuantity : Set where
  wolfensteinLambda :
    CKMQuantity

  vcbMagnitude :
    CKMQuantity

  vubMagnitude :
    CKMQuantity

  gammaAngle :
    CKMQuantity

  betaAngle :
    CKMQuantity

  alphaAngle :
    CKMQuantity

data CKMHonestStatus : Set where
  carrierArithmetic :
    CKMHonestStatus

  leadingOrderEstimate :
    CKMHonestStatus

  leadingOrderDerived :
    CKMHonestStatus

  derived :
    CKMHonestStatus

data CKMFullHonestyBlocker : Set where
  fullPhysicalCKMDiagonalisationNotCertified :
    CKMFullHonestyBlocker

  leadingOrderRowsRemainApproximate :
    CKMFullHonestyBlocker

  paper6RecordsCarrierStatusOnly :
    CKMFullHonestyBlocker

canonicalCKMFullHonestyBlockers :
  List CKMFullHonestyBlocker
canonicalCKMFullHonestyBlockers =
  fullPhysicalCKMDiagonalisationNotCertified
  ∷ leadingOrderRowsRemainApproximate
  ∷ paper6RecordsCarrierStatusOnly
  ∷ []

data CKMPhysicalPromotion : Set where

ckmPhysicalPromotionImpossibleHere :
  CKMPhysicalPromotion →
  ⊥
ckmPhysicalPromotionImpossibleHere ()

record CKMHonestQuantityRow : Set where
  field
    quantity :
      CKMQuantity

    formula :
      String

    relativeErrorPercent :
      Float

    status :
      CKMHonestStatus

    statusLabel :
      String

    rowBoundary :
      String

open CKMHonestQuantityRow public

lambdaFormulaLabel : String
lambdaFormulaLabel =
  "lambda = sqrt(m_d/m_s)"

vcbFormulaLabel : String
vcbFormulaLabel =
  "|Vcb| from isogeny"

vubFormulaLabel : String
vubFormulaLabel =
  "|Vub| = alpha1 * alpha2 with U_d approximately I"

gammaFormulaLabel : String
gammaFormulaLabel =
  "gamma = arctan(sqrt(7)) * (1 - alpha1)"

betaFormulaLabel : String
betaFormulaLabel =
  "beta = arctan(eta/(1-rho))"

alphaFormulaLabel : String
alphaFormulaLabel =
  "alpha = pi - beta - gamma"

carrierArithmeticLabel : String
carrierArithmeticLabel =
  "carrier-arithmetic"

leadingOrderEstimateLabel : String
leadingOrderEstimateLabel =
  "leading-order estimate"

leadingOrderDerivedLabel : String
leadingOrderDerivedLabel =
  "leading-order derived"

derivedLabel : String
derivedLabel =
  "derived"

lambdaHonestRow : CKMHonestQuantityRow
lambdaHonestRow =
  record
    { quantity =
        wolfensteinLambda
    ; formula =
        lambdaFormulaLabel
    ; relativeErrorPercent =
        0.9
    ; status =
        carrierArithmetic
    ; statusLabel =
        carrierArithmeticLabel
    ; rowBoundary =
        "Paper 6 records lambda from sqrt(md/ms) at 0.9 percent error as carrier arithmetic"
    }

vcbHonestRow : CKMHonestQuantityRow
vcbHonestRow =
  record
    { quantity =
        vcbMagnitude
    ; formula =
        vcbFormulaLabel
    ; relativeErrorPercent =
        0.0
    ; status =
        carrierArithmetic
    ; statusLabel =
        carrierArithmeticLabel
    ; rowBoundary =
        "Paper 6 records |Vcb| from isogeny at 0.0 percent error as carrier arithmetic"
    }

vubHonestRow : CKMHonestQuantityRow
vubHonestRow =
  record
    { quantity =
        vubMagnitude
    ; formula =
        vubFormulaLabel
    ; relativeErrorPercent =
        4.2
    ; status =
        leadingOrderEstimate
    ; statusLabel =
        leadingOrderEstimateLabel
    ; rowBoundary =
        "Paper 6 records |Vub| = alpha1*alpha2 with U_d approximately I at 4.2 percent error as a leading-order estimate"
    }

gammaHonestRow : CKMHonestQuantityRow
gammaHonestRow =
  record
    { quantity =
        gammaAngle
    ; formula =
        gammaFormulaLabel
    ; relativeErrorPercent =
        1.6
    ; status =
        carrierArithmetic
    ; statusLabel =
        carrierArithmeticLabel
    ; rowBoundary =
        "Paper 6 records gamma = arctan(sqrt7)*(1-alpha1) at 1.6 percent error as carrier arithmetic"
    }

betaHonestRow : CKMHonestQuantityRow
betaHonestRow =
  record
    { quantity =
        betaAngle
    ; formula =
        betaFormulaLabel
    ; relativeErrorPercent =
        6.0
    ; status =
        leadingOrderDerived
    ; statusLabel =
        leadingOrderDerivedLabel
    ; rowBoundary =
        "Paper 6 records beta = arctan(eta/(1-rho)) at 6.0 percent error as leading-order derived"
    }

alphaHonestRow : CKMHonestQuantityRow
alphaHonestRow =
  record
    { quantity =
        alphaAngle
    ; formula =
        alphaFormulaLabel
    ; relativeErrorPercent =
        0.3
    ; status =
        derived
    ; statusLabel =
        derivedLabel
    ; rowBoundary =
        "Paper 6 records alpha = pi - beta - gamma at 0.3 percent error as derived"
    }

canonicalCKMHonestRows :
  List CKMHonestQuantityRow
canonicalCKMHonestRows =
  lambdaHonestRow
  ∷ vcbHonestRow
  ∷ vubHonestRow
  ∷ gammaHonestRow
  ∷ betaHonestRow
  ∷ alphaHonestRow
  ∷ []

canonicalCKMFullHonestyBoundary :
  List String
canonicalCKMFullHonestyBoundary =
  "Six Paper 6 CKM quantities are recorded with formula, error, and honest status label"
  ∷ "lambda sqrt(md/ms): 0.9 percent, carrier-arithmetic"
  ∷ "|Vcb| isogeny: 0.0 percent, carrier-arithmetic"
  ∷ "|Vub| alpha1*alpha2 with U_d approximately I: 4.2 percent, leading-order estimate"
  ∷ "gamma arctan(sqrt7)*(1-alpha1): 1.6 percent, carrier-arithmetic"
  ∷ "beta arctan(eta/(1-rho)): 6.0 percent, leading-order derived"
  ∷ "alpha pi-beta-gamma: 0.3 percent, derived"
  ∷ "No quantity is overstated, and physical CKM promotion remains false"
  ∷ []

record CKMFullHonestyReceipt : Set where
  field
    rows :
      List CKMHonestQuantityRow

    rowsAreCanonical :
      rows ≡ canonicalCKMHonestRows

    rowCount :
      String

    rowCountIsSix :
      rowCount ≡ "six"

    paper :
      String

    paperIsPaper6 :
      paper ≡ "Paper 6"

    noQuantityOverstated :
      Bool

    noQuantityOverstatedIsTrue :
      noQuantityOverstated ≡ true

    physicalCKMPromotion :
      Bool

    physicalCKMPromotionIsFalse :
      physicalCKMPromotion ≡ false

    blockers :
      List CKMFullHonestyBlocker

    blockersAreCanonical :
      blockers ≡ canonicalCKMFullHonestyBlockers

    promotionFlags :
      List CKMPhysicalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

    receiptBoundaryIsCanonical :
      receiptBoundary ≡ canonicalCKMFullHonestyBoundary

open CKMFullHonestyReceipt public

canonicalCKMFullHonestyReceipt :
  CKMFullHonestyReceipt
canonicalCKMFullHonestyReceipt =
  record
    { rows =
        canonicalCKMHonestRows
    ; rowsAreCanonical =
        refl
    ; rowCount =
        "six"
    ; rowCountIsSix =
        refl
    ; paper =
        "Paper 6"
    ; paperIsPaper6 =
        refl
    ; noQuantityOverstated =
        true
    ; noQuantityOverstatedIsTrue =
        refl
    ; physicalCKMPromotion =
        false
    ; physicalCKMPromotionIsFalse =
        refl
    ; blockers =
        canonicalCKMFullHonestyBlockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        canonicalCKMFullHonestyBoundary
    ; receiptBoundaryIsCanonical =
        refl
    }

ckmFullHonestyRowsAreCanonical :
  rows canonicalCKMFullHonestyReceipt ≡ canonicalCKMHonestRows
ckmFullHonestyRowsAreCanonical =
  refl

ckmFullHonestyNoQuantityOverstated :
  noQuantityOverstated canonicalCKMFullHonestyReceipt ≡ true
ckmFullHonestyNoQuantityOverstated =
  refl

ckmFullHonestyPhysicalCKMPromotionFalse :
  physicalCKMPromotion canonicalCKMFullHonestyReceipt ≡ false
ckmFullHonestyPhysicalCKMPromotionFalse =
  refl

ckmFullHonestyNoPromotionFlags :
  promotionFlags canonicalCKMFullHonestyReceipt ≡ []
ckmFullHonestyNoPromotionFlags =
  refl
