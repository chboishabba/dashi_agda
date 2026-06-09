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
-- carrier table to a physical CKM derivation.  This corrected receipt keeps
-- only lambda as a structural/literature connection, demotes |Vcb| to a PDG
-- tautology, demotes gamma to an ungrounded D=-7 hypothesis, and propagates
-- that demotion to beta and alpha.

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
  knownStructuralConnection :
    CKMHonestStatus

  carrierArithmetic :
    CKMHonestStatus

  pdgTautology :
    CKMHonestStatus

  leadingOrderEstimate :
    CKMHonestStatus

  leadingOrderDerived :
    CKMHonestStatus

  ungroundedStructuralHypothesis :
    CKMHonestStatus

  inheritsDMinusSevenUncertainty :
    CKMHonestStatus

  tautologicalConsequence :
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
  "|Vcb| = A * lambda^2 with A = 0.8086 supplied from PDG/Wolfenstein input"

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

knownStructuralConnectionLabel : String
knownStructuralConnectionLabel =
  "known structural connection"

pdgTautologyLabel : String
pdgTautologyLabel =
  "pdg-tautology; not a carrier prediction"

leadingOrderEstimateLabel : String
leadingOrderEstimateLabel =
  "leading-order estimate"

leadingOrderDerivedLabel : String
leadingOrderDerivedLabel =
  "leading-order derived"

ungroundedStructuralHypothesisLabel : String
ungroundedStructuralHypothesisLabel =
  "ungrounded structural hypothesis; D=-7 selection unproved"

inheritsDMinusSevenUncertaintyLabel : String
inheritsDMinusSevenUncertaintyLabel =
  "inherits D=-7 uncertainty"

tautologicalConsequenceLabel : String
tautologicalConsequenceLabel =
  "tautological consequence; not an independent prediction"

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
        knownStructuralConnection
    ; statusLabel =
        knownStructuralConnectionLabel
    ; rowBoundary =
        "Paper 6 records lambda from sqrt(md/ms) as the Georgi-Jarlskog structural/literature connection, not as a new DASHI CKM derivation"
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
        pdgTautology
    ; statusLabel =
        pdgTautologyLabel
    ; rowBoundary =
        "Paper 6 demotes |Vcb|: A = 0.8086 is PDG input and |Vcb| = A*lambda^2 is a Wolfenstein tautology, not an independent carrier prediction"
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
        ungroundedStructuralHypothesis
    ; statusLabel =
        ungroundedStructuralHypothesisLabel
    ; rowBoundary =
        "Paper 6 demotes gamma: the arctan(sqrt7)*(1-alpha1) formula depends on an unproved D=-7 selection theorem"
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
        inheritsDMinusSevenUncertainty
    ; statusLabel =
        inheritsDMinusSevenUncertaintyLabel
    ; rowBoundary =
        "Paper 6 demotes beta: it is downstream of leading-order |Vub| and the ungrounded D=-7 gamma hypothesis"
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
        tautologicalConsequence
    ; statusLabel =
        tautologicalConsequenceLabel
    ; rowBoundary =
        "Paper 6 demotes alpha: alpha = pi - beta - gamma is a tautological consequence, not an independent carrier prediction"
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
  ∷ "lambda sqrt(md/ms): 0.9 percent, Georgi-Jarlskog structural/literature connection"
  ∷ "|Vcb| = A*lambda^2: pdg-tautology, not a carrier prediction"
  ∷ "|Vub| alpha1*alpha2 with U_d approximately I: 4.2 percent, leading-order estimate"
  ∷ "gamma arctan(sqrt7)*(1-alpha1): ungrounded structural hypothesis, D=-7 selection unproved"
  ∷ "beta arctan(eta/(1-rho)): inherits D=-7 uncertainty and leading-order |Vub| uncertainty"
  ∷ "alpha pi-beta-gamma: tautological consequence, not an independent prediction"
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
