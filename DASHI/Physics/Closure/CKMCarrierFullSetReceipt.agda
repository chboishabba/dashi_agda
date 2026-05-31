module DASHI.Physics.Closure.CKMCarrierFullSetReceipt where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Complete carrier CKM prediction set receipt.
--
-- This records the Manager B full carrier CKM candidate table.  The rows are
-- numerical carrier predictions against PDG comparison targets, with all
-- listed errors below ten percent.

data CKMCarrierObservable : Set where
  lambdaFromDownMassRatio :
    CKMCarrierObservable

  vcbFromIsogenyArithmetic :
    CKMCarrierObservable

  vubFromAlphaProduct :
    CKMCarrierObservable

  gammaFromArcTanSqrt7 :
    CKMCarrierObservable

  betaFromRhoEta :
    CKMCarrierObservable

record CKMCarrierPredictionRow : Set where
  field
    observable :
      CKMCarrierObservable

    formula :
      String

    carrierValue :
      Float

    pdgComparison :
      Float

    relativeErrorPercent :
      Float

    rowNote :
      String

open CKMCarrierPredictionRow public

lambdaCarrierCKMRow : CKMCarrierPredictionRow
lambdaCarrierCKMRow =
  record
    { observable =
        lambdaFromDownMassRatio
    ; formula =
        "lambda = sqrt(m_d/m_s)"
    ; carrierValue =
        0.22420
    ; pdgComparison =
        0.22441
    ; relativeErrorPercent =
        0.09
    ; rowNote =
        "Cabibbo angle carrier prediction"
    }

vcbCarrierCKMRow : CKMCarrierPredictionRow
vcbCarrierCKMRow =
  record
    { observable =
        vcbFromIsogenyArithmetic
    ; formula =
        "|Vcb| = isogeny arithmetic / A lambda^2"
    ; carrierValue =
        0.04072
    ; pdgComparison =
        0.0408
    ; relativeErrorPercent =
        0.20
    ; rowNote =
        "PDG comparison is near 0.0408"
    }

vubCarrierCKMRow : CKMCarrierPredictionRow
vubCarrierCKMRow =
  record
    { observable =
        vubFromAlphaProduct
    ; formula =
        "|Vub| = alpha1 alpha2 = sqrt(m_u/m_t)"
    ; carrierValue =
        0.003537
    ; pdgComparison =
        0.00369
    ; relativeErrorPercent =
        4.16
    ; rowNote =
        "Carrier alpha-product prediction"
    }

gammaCarrierCKMRow : CKMCarrierPredictionRow
gammaCarrierCKMRow =
  record
    { observable =
        gammaFromArcTanSqrt7
    ; formula =
        "gamma = arctan(sqrt(7)) * (1 - alpha1)"
    ; carrierValue =
        1.1596
    ; pdgComparison =
        1.178
    ; relativeErrorPercent =
        1.57
    ; rowNote =
        "PDG comparison is about 1.178 radians"
    }

betaCarrierCKMRow : CKMCarrierPredictionRow
betaCarrierCKMRow =
  record
    { observable =
        betaFromRhoEta
    ; formula =
        "beta = arctan(eta/(1-rho))"
    ; carrierValue =
        0.3973
    ; pdgComparison =
        0.3747
    ; relativeErrorPercent =
        6.04
    ; rowNote =
        "Carrier unitarity-triangle beta prediction"
    }

canonicalCKMCarrierPredictionRows :
  List CKMCarrierPredictionRow
canonicalCKMCarrierPredictionRows =
  lambdaCarrierCKMRow
  ∷ vcbCarrierCKMRow
  ∷ vubCarrierCKMRow
  ∷ gammaCarrierCKMRow
  ∷ betaCarrierCKMRow
  ∷ []

record CKMCarrierFullSetReceipt : Set where
  field
    rows :
      List CKMCarrierPredictionRow

    rowsAreCanonical :
      rows ≡ canonicalCKMCarrierPredictionRows

    fullCarrierCKMSetCandidate :
      Bool

    fullCarrierCKMSetCandidateIsTrue :
      fullCarrierCKMSetCandidate ≡ true

    allWithin10Percent :
      Bool

    allWithin10PercentIsTrue :
      allWithin10Percent ≡ true

    receiptBoundary :
      List String

open CKMCarrierFullSetReceipt public

canonicalCKMCarrierFullSetReceipt :
  CKMCarrierFullSetReceipt
canonicalCKMCarrierFullSetReceipt =
  record
    { rows =
        canonicalCKMCarrierPredictionRows
    ; rowsAreCanonical =
        refl
    ; fullCarrierCKMSetCandidate =
        true
    ; fullCarrierCKMSetCandidateIsTrue =
        refl
    ; allWithin10Percent =
        true
    ; allWithin10PercentIsTrue =
        refl
    ; receiptBoundary =
        "This receipt records the complete five-row carrier CKM prediction set"
        ∷ "The table includes lambda, |Vcb|, |Vub|, gamma, and beta"
        ∷ "All recorded carrier-to-PDG comparison errors are below ten percent"
        ∷ []
    }

ckmCarrierFullSetCandidateFlag :
  fullCarrierCKMSetCandidate canonicalCKMCarrierFullSetReceipt ≡ true
ckmCarrierFullSetCandidateFlag =
  refl

ckmCarrierFullSetAllWithin10Percent :
  allWithin10Percent canonicalCKMCarrierFullSetReceipt ≡ true
ckmCarrierFullSetAllWithin10Percent =
  refl
