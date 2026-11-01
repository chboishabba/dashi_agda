module DASHI.Physics.Closure.Paper6DraftCompleteReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Paper 6 draft-complete receipt.
--
-- This is an editorial/claim-governance receipt for the Paper 6 CKM/Yukawa
-- draft.  This corrected receipt narrows the scope to the Georgi-Jarlskog
-- lambda connection and the leading-order |Vub| adjacent-chain hypothesis.
-- It intentionally does not assert a precision physical CKM derivation.

data Paper6DraftStatus : Set where
  draftCompleteCarrierIdentificationOnly :
    Paper6DraftStatus

data Paper6CKMQuantity : Set where
  wolfensteinLambdaVus :
    Paper6CKMQuantity

  vcbMagnitude :
    Paper6CKMQuantity

  vubMagnitude :
    Paper6CKMQuantity

  gammaAngle :
    Paper6CKMQuantity

  betaAngle :
    Paper6CKMQuantity

  jarlskogInvariant :
    Paper6CKMQuantity

data AccuracyLabel : Set where
  subPercentNumericalAgreement :
    AccuracyLabel

  fewPercentNumericalAgreement :
    AccuracyLabel

  severalPercentNumericalAgreement :
    AccuracyLabel

  orderOnlyStructuralAgreement :
    AccuracyLabel

data DerivationStrengthLabel : Set where
  knownStructuralLiteratureConnection :
    DerivationStrengthLabel

  carrierArithmeticIdentification :
    DerivationStrengthLabel

  leadingOrderCarrierCalculation :
    DerivationStrengthLabel

  openFrontier :
    DerivationStrengthLabel

  candidateDiagnostic :
    DerivationStrengthLabel

  diagnosticOnlyComparison :
    DerivationStrengthLabel

data CarrierArithmeticMechanism : Set where
  adjacentOnlyDepthChain :
    CarrierArithmeticMechanism

  heegnerDMinusSevenCMPoint :
    CarrierArithmeticMechanism

canonicalIndependentCarrierMechanisms :
  List CarrierArithmeticMechanism
canonicalIndependentCarrierMechanisms =
  adjacentOnlyDepthChain
  ∷ []

data Paper6Approximation : Set where
  leadingOrderCarrierReadback :
    Paper6Approximation

  higherOrderCorrectionsRequired :
    Paper6Approximation

  downDiagonalizerUdApproximatelyIdentity :
    Paper6Approximation

canonicalPaper6Approximations :
  List Paper6Approximation
canonicalPaper6Approximations =
  leadingOrderCarrierReadback
  ∷ higherOrderCorrectionsRequired
  ∷ downDiagonalizerUdApproximatelyIdentity
  ∷ []

data Paper6Blocker : Set where
  noCertifiedPhysicalCKMDiagonalisation :
    Paper6Blocker

  noPrecisionPhysicalCKMErrorTheorem :
    Paper6Blocker

  higherOrderCorrectionsNotDerived :
    Paper6Blocker

  udApproximationNotExactPhysicalDiagonalizer :
    Paper6Blocker

  jarlskogOnlyLeadingOrderBookkeeping :
    Paper6Blocker

canonicalPaper6Blockers : List Paper6Blocker
canonicalPaper6Blockers =
  noCertifiedPhysicalCKMDiagonalisation
  ∷ noPrecisionPhysicalCKMErrorTheorem
  ∷ higherOrderCorrectionsNotDerived
  ∷ udApproximationNotExactPhysicalDiagonalizer
  ∷ jarlskogOnlyLeadingOrderBookkeeping
  ∷ []

data Paper6PhysicalCKMPromotion : Set where

paper6PhysicalCKMPromotionImpossibleHere :
  Paper6PhysicalCKMPromotion →
  ⊥
paper6PhysicalCKMPromotionImpossibleHere ()

record CKMQuantityDraftRow : Set where
  field
    quantity :
      Paper6CKMQuantity

    formula :
      String

    carrierValue :
      Float

    comparisonValue :
      Float

    relativeErrorPercent :
      Float

    accuracy :
      AccuracyLabel

    derivationStrength :
      DerivationStrengthLabel

    rowBoundary :
      String

open CKMQuantityDraftRow public

lambdaDraftRow : CKMQuantityDraftRow
lambdaDraftRow =
  record
    { quantity =
        wolfensteinLambdaVus
    ; formula =
        "lambda = alpha_D = alpha1*pi*sqrt(3)"
    ; carrierValue =
        0.2244032573430574
    ; comparisonValue =
        0.22441
    ; relativeErrorPercent =
        0.01
    ; accuracy =
        subPercentNumericalAgreement
    ; derivationStrength =
        knownStructuralLiteratureConnection
    ; rowBoundary =
        "Vus/lambda is recorded as the known Georgi-Jarlskog structural connection; Paper 6 does not claim it as a new DASHI CKM derivation."
    }

vcbDraftRow : CKMQuantityDraftRow
vcbDraftRow =
  record
    { quantity =
        vcbMagnitude
    ; formula =
        "|Vcb| = A*lambda^2 with A = 0.8086 supplied as PDG/Wolfenstein input"
    ; carrierValue =
        0.04072
    ; comparisonValue =
        0.0408
    ; relativeErrorPercent =
        0.20
    ; accuracy =
        subPercentNumericalAgreement
    ; derivationStrength =
        openFrontier
    ; rowBoundary =
        "|Vcb| is demoted: no independent carrier derivation of A is supplied, so this row is an open frontier rather than carrier arithmetic."
    }

vubDraftRow : CKMQuantityDraftRow
vubDraftRow =
  record
    { quantity =
        vubMagnitude
    ; formula =
        "|Vub| = alpha1*alpha2 from adjacent-only chain 0->1->2"
    ; carrierValue =
        0.003537
    ; comparisonValue =
        0.00369
    ; relativeErrorPercent =
        4.16
    ; accuracy =
        fewPercentNumericalAgreement
    ; derivationStrength =
        leadingOrderCarrierCalculation
    ; rowBoundary =
        "|Vub| uses the adjacent-only up-depth chain as a leading-order carrier readback."
    }

gammaDraftRow : CKMQuantityDraftRow
gammaDraftRow =
  record
    { quantity =
        gammaAngle
    ; formula =
        "gamma = arctan(sqrt(7))*(1-alpha1)"
    ; carrierValue =
        1.1596
    ; comparisonValue =
        1.178
    ; relativeErrorPercent =
        1.57
    ; accuracy =
        fewPercentNumericalAgreement
    ; derivationStrength =
        candidateDiagnostic
    ; rowBoundary =
        "Gamma is a candidate diagnostic only: the D=-7 selection theorem is not proved in the carrier receipts."
    }

betaDraftRow : CKMQuantityDraftRow
betaDraftRow =
  record
    { quantity =
        betaAngle
    ; formula =
        "beta = arctan(eta/(1-rho)), with R_b = alpha1*alpha2/(A*lambda^3)"
    ; carrierValue =
        0.3973
    ; comparisonValue =
        0.3747
    ; relativeErrorPercent =
        6.04
    ; accuracy =
        severalPercentNumericalAgreement
    ; derivationStrength =
        openFrontier
    ; rowBoundary =
        "Beta is open frontier because it inherits the leading-order |Vub| approximation and the unproved D=-7 gamma selection."
    }

jarlskogDraftRow : CKMQuantityDraftRow
jarlskogDraftRow =
  record
    { quantity =
        jarlskogInvariant
    ; formula =
        "J_CP is recorded only as leading Wolfenstein-order carrier bookkeeping"
    ; carrierValue =
        0.000064
    ; comparisonValue =
        0.000030
    ; relativeErrorPercent =
        100.0
    ; accuracy =
        orderOnlyStructuralAgreement
    ; derivationStrength =
        diagnosticOnlyComparison
    ; rowBoundary =
        "Jarlskog is included as the sixth CKM quantity only at structural/order level; no precision or nonzero physical theorem is claimed."
    }

canonicalPaper6CKMQuantityRows : List CKMQuantityDraftRow
canonicalPaper6CKMQuantityRows =
  lambdaDraftRow
  ∷ vcbDraftRow
  ∷ vubDraftRow
  ∷ gammaDraftRow
  ∷ betaDraftRow
  ∷ jarlskogDraftRow
  ∷ []

paper6DraftCompleteStatement : String
paper6DraftCompleteStatement =
  "Paper 6 scope is revised: it presents lambda = sqrt(md/ms) as the known Georgi-Jarlskog structural connection and |Vub| approx alpha1*alpha2 as a leading-order adjacent-chain hypothesis in the U_d approximately I approximation; |Vcb|, gamma, beta, alpha, and precision CKM diagonalisation remain open frontier."

record Paper6DraftCompleteReceipt : Set where
  field
    status :
      Paper6DraftStatus

    statusIsDraftCompleteCarrierIdentificationOnly :
      status ≡ draftCompleteCarrierIdentificationOnly

    draftComplete :
      Bool

    draftCompleteIsTrue :
      draftComplete ≡ true

    quantityRows :
      List CKMQuantityDraftRow

    quantityRowsAreCanonical :
      quantityRows ≡ canonicalPaper6CKMQuantityRows

    quantityCount :
      Nat

    quantityCountIsSix :
      quantityCount ≡ 6

    allRowsHaveAccuracyLabels :
      Bool

    allRowsHaveAccuracyLabelsIsTrue :
      allRowsHaveAccuracyLabels ≡ true

    allRowsHaveDerivationStrengthLabels :
      Bool

    allRowsHaveDerivationStrengthLabelsIsTrue :
      allRowsHaveDerivationStrengthLabels ≡ true

    independentCarrierMechanisms :
      List CarrierArithmeticMechanism

    independentCarrierMechanismsAreCanonical :
      independentCarrierMechanisms ≡ canonicalIndependentCarrierMechanisms

    adjacentOnlyChainDocumented :
      Bool

    adjacentOnlyChainDocumentedIsTrue :
      adjacentOnlyChainDocumented ≡ true

    heegnerDMinusSevenDocumented :
      Bool

    heegnerDMinusSevenDocumentedIsFalse :
      heegnerDMinusSevenDocumented ≡ false

    mechanismsAreIndependent :
      Bool

    mechanismsAreIndependentIsFalse :
      mechanismsAreIndependent ≡ false

    approximations :
      List Paper6Approximation

    approximationsAreCanonical :
      approximations ≡ canonicalPaper6Approximations

    higherOrderCorrectionsDocumented :
      Bool

    higherOrderCorrectionsDocumentedIsTrue :
      higherOrderCorrectionsDocumented ≡ true

    udApproximatelyIdentityDocumented :
      Bool

    udApproximatelyIdentityDocumentedIsTrue :
      udApproximatelyIdentityDocumented ≡ true

    leadingOrderOnly :
      Bool

    leadingOrderOnlyIsTrue :
      leadingOrderOnly ≡ true

    structuralCarrierIdentificationOnly :
      Bool

    structuralCarrierIdentificationOnlyIsTrue :
      structuralCarrierIdentificationOnly ≡ true

    precisionCKMDerivationClaimed :
      Bool

    precisionCKMDerivationClaimedIsFalse :
      precisionCKMDerivationClaimed ≡ false

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

    falsePhysicalCKMPromotionRecorded :
      Bool

    falsePhysicalCKMPromotionRecordedIsTrue :
      falsePhysicalCKMPromotionRecorded ≡ true

    blockers :
      List Paper6Blocker

    blockersAreCanonical :
      blockers ≡ canonicalPaper6Blockers

    promotionFlags :
      List Paper6PhysicalCKMPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ paper6DraftCompleteStatement

    receiptBoundary :
      List String

open Paper6DraftCompleteReceipt public

canonicalPaper6DraftCompleteReceipt :
  Paper6DraftCompleteReceipt
canonicalPaper6DraftCompleteReceipt =
  record
    { status =
        draftCompleteCarrierIdentificationOnly
    ; statusIsDraftCompleteCarrierIdentificationOnly =
        refl
    ; draftComplete =
        true
    ; draftCompleteIsTrue =
        refl
    ; quantityRows =
        canonicalPaper6CKMQuantityRows
    ; quantityRowsAreCanonical =
        refl
    ; quantityCount =
        6
    ; quantityCountIsSix =
        refl
    ; allRowsHaveAccuracyLabels =
        true
    ; allRowsHaveAccuracyLabelsIsTrue =
        refl
    ; allRowsHaveDerivationStrengthLabels =
        true
    ; allRowsHaveDerivationStrengthLabelsIsTrue =
        refl
    ; independentCarrierMechanisms =
        canonicalIndependentCarrierMechanisms
    ; independentCarrierMechanismsAreCanonical =
        refl
    ; adjacentOnlyChainDocumented =
        true
    ; adjacentOnlyChainDocumentedIsTrue =
        refl
    ; heegnerDMinusSevenDocumented =
        false
    ; heegnerDMinusSevenDocumentedIsFalse =
        refl
    ; mechanismsAreIndependent =
        false
    ; mechanismsAreIndependentIsFalse =
        refl
    ; approximations =
        canonicalPaper6Approximations
    ; approximationsAreCanonical =
        refl
    ; higherOrderCorrectionsDocumented =
        true
    ; higherOrderCorrectionsDocumentedIsTrue =
        refl
    ; udApproximatelyIdentityDocumented =
        true
    ; udApproximatelyIdentityDocumentedIsTrue =
        refl
    ; leadingOrderOnly =
        true
    ; leadingOrderOnlyIsTrue =
        refl
    ; structuralCarrierIdentificationOnly =
        true
    ; structuralCarrierIdentificationOnlyIsTrue =
        refl
    ; precisionCKMDerivationClaimed =
        false
    ; precisionCKMDerivationClaimedIsFalse =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    ; falsePhysicalCKMPromotionRecorded =
        true
    ; falsePhysicalCKMPromotionRecordedIsTrue =
        refl
    ; blockers =
        canonicalPaper6Blockers
    ; blockersAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        paper6DraftCompleteStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Paper 6 scope is revised to lambda/Vus as Georgi-Jarlskog literature connection and |Vub| as leading-order adjacent-chain hypothesis"
        ∷ "|Vcb| is open frontier because A = 0.8086 is PDG input"
        ∷ "Gamma is candidate diagnostic only because D=-7 selection is unproved"
        ∷ "Beta and alpha are downstream/open and are not independent carrier predictions"
        ∷ "Each row carries both an accuracy label and a derivation-strength label"
        ∷ "Only the adjacent-only chain is retained as a Paper 6 carrier mechanism"
        ∷ "Higher-order corrections are expected and not derived in this receipt"
        ∷ "The down-sector U_d approximately I simplification is documented as an approximation, not a physical diagonalisation theorem"
        ∷ "Precision physical CKM derivation and physical CKM promotion are false"
        ∷ []
    }

paper6DraftCompleteHasSixQuantities :
  quantityCount canonicalPaper6DraftCompleteReceipt ≡ 6
paper6DraftCompleteHasSixQuantities =
  refl

paper6DraftCompleteRecordsIndependentMechanisms :
  independentCarrierMechanisms canonicalPaper6DraftCompleteReceipt
  ≡
  canonicalIndependentCarrierMechanisms
paper6DraftCompleteRecordsIndependentMechanisms =
  refl

paper6DraftCompleteDocumentsApproximations :
  approximations canonicalPaper6DraftCompleteReceipt
  ≡
  canonicalPaper6Approximations
paper6DraftCompleteDocumentsApproximations =
  refl

paper6DraftCompleteDoesNotClaimPrecisionCKM :
  precisionCKMDerivationClaimed canonicalPaper6DraftCompleteReceipt
  ≡
  false
paper6DraftCompleteDoesNotClaimPrecisionCKM =
  refl

paper6DraftCompleteKeepsPhysicalCKMFalse :
  physicalCKMPromoted canonicalPaper6DraftCompleteReceipt ≡ false
paper6DraftCompleteKeepsPhysicalCKMFalse =
  refl

paper6DraftCompleteNoPromotion :
  Paper6PhysicalCKMPromotion →
  ⊥
paper6DraftCompleteNoPromotion =
  paper6PhysicalCKMPromotionImpossibleHere
