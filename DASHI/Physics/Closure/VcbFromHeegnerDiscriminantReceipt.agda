module DASHI.Physics.Closure.VcbFromHeegnerDiscriminantReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_; _-_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

open import MonsterOntos using (SSP; p3; p5; toNat)

------------------------------------------------------------------------
-- Gate 7 Heegner p3-p5 Vcb diagnostic receipt.
--
-- This is a concrete diagnostic receipt only.  It records the p3 and p5
-- finite-lane discriminant readback feeding the down-sector off-diagonal
-- target
--
--   (Y_d)23 = (14 / sqrt(24)) * (8*pi/3)
--
-- and the comparison |V_cb| ~= 0.040717 against a PDG-sized comparison
-- target ~= 0.041.  The recorded 0.20 percent status is diagnostic
-- bookkeeping only: no physical Vcb value, CKM diagonalisation, Yukawa
-- matrix, or promotion flag is constructed here.

data HeegnerP3P5VcbBlocker : Set where
  missingPhysicalYukawaMatrixForDownSector :
    HeegnerP3P5VcbBlocker

  missingBiunitaryDiagonalizationForPhysicalCKM :
    HeegnerP3P5VcbBlocker

  missingPDGVcbAcceptedAuthority :
    HeegnerP3P5VcbBlocker

  missingErrorBoundForHeegnerP3P5Diagnostic :
    HeegnerP3P5VcbBlocker

canonicalHeegnerP3P5VcbBlockers :
  List HeegnerP3P5VcbBlocker
canonicalHeegnerP3P5VcbBlockers =
  missingPhysicalYukawaMatrixForDownSector
  ∷ missingBiunitaryDiagonalizationForPhysicalCKM
  ∷ missingPDGVcbAcceptedAuthority
  ∷ missingErrorBoundForHeegnerP3P5Diagnostic
  ∷ []

data PhysicalVcbDerivedFromHeegnerP3P5 : Set where

physicalVcbDerivedFromHeegnerP3P5IsFalse :
  PhysicalVcbDerivedFromHeegnerP3P5 →
  ⊥
physicalVcbDerivedFromHeegnerP3P5IsFalse ()

heegnerP3P5Yd23Formula : String
heegnerP3P5Yd23Formula =
  "(Y_d)23 = (14 / sqrt(24)) * (8*pi/3)"

vcbDiagnosticApproxLabel : String
vcbDiagnosticApproxLabel =
  "|V_cb| diagnostic approximately 0.040717"

pdgVcbComparisonLabel : String
pdgVcbComparisonLabel =
  "PDG comparison target approximately 0.041"

vcbDiagnosticStatusLabel : String
vcbDiagnosticStatusLabel =
  "0.20 percent diagnostic status; comparison only"

record VcbFromHeegnerDiscriminantReceipt : Set where
  field
    lowerLane :
      SSP

    lowerLaneIsP3 :
      lowerLane ≡ p3

    upperLane :
      SSP

    upperLaneIsP5 :
      upperLane ≡ p5

    p3BaseFieldCardinality :
      Nat

    p3BaseFieldCardinalityIsThree :
      p3BaseFieldCardinality ≡ 3

    p5BaseFieldCardinality :
      Nat

    p5BaseFieldCardinalityIsFive :
      p5BaseFieldCardinality ≡ 5

    p3DiscriminantDiagnostic :
      Nat

    p3DiscriminantDiagnosticIsThreeSquaredMinusThree :
      p3DiscriminantDiagnostic ≡ (3 * 3) - 3

    p3DiscriminantDiagnosticIsSix :
      p3DiscriminantDiagnostic ≡ 6

    p5DiscriminantDiagnostic :
      Nat

    p5DiscriminantDiagnosticIsFiveSquaredMinusFive :
      p5DiscriminantDiagnostic ≡ (5 * 5) - 5

    p5DiscriminantDiagnosticIsTwenty :
      p5DiscriminantDiagnostic ≡ 20

    heegnerNumeratorDiagnostic :
      Nat

    heegnerNumeratorDiagnosticIsFourteen :
      heegnerNumeratorDiagnostic ≡ 14

    heegnerSqrtRadicandDiagnostic :
      Nat

    heegnerSqrtRadicandDiagnosticIsTwentyFour :
      heegnerSqrtRadicandDiagnostic ≡ 24

    heegnerAngularNumeratorDiagnostic :
      Nat

    heegnerAngularNumeratorDiagnosticIsEight :
      heegnerAngularNumeratorDiagnostic ≡ 8

    heegnerAngularDenominatorDiagnostic :
      Nat

    heegnerAngularDenominatorDiagnosticIsThree :
      heegnerAngularDenominatorDiagnostic ≡ 3

    yd23Formula :
      String

    yd23FormulaIsCanonical :
      yd23Formula ≡ heegnerP3P5Yd23Formula

    vcbPartsPerMillion :
      Nat

    vcbPartsPerMillionIsApproxZeroPointZeroFourZeroSevenOneSeven :
      vcbPartsPerMillion ≡ 40717

    vcbDiagnosticLabel :
      String

    vcbDiagnosticLabelIsCanonical :
      vcbDiagnosticLabel ≡ vcbDiagnosticApproxLabel

    pdgComparisonPartsPerMillion :
      Nat

    pdgComparisonPartsPerMillionIsApproxZeroPointZeroFourOne :
      pdgComparisonPartsPerMillion ≡ 41000

    pdgComparisonLabel :
      String

    pdgComparisonLabelIsCanonical :
      pdgComparisonLabel ≡ pdgVcbComparisonLabel

    diagnosticStatusBasisPoints :
      Nat

    diagnosticStatusBasisPointsIsTwenty :
      diagnosticStatusBasisPoints ≡ 20

    diagnosticStatusLabel :
      String

    diagnosticStatusLabelIsCanonical :
      diagnosticStatusLabel ≡ vcbDiagnosticStatusLabel

    derivedPhysicalVcb :
      Bool

    derivedPhysicalVcbIsFalse :
      derivedPhysicalVcb ≡ false

    physicalYukawaMatrixConstructed :
      Bool

    physicalYukawaMatrixConstructedIsFalse :
      physicalYukawaMatrixConstructed ≡ false

    physicalCKMDiagonalizationConstructed :
      Bool

    physicalCKMDiagonalizationConstructedIsFalse :
      physicalCKMDiagonalizationConstructed ≡ false

    pdgAuthorityPromoted :
      Bool

    pdgAuthorityPromotedIsFalse :
      pdgAuthorityPromoted ≡ false

    physicalPromotionClaimed :
      Bool

    physicalPromotionClaimedIsFalse :
      physicalPromotionClaimed ≡ false

    blockers :
      List HeegnerP3P5VcbBlocker

    blockersAreCanonical :
      blockers ≡ canonicalHeegnerP3P5VcbBlockers

    receiptBoundary :
      List String

open VcbFromHeegnerDiscriminantReceipt public

canonicalVcbFromHeegnerDiscriminantReceipt :
  VcbFromHeegnerDiscriminantReceipt
canonicalVcbFromHeegnerDiscriminantReceipt =
  record
    { lowerLane =
        p3
    ; lowerLaneIsP3 =
        refl
    ; upperLane =
        p5
    ; upperLaneIsP5 =
        refl
    ; p3BaseFieldCardinality =
        toNat p3
    ; p3BaseFieldCardinalityIsThree =
        refl
    ; p5BaseFieldCardinality =
        toNat p5
    ; p5BaseFieldCardinalityIsFive =
        refl
    ; p3DiscriminantDiagnostic =
        6
    ; p3DiscriminantDiagnosticIsThreeSquaredMinusThree =
        refl
    ; p3DiscriminantDiagnosticIsSix =
        refl
    ; p5DiscriminantDiagnostic =
        20
    ; p5DiscriminantDiagnosticIsFiveSquaredMinusFive =
        refl
    ; p5DiscriminantDiagnosticIsTwenty =
        refl
    ; heegnerNumeratorDiagnostic =
        14
    ; heegnerNumeratorDiagnosticIsFourteen =
        refl
    ; heegnerSqrtRadicandDiagnostic =
        24
    ; heegnerSqrtRadicandDiagnosticIsTwentyFour =
        refl
    ; heegnerAngularNumeratorDiagnostic =
        8
    ; heegnerAngularNumeratorDiagnosticIsEight =
        refl
    ; heegnerAngularDenominatorDiagnostic =
        3
    ; heegnerAngularDenominatorDiagnosticIsThree =
        refl
    ; yd23Formula =
        heegnerP3P5Yd23Formula
    ; yd23FormulaIsCanonical =
        refl
    ; vcbPartsPerMillion =
        40717
    ; vcbPartsPerMillionIsApproxZeroPointZeroFourZeroSevenOneSeven =
        refl
    ; vcbDiagnosticLabel =
        vcbDiagnosticApproxLabel
    ; vcbDiagnosticLabelIsCanonical =
        refl
    ; pdgComparisonPartsPerMillion =
        41000
    ; pdgComparisonPartsPerMillionIsApproxZeroPointZeroFourOne =
        refl
    ; pdgComparisonLabel =
        pdgVcbComparisonLabel
    ; pdgComparisonLabelIsCanonical =
        refl
    ; diagnosticStatusBasisPoints =
        20
    ; diagnosticStatusBasisPointsIsTwenty =
        refl
    ; diagnosticStatusLabel =
        vcbDiagnosticStatusLabel
    ; diagnosticStatusLabelIsCanonical =
        refl
    ; derivedPhysicalVcb =
        false
    ; derivedPhysicalVcbIsFalse =
        refl
    ; physicalYukawaMatrixConstructed =
        false
    ; physicalYukawaMatrixConstructedIsFalse =
        refl
    ; physicalCKMDiagonalizationConstructed =
        false
    ; physicalCKMDiagonalizationConstructedIsFalse =
        refl
    ; pdgAuthorityPromoted =
        false
    ; pdgAuthorityPromotedIsFalse =
        refl
    ; physicalPromotionClaimed =
        false
    ; physicalPromotionClaimedIsFalse =
        refl
    ; blockers =
        canonicalHeegnerP3P5VcbBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "Heegner p3-p5 lane records (Y_d)23 = (14 / sqrt(24)) * (8*pi/3)"
        ∷ "|V_cb| diagnostic is approximately 0.040717"
        ∷ "PDG comparison target is approximately 0.041"
        ∷ "diagnostic status is recorded as 0.20 percent"
        ∷ "all physical derivation and promotion flags are false"
        ∷ []
    }

vcbHeegnerReceiptDerivedPhysicalVcbFalse :
  derivedPhysicalVcb canonicalVcbFromHeegnerDiscriminantReceipt ≡ false
vcbHeegnerReceiptDerivedPhysicalVcbFalse =
  refl

vcbHeegnerReceiptPhysicalPromotionFalse :
  physicalPromotionClaimed canonicalVcbFromHeegnerDiscriminantReceipt ≡ false
vcbHeegnerReceiptPhysicalPromotionFalse =
  refl

vcbHeegnerNoPhysicalVcbDerivation :
  PhysicalVcbDerivedFromHeegnerP3P5 →
  ⊥
vcbHeegnerNoPhysicalVcbDerivation =
  physicalVcbDerivedFromHeegnerP3P5IsFalse
