module DASHI.Physics.QFT.ConformalSpinFromCMReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.BraidingMorphismReceipt as Braiding
import DASHI.Physics.QFT.FiniteDHRAbelianReconstructionReceipt as DHR

------------------------------------------------------------------------
-- CM conformal-spin diagnostic receipt.
--
-- This module records the finite prime-lane CM conformal-spin labels visible
-- at the current abelian character surface.  The labels are diagnostic:
-- p2/D=-4 has h=1, p3/D=-3 has h=3/4, and p5/D=-7 has h=7/4 modulo
-- integers.  None is the expected h=1/2 fermion conformal spin for direct
-- fundamental quark fields, so the finite prime-lane CM characters are not
-- promoted here as direct quark fields or as a full Standard Model sector.

data CMConformalSpinLane : Set where
  p2GaussianD-4Lane :
    CMConformalSpinLane

  p3EisensteinD-3Lane :
    CMConformalSpinLane

  p5HeegnerD-7Lane :
    CMConformalSpinLane

canonicalCMConformalSpinLanes :
  List CMConformalSpinLane
canonicalCMConformalSpinLanes =
  p2GaussianD-4Lane
  ∷ p3EisensteinD-3Lane
  ∷ p5HeegnerD-7Lane
  ∷ []

cmLanePrimeLabel :
  CMConformalSpinLane →
  Nat
cmLanePrimeLabel p2GaussianD-4Lane =
  2
cmLanePrimeLabel p3EisensteinD-3Lane =
  3
cmLanePrimeLabel p5HeegnerD-7Lane =
  5

cmLaneDiscriminantLabel :
  CMConformalSpinLane →
  String
cmLaneDiscriminantLabel p2GaussianD-4Lane =
  "D=-4"
cmLaneDiscriminantLabel p3EisensteinD-3Lane =
  "D=-3"
cmLaneDiscriminantLabel p5HeegnerD-7Lane =
  "D=-7"

cmConformalSpinNumeratorOverFour :
  CMConformalSpinLane →
  Nat
cmConformalSpinNumeratorOverFour p2GaussianD-4Lane =
  4
cmConformalSpinNumeratorOverFour p3EisensteinD-3Lane =
  3
cmConformalSpinNumeratorOverFour p5HeegnerD-7Lane =
  7

cmConformalSpinDenominator :
  CMConformalSpinLane →
  Nat
cmConformalSpinDenominator _ =
  4

cmConformalSpinModuloIntegerLabel :
  CMConformalSpinLane →
  String
cmConformalSpinModuloIntegerLabel p2GaussianD-4Lane =
  "h=1 mod Z"
cmConformalSpinModuloIntegerLabel p3EisensteinD-3Lane =
  "h=3/4 mod Z"
cmConformalSpinModuloIntegerLabel p5HeegnerD-7Lane =
  "h=7/4 mod Z"

data ConformalSpinFermionHalfDiagnostic : Set where
  notExpectedFermionSpinOneHalfForQuarks :
    ConformalSpinFermionHalfDiagnostic

cmConformalSpinFermionHalfDiagnostic :
  CMConformalSpinLane →
  ConformalSpinFermionHalfDiagnostic
cmConformalSpinFermionHalfDiagnostic _ =
  notExpectedFermionSpinOneHalfForQuarks

cmConformalSpinDiagnosticLabel : String
cmConformalSpinDiagnosticLabel =
  "CM conformal-spin labels are h=1, 3/4, 7/4 modulo integers, not the expected h=1/2 fermion spin for direct fundamental quark fields"

primeLaneCMCharacterBoundaryLabel : String
primeLaneCMCharacterBoundaryLabel =
  "Finite prime-lane CM characters are diagnostic abelian sectors, not direct fundamental quark fields"

data ConformalSpinFromCMPromotionFlag : Set where

conformalSpinFromCMPromotionFlagImpossibleHere :
  ConformalSpinFromCMPromotionFlag →
  ⊥
conformalSpinFromCMPromotionFlagImpossibleHere ()

record ConformalSpinFromCMReceipt : Setω where
  field
    finiteDHRAbelianReceipt :
      DHR.FiniteDHRAbelianReconstructionReceipt

    braidingMorphismReceipt :
      Braiding.BraidingMorphismReceipt

    lanes :
      List CMConformalSpinLane

    lanesAreCanonical :
      lanes ≡ canonicalCMConformalSpinLanes

    p2Prime :
      Nat

    p2PrimeIsTwo :
      p2Prime ≡ cmLanePrimeLabel p2GaussianD-4Lane

    p2Discriminant :
      String

    p2DiscriminantIsD-4 :
      p2Discriminant ≡ cmLaneDiscriminantLabel p2GaussianD-4Lane

    p2SpinNumeratorOverFour :
      Nat

    p2SpinNumeratorOverFourIsFour :
      p2SpinNumeratorOverFour
      ≡
      cmConformalSpinNumeratorOverFour p2GaussianD-4Lane

    p2SpinDenominator :
      Nat

    p2SpinDenominatorIsFour :
      p2SpinDenominator ≡ cmConformalSpinDenominator p2GaussianD-4Lane

    p2SpinLabel :
      String

    p2SpinLabelIsOneModuloIntegers :
      p2SpinLabel ≡ cmConformalSpinModuloIntegerLabel p2GaussianD-4Lane

    p3Prime :
      Nat

    p3PrimeIsThree :
      p3Prime ≡ cmLanePrimeLabel p3EisensteinD-3Lane

    p3Discriminant :
      String

    p3DiscriminantIsD-3 :
      p3Discriminant ≡ cmLaneDiscriminantLabel p3EisensteinD-3Lane

    p3SpinNumeratorOverFour :
      Nat

    p3SpinNumeratorOverFourIsThree :
      p3SpinNumeratorOverFour
      ≡
      cmConformalSpinNumeratorOverFour p3EisensteinD-3Lane

    p3SpinDenominator :
      Nat

    p3SpinDenominatorIsFour :
      p3SpinDenominator ≡ cmConformalSpinDenominator p3EisensteinD-3Lane

    p3SpinLabel :
      String

    p3SpinLabelIsThreeFourthsModuloIntegers :
      p3SpinLabel ≡ cmConformalSpinModuloIntegerLabel p3EisensteinD-3Lane

    p5Prime :
      Nat

    p5PrimeIsFive :
      p5Prime ≡ cmLanePrimeLabel p5HeegnerD-7Lane

    p5Discriminant :
      String

    p5DiscriminantIsD-7 :
      p5Discriminant ≡ cmLaneDiscriminantLabel p5HeegnerD-7Lane

    p5SpinNumeratorOverFour :
      Nat

    p5SpinNumeratorOverFourIsSeven :
      p5SpinNumeratorOverFour
      ≡
      cmConformalSpinNumeratorOverFour p5HeegnerD-7Lane

    p5SpinDenominator :
      Nat

    p5SpinDenominatorIsFour :
      p5SpinDenominator ≡ cmConformalSpinDenominator p5HeegnerD-7Lane

    p5SpinLabel :
      String

    p5SpinLabelIsSevenFourthsModuloIntegers :
      p5SpinLabel ≡ cmConformalSpinModuloIntegerLabel p5HeegnerD-7Lane

    p2FermionHalfDiagnostic :
      ConformalSpinFermionHalfDiagnostic

    p2FermionHalfDiagnosticIsNegative :
      p2FermionHalfDiagnostic
      ≡
      cmConformalSpinFermionHalfDiagnostic p2GaussianD-4Lane

    p3FermionHalfDiagnostic :
      ConformalSpinFermionHalfDiagnostic

    p3FermionHalfDiagnosticIsNegative :
      p3FermionHalfDiagnostic
      ≡
      cmConformalSpinFermionHalfDiagnostic p3EisensteinD-3Lane

    p5FermionHalfDiagnostic :
      ConformalSpinFermionHalfDiagnostic

    p5FermionHalfDiagnosticIsNegative :
      p5FermionHalfDiagnostic
      ≡
      cmConformalSpinFermionHalfDiagnostic p5HeegnerD-7Lane

    diagnosticStatement :
      String

    diagnosticStatementIsCanonical :
      diagnosticStatement ≡ cmConformalSpinDiagnosticLabel

    primeLaneCMCharactersAreDirectQuarkFields :
      Bool

    primeLaneCMCharactersAreDirectQuarkFieldsIsFalse :
      primeLaneCMCharactersAreDirectQuarkFields ≡ false

    quarkFermionSpinOneHalfMatched :
      Bool

    quarkFermionSpinOneHalfMatchedIsFalse :
      quarkFermionSpinOneHalfMatched ≡ false

    fullStandardModelMatterPromoted :
      Bool

    fullStandardModelMatterPromotedIsFalse :
      fullStandardModelMatterPromoted ≡ false

    fullStandardModelGaugePromoted :
      Bool

    fullStandardModelGaugePromotedIsFalse :
      fullStandardModelGaugePromoted ≡ false

    fullDHRDRReconstructionPromoted :
      Bool

    fullDHRDRReconstructionPromotedIsFalse :
      fullDHRDRReconstructionPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    promotionFlags :
      List ConformalSpinFromCMPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ primeLaneCMCharacterBoundaryLabel

    receiptBoundary :
      List String

open ConformalSpinFromCMReceipt public

canonicalConformalSpinFromCMReceipt :
  ConformalSpinFromCMReceipt
canonicalConformalSpinFromCMReceipt =
  record
    { finiteDHRAbelianReceipt =
        DHR.canonicalFiniteDHRAbelianReconstructionReceipt
    ; braidingMorphismReceipt =
        Braiding.canonicalBraidingMorphismReceipt
    ; lanes =
        canonicalCMConformalSpinLanes
    ; lanesAreCanonical =
        refl
    ; p2Prime =
        2
    ; p2PrimeIsTwo =
        refl
    ; p2Discriminant =
        "D=-4"
    ; p2DiscriminantIsD-4 =
        refl
    ; p2SpinNumeratorOverFour =
        4
    ; p2SpinNumeratorOverFourIsFour =
        refl
    ; p2SpinDenominator =
        4
    ; p2SpinDenominatorIsFour =
        refl
    ; p2SpinLabel =
        "h=1 mod Z"
    ; p2SpinLabelIsOneModuloIntegers =
        refl
    ; p3Prime =
        3
    ; p3PrimeIsThree =
        refl
    ; p3Discriminant =
        "D=-3"
    ; p3DiscriminantIsD-3 =
        refl
    ; p3SpinNumeratorOverFour =
        3
    ; p3SpinNumeratorOverFourIsThree =
        refl
    ; p3SpinDenominator =
        4
    ; p3SpinDenominatorIsFour =
        refl
    ; p3SpinLabel =
        "h=3/4 mod Z"
    ; p3SpinLabelIsThreeFourthsModuloIntegers =
        refl
    ; p5Prime =
        5
    ; p5PrimeIsFive =
        refl
    ; p5Discriminant =
        "D=-7"
    ; p5DiscriminantIsD-7 =
        refl
    ; p5SpinNumeratorOverFour =
        7
    ; p5SpinNumeratorOverFourIsSeven =
        refl
    ; p5SpinDenominator =
        4
    ; p5SpinDenominatorIsFour =
        refl
    ; p5SpinLabel =
        "h=7/4 mod Z"
    ; p5SpinLabelIsSevenFourthsModuloIntegers =
        refl
    ; p2FermionHalfDiagnostic =
        notExpectedFermionSpinOneHalfForQuarks
    ; p2FermionHalfDiagnosticIsNegative =
        refl
    ; p3FermionHalfDiagnostic =
        notExpectedFermionSpinOneHalfForQuarks
    ; p3FermionHalfDiagnosticIsNegative =
        refl
    ; p5FermionHalfDiagnostic =
        notExpectedFermionSpinOneHalfForQuarks
    ; p5FermionHalfDiagnosticIsNegative =
        refl
    ; diagnosticStatement =
        cmConformalSpinDiagnosticLabel
    ; diagnosticStatementIsCanonical =
        refl
    ; primeLaneCMCharactersAreDirectQuarkFields =
        false
    ; primeLaneCMCharactersAreDirectQuarkFieldsIsFalse =
        refl
    ; quarkFermionSpinOneHalfMatched =
        false
    ; quarkFermionSpinOneHalfMatchedIsFalse =
        refl
    ; fullStandardModelMatterPromoted =
        false
    ; fullStandardModelMatterPromotedIsFalse =
        refl
    ; fullStandardModelGaugePromoted =
        false
    ; fullStandardModelGaugePromotedIsFalse =
        refl
    ; fullDHRDRReconstructionPromoted =
        false
    ; fullDHRDRReconstructionPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; boundaryStatement =
        primeLaneCMCharacterBoundaryLabel
    ; boundaryStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Prime-lane CM conformal-spin labels computed over denominator four: p2=4/4, p3=3/4, p5=7/4"
        ∷ "The corresponding discriminants are D=-4, D=-3, and D=-7"
        ∷ "These labels are not the expected h=1/2 fermion conformal spin for direct fundamental quark fields"
        ∷ "Finite prime-lane CM characters remain diagnostic abelian sectors, not direct quark fields"
        ∷ "All full/SM/DHR promotion flags remain false"
        ∷ []
    }

cmConformalSpinReceiptComputesP2AsOne :
  p2SpinNumeratorOverFour canonicalConformalSpinFromCMReceipt ≡ 4
cmConformalSpinReceiptComputesP2AsOne =
  refl

cmConformalSpinReceiptComputesP3AsThreeFourths :
  p3SpinNumeratorOverFour canonicalConformalSpinFromCMReceipt ≡ 3
cmConformalSpinReceiptComputesP3AsThreeFourths =
  refl

cmConformalSpinReceiptComputesP5AsSevenFourths :
  p5SpinNumeratorOverFour canonicalConformalSpinFromCMReceipt ≡ 7
cmConformalSpinReceiptComputesP5AsSevenFourths =
  refl

cmConformalSpinReceiptRejectsDirectQuarkFieldPromotion :
  primeLaneCMCharactersAreDirectQuarkFields
    canonicalConformalSpinFromCMReceipt
  ≡
  false
cmConformalSpinReceiptRejectsDirectQuarkFieldPromotion =
  refl

cmConformalSpinReceiptKeepsSMMatterPromotionFalse :
  fullStandardModelMatterPromoted canonicalConformalSpinFromCMReceipt
  ≡
  false
cmConformalSpinReceiptKeepsSMMatterPromotionFalse =
  refl

cmConformalSpinReceiptKeepsGSMPromotionFalse :
  gDHREqualsGSMPromoted canonicalConformalSpinFromCMReceipt
  ≡
  false
cmConformalSpinReceiptKeepsGSMPromotionFalse =
  refl
