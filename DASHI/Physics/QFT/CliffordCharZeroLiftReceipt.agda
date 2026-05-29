module DASHI.Physics.QFT.CliffordCharZeroLiftReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Characteristic-zero Clifford lift diagnostic receipt.
--
-- This receipt records the p2-lane companion-matrix lift over Z as a
-- diagnostic anyonic statistics surface.  The recorded characteristic-zero
-- lane has characteristic polynomial x^2 + x + 1, roots exp(+-2*pi*i/3),
-- statistics phase exp(2*pi*i/3), and conformal-spin diagnostic h=1/3.
-- It therefore records an anyonic, non-fermionic p2-lane phase and keeps the
-- separate fermion sector requirement open.  It does not promote an exact
-- Standard Model match or G_DHR = G_SM.

data CliffordCharZeroLiftLane : Set where
  p2CompanionMatrixLane :
    CliffordCharZeroLiftLane

data CliffordCharZeroRoot : Set where
  expPlusTwoPiIOverThree :
    CliffordCharZeroRoot

  expMinusTwoPiIOverThree :
    CliffordCharZeroRoot

canonicalCliffordCharZeroRoots :
  List CliffordCharZeroRoot
canonicalCliffordCharZeroRoots =
  expPlusTwoPiIOverThree
  ∷ expMinusTwoPiIOverThree
  ∷ []

data CliffordCharZeroLiftPromotionFlag : Set where

companionMatrixOverZLabel : String
companionMatrixOverZLabel =
  "[[0,1],[1,1]] over Z"

characteristicPolynomialLabel : String
characteristicPolynomialLabel =
  "x^2 + x + 1"

rootPairLabel : String
rootPairLabel =
  "roots exp(+2*pi*i/3) and exp(-2*pi*i/3)"

p2LaneStatisticsPhaseLabel : String
p2LaneStatisticsPhaseLabel =
  "exp(2*pi*i/3)"

p2LaneSpinDiagnosticLabel : String
p2LaneSpinDiagnosticLabel =
  "h=1/3"

anyonicNonFermionicDiagnosticLabel : String
anyonicNonFermionicDiagnosticLabel =
  "p2 lane has anyonic phase exp(2*pi*i/3), not fermionic statistics phase -1"

separateFermionSectorBoundaryLabel : String
separateFermionSectorBoundaryLabel =
  "separate fermion sector remains required; no exact SM or G_DHR promotion"

record CliffordCharZeroLiftReceipt : Setω where
  field
    lane :
      CliffordCharZeroLiftLane

    laneIsP2CompanionMatrix :
      lane ≡ p2CompanionMatrixLane

    baseRing :
      String

    baseRingIsZ :
      baseRing ≡ "Z"

    characteristicZeroLift :
      Bool

    characteristicZeroLiftIsTrue :
      characteristicZeroLift ≡ true

    companionMatrix :
      String

    companionMatrixIsCanonical :
      companionMatrix ≡ companionMatrixOverZLabel

    characteristicPolynomial :
      String

    characteristicPolynomialIsX2PlusXPlus1 :
      characteristicPolynomial ≡ characteristicPolynomialLabel

    roots :
      List CliffordCharZeroRoot

    rootsAreCanonical :
      roots ≡ canonicalCliffordCharZeroRoots

    rootsLabel :
      String

    rootsLabelIsCanonical :
      rootsLabel ≡ rootPairLabel

    p2LaneStatisticsPhase :
      String

    p2LaneStatisticsPhaseIsExpTwoPiIOverThree :
      p2LaneStatisticsPhase ≡ p2LaneStatisticsPhaseLabel

    spinNumerator :
      Nat

    spinNumeratorIsOne :
      spinNumerator ≡ 1

    spinDenominator :
      Nat

    spinDenominatorIsThree :
      spinDenominator ≡ 3

    spinDiagnostic :
      String

    spinDiagnosticIsOneThird :
      spinDiagnostic ≡ p2LaneSpinDiagnosticLabel

    diagnosticStatement :
      String

    diagnosticStatementIsCanonical :
      diagnosticStatement ≡ anyonicNonFermionicDiagnosticLabel

    anyonicNotFermionic :
      Bool

    anyonicNotFermionicIsTrue :
      anyonicNotFermionic ≡ true

    fermionicPrimeLaneStatistics :
      Bool

    fermionicPrimeLaneStatisticsIsFalse :
      fermionicPrimeLaneStatistics ≡ false

    separateFermionSectorRequired :
      Bool

    separateFermionSectorRequiredIsTrue :
      separateFermionSectorRequired ≡ true

    exactStandardModelMatchPromoted :
      Bool

    exactStandardModelMatchPromotedIsFalse :
      exactStandardModelMatchPromoted ≡ false

    gDHREqualsGSMPromoted :
      Bool

    gDHREqualsGSMPromotedIsFalse :
      gDHREqualsGSMPromoted ≡ false

    promotionFlags :
      List CliffordCharZeroLiftPromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open CliffordCharZeroLiftReceipt public

canonicalCliffordCharZeroLiftReceipt :
  CliffordCharZeroLiftReceipt
canonicalCliffordCharZeroLiftReceipt =
  record
    { lane =
        p2CompanionMatrixLane
    ; laneIsP2CompanionMatrix =
        refl
    ; baseRing =
        "Z"
    ; baseRingIsZ =
        refl
    ; characteristicZeroLift =
        true
    ; characteristicZeroLiftIsTrue =
        refl
    ; companionMatrix =
        companionMatrixOverZLabel
    ; companionMatrixIsCanonical =
        refl
    ; characteristicPolynomial =
        characteristicPolynomialLabel
    ; characteristicPolynomialIsX2PlusXPlus1 =
        refl
    ; roots =
        canonicalCliffordCharZeroRoots
    ; rootsAreCanonical =
        refl
    ; rootsLabel =
        rootPairLabel
    ; rootsLabelIsCanonical =
        refl
    ; p2LaneStatisticsPhase =
        p2LaneStatisticsPhaseLabel
    ; p2LaneStatisticsPhaseIsExpTwoPiIOverThree =
        refl
    ; spinNumerator =
        1
    ; spinNumeratorIsOne =
        refl
    ; spinDenominator =
        3
    ; spinDenominatorIsThree =
        refl
    ; spinDiagnostic =
        p2LaneSpinDiagnosticLabel
    ; spinDiagnosticIsOneThird =
        refl
    ; diagnosticStatement =
        anyonicNonFermionicDiagnosticLabel
    ; diagnosticStatementIsCanonical =
        refl
    ; anyonicNotFermionic =
        true
    ; anyonicNotFermionicIsTrue =
        refl
    ; fermionicPrimeLaneStatistics =
        false
    ; fermionicPrimeLaneStatisticsIsFalse =
        refl
    ; separateFermionSectorRequired =
        true
    ; separateFermionSectorRequiredIsTrue =
        refl
    ; exactStandardModelMatchPromoted =
        false
    ; exactStandardModelMatchPromotedIsFalse =
        refl
    ; gDHREqualsGSMPromoted =
        false
    ; gDHREqualsGSMPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        anyonicNonFermionicDiagnosticLabel
        ∷ separateFermionSectorBoundaryLabel
        ∷ []
    }

cliffordCharZeroLiftIsAnyonicNotFermionic :
  anyonicNotFermionic canonicalCliffordCharZeroLiftReceipt
  ≡
  true
cliffordCharZeroLiftIsAnyonicNotFermionic =
  refl

cliffordCharZeroLiftDoesNotProvideFermionicPrimeLaneStatistics :
  fermionicPrimeLaneStatistics canonicalCliffordCharZeroLiftReceipt
  ≡
  false
cliffordCharZeroLiftDoesNotProvideFermionicPrimeLaneStatistics =
  refl

cliffordCharZeroLiftRequiresSeparateFermionSector :
  separateFermionSectorRequired canonicalCliffordCharZeroLiftReceipt
  ≡
  true
cliffordCharZeroLiftRequiresSeparateFermionSector =
  refl

cliffordCharZeroLiftDoesNotPromoteExactSM :
  exactStandardModelMatchPromoted canonicalCliffordCharZeroLiftReceipt
  ≡
  false
cliffordCharZeroLiftDoesNotPromoteExactSM =
  refl

cliffordCharZeroLiftDoesNotPromoteGDHREqualsGSM :
  gDHREqualsGSMPromoted canonicalCliffordCharZeroLiftReceipt
  ≡
  false
cliffordCharZeroLiftDoesNotPromoteGDHREqualsGSM =
  refl
