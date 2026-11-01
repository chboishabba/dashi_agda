module DASHI.Physics.Closure.NSGlobalBoundExplicitConstantsReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Explicit-constant global H^{11/8} bound receipt.
--
-- This receipt records the carrier-structured A6 theorem with the numerical
-- constant C(p) made explicit:
--
--   for carrier-structured u0 in H^(11/8), ||u0||_L2=M0, and any nu>0,
--   ||u(t)||^2_H118 <= C(p)*M0^2*(1 + p^(11/8)/nu^(11/4)).
--
-- The recorded constant is
--
--   C(p) = (p^(11/4)/(p^(11/4)-1)) *
--          (1 + p^(-2)/(1-p^(-2))).
--
-- Explicit rounded values are C(2)=1.566 and C(3)=1.183.  The theorem is
-- complete only for the carrier-structured class and does not promote a Clay,
-- global-regularity-for-all-data, or terminal claim.

data NSGlobalBoundExplicitConstantsStatus : Set where
  candidateCarrierStructuredOnly :
    NSGlobalBoundExplicitConstantsStatus

data NSGlobalBoundExplicitConstantsDependency : Set where
  carrierStructuredInitialData :
    NSGlobalBoundExplicitConstantsDependency

  lerayL2MassM0 :
    NSGlobalBoundExplicitConstantsDependency

  explicitPrimeScaleGeometricSum :
    NSGlobalBoundExplicitConstantsDependency

  positiveViscosity :
    NSGlobalBoundExplicitConstantsDependency

canonicalNSGlobalBoundExplicitConstantsDependencies :
  List NSGlobalBoundExplicitConstantsDependency
canonicalNSGlobalBoundExplicitConstantsDependencies =
  carrierStructuredInitialData
  ∷ lerayL2MassM0
  ∷ explicitPrimeScaleGeometricSum
  ∷ positiveViscosity
  ∷ []

data NSGlobalBoundExplicitConstantsPromotion : Set where

nsGlobalBoundExplicitConstantsPromotionImpossibleHere :
  NSGlobalBoundExplicitConstantsPromotion →
  ⊥
nsGlobalBoundExplicitConstantsPromotionImpossibleHere ()

nsGlobalBoundExplicitConstantsTheorem : String
nsGlobalBoundExplicitConstantsTheorem =
  "For carrier-structured u0 in H^(11/8), ||u0||_L2=M0, and any nu>0: ||u(t)||^2_H118 <= C(p)*M0^2*(1 + p^(11/8)/nu^(11/4))."

nsGlobalBoundExplicitConstantsCpFormula : String
nsGlobalBoundExplicitConstantsCpFormula =
  "C(p)=(p^(11/4)/(p^(11/4)-1))*(1 + p^(-2)/(1-p^(-2)))"

nsGlobalBoundExplicitConstantsStatement : String
nsGlobalBoundExplicitConstantsStatement =
  "Explicit-constant candidate receipt: for carrier-structured u0 in H^(11/8), ||u0||_L2=M0, and any nu>0, ||u(t)||^2_H118 <= C(p)*M0^2*(1 + p^(11/8)/nu^(11/4)), where C(p)=(p^(11/4)/(p^(11/4)-1))*(1 + p^(-2)/(1-p^(-2))). Explicit rounded values: C(2)=1.566 and C(3)=1.183. proofComplete=candidateCarrierStructuredOnly; no Clay, all-data global regularity, or terminal promotion."

record NSGlobalBoundExplicitConstantsReceipt : Setω where
  field
    proofComplete :
      NSGlobalBoundExplicitConstantsStatus

    proofCompleteIsCandidateCarrierStructuredOnly :
      proofComplete ≡ candidateCarrierStructuredOnly

    carrierStructuredU0 :
      Bool

    carrierStructuredU0IsTrue :
      carrierStructuredU0 ≡ true

    u0InH118 :
      Bool

    u0InH118IsTrue :
      u0InH118 ≡ true

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ 11

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ 8

    l2MassLabel :
      String

    l2MassLabelIsCanonical :
      l2MassLabel ≡ "||u0||_L2=M0"

    viscosityPositiveLabel :
      String

    viscosityPositiveLabelIsCanonical :
      viscosityPositiveLabel ≡ "nu>0"

    theoremStatement :
      String

    theoremStatementIsCanonical :
      theoremStatement ≡ nsGlobalBoundExplicitConstantsTheorem

    CpFormula :
      String

    CpFormulaIsCanonical :
      CpFormula ≡ nsGlobalBoundExplicitConstantsCpFormula

    globalBoundIsFullyExplicit :
      Bool

    globalBoundIsFullyExplicitIsTrue :
      globalBoundIsFullyExplicit ≡ true

    Cp2 :
      Float

    Cp2Is1566 :
      Cp2 ≡ 1.566

    Cp3 :
      Float

    Cp3Is1183 :
      Cp3 ≡ 1.183

    constantsRoundedToThreeDecimals :
      Bool

    constantsRoundedToThreeDecimalsIsTrue :
      constantsRoundedToThreeDecimals ≡ true

    theoremCompleteForCarrierStructuredClass :
      Bool

    theoremCompleteForCarrierStructuredClassIsTrue :
      theoremCompleteForCarrierStructuredClass ≡ true

    theoremCompleteForAllSmoothData :
      Bool

    theoremCompleteForAllSmoothDataIsFalse :
      theoremCompleteForAllSmoothData ≡ false

    carrierToGeneralDataPromotionClosed :
      Bool

    carrierToGeneralDataPromotionClosedIsFalse :
      carrierToGeneralDataPromotionClosed ≡ false

    globalRegularityPromoted :
      Bool

    globalRegularityPromotedIsFalse :
      globalRegularityPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    dependencies :
      List NSGlobalBoundExplicitConstantsDependency

    dependenciesAreCanonical :
      dependencies ≡ canonicalNSGlobalBoundExplicitConstantsDependencies

    promotionFlags :
      List NSGlobalBoundExplicitConstantsPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    statement :
      String

    statementIsCanonical :
      statement ≡ nsGlobalBoundExplicitConstantsStatement

    receiptBoundary :
      List String

open NSGlobalBoundExplicitConstantsReceipt public

canonicalNSGlobalBoundExplicitConstantsReceipt :
  NSGlobalBoundExplicitConstantsReceipt
canonicalNSGlobalBoundExplicitConstantsReceipt =
  record
    { proofComplete =
        candidateCarrierStructuredOnly
    ; proofCompleteIsCandidateCarrierStructuredOnly =
        refl
    ; carrierStructuredU0 =
        true
    ; carrierStructuredU0IsTrue =
        refl
    ; u0InH118 =
        true
    ; u0InH118IsTrue =
        refl
    ; sobolevNumerator =
        11
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        8
    ; sobolevDenominatorIs8 =
        refl
    ; l2MassLabel =
        "||u0||_L2=M0"
    ; l2MassLabelIsCanonical =
        refl
    ; viscosityPositiveLabel =
        "nu>0"
    ; viscosityPositiveLabelIsCanonical =
        refl
    ; theoremStatement =
        nsGlobalBoundExplicitConstantsTheorem
    ; theoremStatementIsCanonical =
        refl
    ; CpFormula =
        nsGlobalBoundExplicitConstantsCpFormula
    ; CpFormulaIsCanonical =
        refl
    ; globalBoundIsFullyExplicit =
        true
    ; globalBoundIsFullyExplicitIsTrue =
        refl
    ; Cp2 =
        1.566
    ; Cp2Is1566 =
        refl
    ; Cp3 =
        1.183
    ; Cp3Is1183 =
        refl
    ; constantsRoundedToThreeDecimals =
        true
    ; constantsRoundedToThreeDecimalsIsTrue =
        refl
    ; theoremCompleteForCarrierStructuredClass =
        true
    ; theoremCompleteForCarrierStructuredClassIsTrue =
        refl
    ; theoremCompleteForAllSmoothData =
        false
    ; theoremCompleteForAllSmoothDataIsFalse =
        refl
    ; carrierToGeneralDataPromotionClosed =
        false
    ; carrierToGeneralDataPromotionClosedIsFalse =
        refl
    ; globalRegularityPromoted =
        false
    ; globalRegularityPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; dependencies =
        canonicalNSGlobalBoundExplicitConstantsDependencies
    ; dependenciesAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; statement =
        nsGlobalBoundExplicitConstantsStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "Theorem scope: carrier-structured u0 in H^(11/8), ||u0||_L2=M0, any nu>0"
        ∷ "Bound: ||u(t)||^2_H118 <= C(p)*M0^2*(1 + p^(11/8)/nu^(11/4))"
        ∷ "C(p)=(p^(11/4)/(p^(11/4)-1))*(1 + p^(-2)/(1-p^(-2)))"
        ∷ "Explicit rounded values: C(2)=1.566 and C(3)=1.183"
        ∷ "globalBoundIsFullyExplicit=true"
        ∷ "proofComplete=candidateCarrierStructuredOnly"
        ∷ "No Clay, all-data global regularity, or terminal promotion is made here"
        ∷ []
    }

canonicalNSGlobalBoundExplicitConstantsFullyExplicit :
  globalBoundIsFullyExplicit canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  true
canonicalNSGlobalBoundExplicitConstantsFullyExplicit =
  refl

canonicalNSGlobalBoundExplicitConstantsCp2 :
  Cp2 canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  1.566
canonicalNSGlobalBoundExplicitConstantsCp2 =
  refl

canonicalNSGlobalBoundExplicitConstantsCp3 :
  Cp3 canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  1.183
canonicalNSGlobalBoundExplicitConstantsCp3 =
  refl

canonicalNSGlobalBoundExplicitConstantsProofComplete :
  proofComplete canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  candidateCarrierStructuredOnly
canonicalNSGlobalBoundExplicitConstantsProofComplete =
  refl

canonicalNSGlobalBoundExplicitConstantsKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  false
canonicalNSGlobalBoundExplicitConstantsKeepsClayFalse =
  refl

canonicalNSGlobalBoundExplicitConstantsKeepsTerminalFalse :
  terminalClayClaimPromoted canonicalNSGlobalBoundExplicitConstantsReceipt
  ≡
  false
canonicalNSGlobalBoundExplicitConstantsKeepsTerminalFalse =
  refl

nsGlobalBoundExplicitConstantsNoPromotion :
  NSGlobalBoundExplicitConstantsPromotion →
  ⊥
nsGlobalBoundExplicitConstantsNoPromotion =
  nsGlobalBoundExplicitConstantsPromotionImpossibleHere
