module DASHI.Physics.Closure.YMKPThresholdCorrectionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- YM KP analytic threshold correction receipt.
--
-- This receipt supersedes the older carrier-side 13.64/7.64 bookkeeping for
-- the physical constants surface.  It records the corrected physical c_min,
-- KP convergence and strict-absorption beta thresholds, the beta=6 physical
-- comparison, and the Balaban gap still needed before a continuum RG flow can
-- be consumed.  It does not promote continuum Yang-Mills or Clay.

data YMKPThresholdCorrectionStatus : Set where
  ymKPThresholdCorrectionRecorded_noClayPromotion :
    YMKPThresholdCorrectionStatus

data YMThresholdCorrectionDatum : Set where
  cMinPhysicalRecorded :
    YMThresholdCorrectionDatum

  pBranchingRecorded :
    YMThresholdCorrectionDatum

  aWeightRecorded :
    YMThresholdCorrectionDatum

  kpConvergenceThresholdRecorded :
    YMThresholdCorrectionDatum

  kpStrictAbsorptionThresholdRecorded :
    YMThresholdCorrectionDatum

  physicalBetaRecorded :
    YMThresholdCorrectionDatum

  balabanConvergenceGapRecorded :
    YMThresholdCorrectionDatum

  balabanStrictAbsorptionGapRecorded :
    YMThresholdCorrectionDatum

  ratioAtPhysicalBetaRecorded :
    YMThresholdCorrectionDatum

  contourActionSuppressionRecorded :
    YMThresholdCorrectionDatum

  allDiameterGeometricBoundRecorded :
    YMThresholdCorrectionDatum

canonicalYMThresholdCorrectionData :
  List YMThresholdCorrectionDatum
canonicalYMThresholdCorrectionData =
  cMinPhysicalRecorded
  ∷ pBranchingRecorded
  ∷ aWeightRecorded
  ∷ kpConvergenceThresholdRecorded
  ∷ kpStrictAbsorptionThresholdRecorded
  ∷ physicalBetaRecorded
  ∷ balabanConvergenceGapRecorded
  ∷ balabanStrictAbsorptionGapRecorded
  ∷ ratioAtPhysicalBetaRecorded
  ∷ contourActionSuppressionRecorded
  ∷ allDiameterGeometricBoundRecorded
  ∷ []

data YMThresholdCorrectionNonClaim : Set where
  physicalBetaDoesNotMeetKPConvergence :
    YMThresholdCorrectionNonClaim

  physicalBetaDoesNotMeetKPStrictAbsorption :
    YMThresholdCorrectionNonClaim

  balabanRGStillMustRaiseEffectiveBeta :
    YMThresholdCorrectionNonClaim

  continuumRGFlowBridgeStillOpen :
    YMThresholdCorrectionNonClaim

  betaTimesActionNotSuppressionRoute :
    YMThresholdCorrectionNonClaim

  geometricBoundConditionalOnStrictAbsorber :
    YMThresholdCorrectionNonClaim

  noClayYangMillsPromotion :
    YMThresholdCorrectionNonClaim

canonicalYMThresholdCorrectionNonClaims :
  List YMThresholdCorrectionNonClaim
canonicalYMThresholdCorrectionNonClaims =
  physicalBetaDoesNotMeetKPConvergence
  ∷ physicalBetaDoesNotMeetKPStrictAbsorption
  ∷ balabanRGStillMustRaiseEffectiveBeta
  ∷ continuumRGFlowBridgeStillOpen
  ∷ betaTimesActionNotSuppressionRoute
  ∷ geometricBoundConditionalOnStrictAbsorber
  ∷ noClayYangMillsPromotion
  ∷ []

data YMKPGeometricTailLaw : Set where
  countAndActivityImplyGeometricTail :
    YMKPGeometricTailLaw

data YMKPThresholdCorrectionPromotion : Set where

ymKPThresholdCorrectionPromotionImpossibleHere :
  YMKPThresholdCorrectionPromotion →
  ⊥
ymKPThresholdCorrectionPromotionImpossibleHere ()

cMinPhysicalNumerator :
  Nat
cMinPhysicalNumerator =
  242

cMinPhysicalDenominator :
  Nat
cMinPhysicalDenominator =
  1000

pBranching :
  Nat
pBranching =
  7

aWeightNumerator :
  Nat
aWeightNumerator =
  50

aWeightDenominator :
  Nat
aWeightDenominator =
  100

betaKPConvergenceNumerator :
  Nat
betaKPConvergenceNumerator =
  1011

betaKPConvergenceDenominator :
  Nat
betaKPConvergenceDenominator =
  100

betaKPStrictAbsorptionNumerator :
  Nat
betaKPStrictAbsorptionNumerator =
  1297

betaKPStrictAbsorptionDenominator :
  Nat
betaKPStrictAbsorptionDenominator =
  100

betaPhysicalNumerator :
  Nat
betaPhysicalNumerator =
  600

betaPhysicalDenominator :
  Nat
betaPhysicalDenominator =
  100

balabanConvergenceGapNumerator :
  Nat
balabanConvergenceGapNumerator =
  411

balabanConvergenceGapDenominator :
  Nat
balabanConvergenceGapDenominator =
  100

balabanStrictAbsorptionGapNumerator :
  Nat
balabanStrictAbsorptionGapNumerator =
  697

balabanStrictAbsorptionGapDenominator :
  Nat
balabanStrictAbsorptionGapDenominator =
  100

rAtBeta6Numerator :
  Nat
rAtBeta6Numerator =
  270

rAtBeta6Denominator :
  Nat
rAtBeta6Denominator =
  100

betaPhysicalPlusConvergenceGapIsKPConvergence :
  betaPhysicalNumerator + balabanConvergenceGapNumerator
  ≡
  betaKPConvergenceNumerator
betaPhysicalPlusConvergenceGapIsKPConvergence =
  refl

betaPhysicalPlusStrictGapIsKPStrictAbsorption :
  betaPhysicalNumerator + balabanStrictAbsorptionGapNumerator
  ≡
  betaKPStrictAbsorptionNumerator
betaPhysicalPlusStrictGapIsKPStrictAbsorption =
  refl

thresholdCorrectionStatement :
  String
thresholdCorrectionStatement =
  "Corrected YM KP threshold constants: c_min_physical=0.242, p=7, a=0.5, beta_KP_convergence=10.11, beta_KP_strict_absorption=12.97, beta_physical=6.0, Balaban gaps 4.11 and 6.97, and r(beta=6)=2.70."

thresholdCorrectionBoundaryStatement :
  String
thresholdCorrectionBoundaryStatement =
  "At physical beta=6.0 the KP threshold is divergent for both convergence and strict absorption; Balaban RG must increase effective beta, and the continuum RG-flow bridge remains open."

contourSuppressionStatement :
  String
contourSuppressionStatement =
  "KP activity suppression is recorded as |z Gamma| <= C0^|Gamma| exp(-beta*c_min*|Gamma|), not as the large-beta inequality |exp(-beta S)-1| <= beta*S."

geometricTailStatement :
  String
geometricTailStatement =
  "All-diameter geometric bound with p=7 and a=0.5: if count_n <= C*p^n and |z Gamma| <= C0^|Gamma| exp(-beta*c_min*|Gamma|), then the a-weighted tail is bounded by C*r/(1-r), where r = p*C0*exp(a-beta*c_min), provided r < 1."

strictAbsorberStatement :
  String
strictAbsorberStatement =
  "Strict KP absorption requires the geometric tail bound plus the strict absorber condition; the physical beta bridge remains open and no Clay promotion follows."

noClayThresholdCorrectionStatement :
  String
noClayThresholdCorrectionStatement =
  "This threshold correction is analytic bookkeeping only; it does not promote continuum Yang-Mills, a mass gap, or Clay Yang-Mills."

record YMKPThresholdCorrectionReceipt : Setω where
  field
    status :
      YMKPThresholdCorrectionStatus

    statusIsCanonical :
      status ≡ ymKPThresholdCorrectionRecorded_noClayPromotion

    c_min_physicalNumerator :
      Nat

    c_min_physicalNumeratorIs242 :
      c_min_physicalNumerator ≡ cMinPhysicalNumerator

    c_min_physicalDenominator :
      Nat

    c_min_physicalDenominatorIs1000 :
      c_min_physicalDenominator ≡ cMinPhysicalDenominator

    p_branching :
      Nat

    p_branchingIs7 :
      p_branching ≡ pBranching

    a_weightNumerator :
      Nat

    a_weightNumeratorIs50 :
      a_weightNumerator ≡ aWeightNumerator

    a_weightDenominator :
      Nat

    a_weightDenominatorIs100 :
      a_weightDenominator ≡ aWeightDenominator

    beta_KP_convergenceNumerator :
      Nat

    beta_KP_convergenceNumeratorIs1011 :
      beta_KP_convergenceNumerator ≡ betaKPConvergenceNumerator

    beta_KP_convergenceDenominator :
      Nat

    beta_KP_convergenceDenominatorIs100 :
      beta_KP_convergenceDenominator ≡ betaKPConvergenceDenominator

    beta_KP_strict_absorptionNumerator :
      Nat

    beta_KP_strict_absorptionNumeratorIs1297 :
      beta_KP_strict_absorptionNumerator
      ≡
      betaKPStrictAbsorptionNumerator

    beta_KP_strict_absorptionDenominator :
      Nat

    beta_KP_strict_absorptionDenominatorIs100 :
      beta_KP_strict_absorptionDenominator
      ≡
      betaKPStrictAbsorptionDenominator

    beta_physicalNumerator :
      Nat

    beta_physicalNumeratorIs600 :
      beta_physicalNumerator ≡ betaPhysicalNumerator

    beta_physicalDenominator :
      Nat

    beta_physicalDenominatorIs100 :
      beta_physicalDenominator ≡ betaPhysicalDenominator

    balabanConvergenceGapNumeratorRecorded :
      Nat

    balabanConvergenceGapNumeratorRecordedIs411 :
      balabanConvergenceGapNumeratorRecorded
      ≡
      balabanConvergenceGapNumerator

    balabanConvergenceGapDenominatorRecorded :
      Nat

    balabanConvergenceGapDenominatorRecordedIs100 :
      balabanConvergenceGapDenominatorRecorded
      ≡
      balabanConvergenceGapDenominator

    balabanStrictAbsorptionGapNumeratorRecorded :
      Nat

    balabanStrictAbsorptionGapNumeratorRecordedIs697 :
      balabanStrictAbsorptionGapNumeratorRecorded
      ≡
      balabanStrictAbsorptionGapNumerator

    balabanStrictAbsorptionGapDenominatorRecorded :
      Nat

    balabanStrictAbsorptionGapDenominatorRecordedIs100 :
      balabanStrictAbsorptionGapDenominatorRecorded
      ≡
      balabanStrictAbsorptionGapDenominator

    r_at_beta6Numerator :
      Nat

    r_at_beta6NumeratorIs270 :
      r_at_beta6Numerator ≡ rAtBeta6Numerator

    r_at_beta6Denominator :
      Nat

    r_at_beta6DenominatorIs100 :
      r_at_beta6Denominator ≡ rAtBeta6Denominator

    betaPhysicalPlusConvergenceGap :
      betaPhysicalNumerator + balabanConvergenceGapNumerator
      ≡
      betaKPConvergenceNumerator

    betaPhysicalPlusStrictAbsorptionGap :
      betaPhysicalNumerator + balabanStrictAbsorptionGapNumerator
      ≡
      betaKPStrictAbsorptionNumerator

    geometricTailLaw :
      YMKPGeometricTailLaw

    geometricTailLawIsCanonical :
      geometricTailLaw ≡ countAndActivityImplyGeometricTail

    count_nBoundedByCPToN :
      Bool

    count_nBoundedByCPToNIsTrue :
      count_nBoundedByCPToN ≡ true

    activityBoundUsesContourActionSuppression :
      Bool

    activityBoundUsesContourActionSuppressionIsTrue :
      activityBoundUsesContourActionSuppression ≡ true

    betaTimesActionSuppressionUsed :
      Bool

    betaTimesActionSuppressionUsedIsFalse :
      betaTimesActionSuppressionUsed ≡ false

    rFormulaRecorded :
      Bool

    rFormulaRecordedIsTrue :
      rFormulaRecorded ≡ true

    geometricSumBoundRecorded :
      Bool

    geometricSumBoundRecordedIsTrue :
      geometricSumBoundRecorded ≡ true

    strictAbsorberConditionRequired :
      Bool

    strictAbsorberConditionRequiredIsTrue :
      strictAbsorberConditionRequired ≡ true

    physicalBetaBridgeOpen :
      Bool

    physicalBetaBridgeOpenIsTrue :
      physicalBetaBridgeOpen ≡ true

    physicalBetaKPDivergent :
      Bool

    physicalBetaKPDivergentIsTrue :
      physicalBetaKPDivergent ≡ true

    balabanRGMustIncreaseEffectiveBeta :
      Bool

    balabanRGMustIncreaseEffectiveBetaIsTrue :
      balabanRGMustIncreaseEffectiveBeta ≡ true

    continuumRGFlowBridgeOpen :
      Bool

    continuumRGFlowBridgeOpenIsTrue :
      continuumRGFlowBridgeOpen ≡ true

    continuumYangMillsPromoted :
      Bool

    continuumYangMillsPromotedIsFalse :
      continuumYangMillsPromoted ≡ false

    clayYMPromoted :
      Bool

    clayYMPromotedIsFalse :
      clayYMPromoted ≡ false

    dataRecorded :
      List YMThresholdCorrectionDatum

    dataRecordedAreCanonical :
      dataRecorded ≡ canonicalYMThresholdCorrectionData

    nonClaims :
      List YMThresholdCorrectionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalYMThresholdCorrectionNonClaims

    correctionBoundary :
      String

    correctionBoundaryIsCanonical :
      correctionBoundary ≡ thresholdCorrectionStatement

    divergenceBoundary :
      String

    divergenceBoundaryIsCanonical :
      divergenceBoundary ≡ thresholdCorrectionBoundaryStatement

    contourSuppressionBoundary :
      String

    contourSuppressionBoundaryIsCanonical :
      contourSuppressionBoundary ≡ contourSuppressionStatement

    geometricTailBoundary :
      String

    geometricTailBoundaryIsCanonical :
      geometricTailBoundary ≡ geometricTailStatement

    strictAbsorberBoundary :
      String

    strictAbsorberBoundaryIsCanonical :
      strictAbsorberBoundary ≡ strictAbsorberStatement

    noClayBoundary :
      String

    noClayBoundaryIsCanonical :
      noClayBoundary ≡ noClayThresholdCorrectionStatement

    promotionFlags :
      List YMKPThresholdCorrectionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open YMKPThresholdCorrectionReceipt public

canonicalYMKPThresholdCorrectionReceipt :
  YMKPThresholdCorrectionReceipt
canonicalYMKPThresholdCorrectionReceipt =
  record
    { status =
        ymKPThresholdCorrectionRecorded_noClayPromotion
    ; statusIsCanonical =
        refl
    ; c_min_physicalNumerator =
        cMinPhysicalNumerator
    ; c_min_physicalNumeratorIs242 =
        refl
    ; c_min_physicalDenominator =
        cMinPhysicalDenominator
    ; c_min_physicalDenominatorIs1000 =
        refl
    ; p_branching =
        pBranching
    ; p_branchingIs7 =
        refl
    ; a_weightNumerator =
        aWeightNumerator
    ; a_weightNumeratorIs50 =
        refl
    ; a_weightDenominator =
        aWeightDenominator
    ; a_weightDenominatorIs100 =
        refl
    ; beta_KP_convergenceNumerator =
        betaKPConvergenceNumerator
    ; beta_KP_convergenceNumeratorIs1011 =
        refl
    ; beta_KP_convergenceDenominator =
        betaKPConvergenceDenominator
    ; beta_KP_convergenceDenominatorIs100 =
        refl
    ; beta_KP_strict_absorptionNumerator =
        betaKPStrictAbsorptionNumerator
    ; beta_KP_strict_absorptionNumeratorIs1297 =
        refl
    ; beta_KP_strict_absorptionDenominator =
        betaKPStrictAbsorptionDenominator
    ; beta_KP_strict_absorptionDenominatorIs100 =
        refl
    ; beta_physicalNumerator =
        betaPhysicalNumerator
    ; beta_physicalNumeratorIs600 =
        refl
    ; beta_physicalDenominator =
        betaPhysicalDenominator
    ; beta_physicalDenominatorIs100 =
        refl
    ; balabanConvergenceGapNumeratorRecorded =
        balabanConvergenceGapNumerator
    ; balabanConvergenceGapNumeratorRecordedIs411 =
        refl
    ; balabanConvergenceGapDenominatorRecorded =
        balabanConvergenceGapDenominator
    ; balabanConvergenceGapDenominatorRecordedIs100 =
        refl
    ; balabanStrictAbsorptionGapNumeratorRecorded =
        balabanStrictAbsorptionGapNumerator
    ; balabanStrictAbsorptionGapNumeratorRecordedIs697 =
        refl
    ; balabanStrictAbsorptionGapDenominatorRecorded =
        balabanStrictAbsorptionGapDenominator
    ; balabanStrictAbsorptionGapDenominatorRecordedIs100 =
        refl
    ; r_at_beta6Numerator =
        rAtBeta6Numerator
    ; r_at_beta6NumeratorIs270 =
        refl
    ; r_at_beta6Denominator =
        rAtBeta6Denominator
    ; r_at_beta6DenominatorIs100 =
        refl
    ; betaPhysicalPlusConvergenceGap =
        betaPhysicalPlusConvergenceGapIsKPConvergence
    ; betaPhysicalPlusStrictAbsorptionGap =
        betaPhysicalPlusStrictGapIsKPStrictAbsorption
    ; geometricTailLaw =
        countAndActivityImplyGeometricTail
    ; geometricTailLawIsCanonical =
        refl
    ; count_nBoundedByCPToN =
        true
    ; count_nBoundedByCPToNIsTrue =
        refl
    ; activityBoundUsesContourActionSuppression =
        true
    ; activityBoundUsesContourActionSuppressionIsTrue =
        refl
    ; betaTimesActionSuppressionUsed =
        false
    ; betaTimesActionSuppressionUsedIsFalse =
        refl
    ; rFormulaRecorded =
        true
    ; rFormulaRecordedIsTrue =
        refl
    ; geometricSumBoundRecorded =
        true
    ; geometricSumBoundRecordedIsTrue =
        refl
    ; strictAbsorberConditionRequired =
        true
    ; strictAbsorberConditionRequiredIsTrue =
        refl
    ; physicalBetaBridgeOpen =
        true
    ; physicalBetaBridgeOpenIsTrue =
        refl
    ; physicalBetaKPDivergent =
        true
    ; physicalBetaKPDivergentIsTrue =
        refl
    ; balabanRGMustIncreaseEffectiveBeta =
        true
    ; balabanRGMustIncreaseEffectiveBetaIsTrue =
        refl
    ; continuumRGFlowBridgeOpen =
        true
    ; continuumRGFlowBridgeOpenIsTrue =
        refl
    ; continuumYangMillsPromoted =
        false
    ; continuumYangMillsPromotedIsFalse =
        refl
    ; clayYMPromoted =
        false
    ; clayYMPromotedIsFalse =
        refl
    ; dataRecorded =
        canonicalYMThresholdCorrectionData
    ; dataRecordedAreCanonical =
        refl
    ; nonClaims =
        canonicalYMThresholdCorrectionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; correctionBoundary =
        thresholdCorrectionStatement
    ; correctionBoundaryIsCanonical =
        refl
    ; divergenceBoundary =
        thresholdCorrectionBoundaryStatement
    ; divergenceBoundaryIsCanonical =
        refl
    ; contourSuppressionBoundary =
        contourSuppressionStatement
    ; contourSuppressionBoundaryIsCanonical =
        refl
    ; geometricTailBoundary =
        geometricTailStatement
    ; geometricTailBoundaryIsCanonical =
        refl
    ; strictAbsorberBoundary =
        strictAbsorberStatement
    ; strictAbsorberBoundaryIsCanonical =
        refl
    ; noClayBoundary =
        noClayThresholdCorrectionStatement
    ; noClayBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

ymKPThresholdPhysicalBetaDivergent :
  physicalBetaKPDivergent canonicalYMKPThresholdCorrectionReceipt ≡ true
ymKPThresholdPhysicalBetaDivergent =
  refl

ymKPThresholdBalabanMustIncreaseBeta :
  balabanRGMustIncreaseEffectiveBeta canonicalYMKPThresholdCorrectionReceipt
  ≡
  true
ymKPThresholdBalabanMustIncreaseBeta =
  refl

ymKPThresholdContinuumRGBridgeOpen :
  continuumRGFlowBridgeOpen canonicalYMKPThresholdCorrectionReceipt ≡ true
ymKPThresholdContinuumRGBridgeOpen =
  refl

ymKPThresholdNoClayPromotion :
  clayYMPromoted canonicalYMKPThresholdCorrectionReceipt ≡ false
ymKPThresholdNoClayPromotion =
  refl
