module DASHI.Physics.ExoticGravity.SuperconductingSourceVsConstitutiveEnhancementBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SUPERCONDUCTING SOURCE VS CONSTITUTIVE ENHANCEMENT
--
-- A larger measured gravity-channel observable can arise because the physical
-- source changed (mass-current/stress-energy), or because the response map from
-- that source to gravity changed.  These are different hypotheses.
------------------------------------------------------------------------

data EnhancementCoordinate : Set where
  sourceChange : EnhancementCoordinate
  constitutiveChange : EnhancementCoordinate
  geometryChange : EnhancementCoordinate
  backgroundChange : EnhancementCoordinate

record SourceConstitutiveFactorization : Set where
  constructor source-constitutive-factorization
  field
    sourceObservable : String
    geometryOperator : String
    standardGravityCoefficient : String
    candidateGravityCoefficient : String
    predictedStandardField : String
    predictedCandidateField : String

canonicalFactorization : SourceConstitutiveFactorization
canonicalFactorization = source-constitutive-factorization
  "J_m or T_0i"
  "K_geometry[J_m]"
  "C_GR"
  "C_SC"
  "B_g^GR = C_GR * K_geometry[J_m]"
  "B_g^SC = C_SC * K_geometry[J_m]"

------------------------------------------------------------------------
-- Independent coordinates.
------------------------------------------------------------------------

record SourceConstitutiveBoundary : Set where
  constructor source-constitutive-boundary
  field
    largerFieldImpliesConstitutiveChange : Bool
    largerFieldImpliesConstitutiveChangeIsFalse :
      largerFieldImpliesConstitutiveChange ≡ false

    superconductingPhaseMayChangeSourceCurrent : Bool
    superconductingPhaseMayChangeSourceCurrentIsTrue :
      superconductingPhaseMayChangeSourceCurrent ≡ true

    sourceChangeEqualsConstitutiveChange : Bool
    sourceChangeEqualsConstitutiveChangeIsFalse :
      sourceChangeEqualsConstitutiveChange ≡ false

    fixedSourceComparisonRequiredForConstitutiveClaim : Bool
    fixedSourceComparisonRequiredForConstitutiveClaimIsTrue :
      fixedSourceComparisonRequiredForConstitutiveClaim ≡ true

canonicalSourceConstitutiveBoundary : SourceConstitutiveBoundary
canonicalSourceConstitutiveBoundary =
  source-constitutive-boundary false refl true refl false refl true refl

------------------------------------------------------------------------
-- Enhancement ratios.
------------------------------------------------------------------------

record EnhancementRatios : Set where
  constructor enhancement-ratios
  field
    sourceRatio : String
    constitutiveRatio : String
    totalFieldRatio : String
    factorization : String

canonicalEnhancementRatios : EnhancementRatios
canonicalEnhancementRatios = enhancement-ratios
  "eta_J = K[J_m^SC] / K[J_m^N]"
  "eta_C = C_SC / C_GR"
  "eta_B = B_g^SC / B_g^N"
  "eta_B = eta_C * eta_J when geometry/background coordinates are matched"

------------------------------------------------------------------------
-- BIDI acquisition router.
------------------------------------------------------------------------

data EnhancementLeaf : Set where
  sourceCurrentLeaf : EnhancementLeaf
  sourceStressEnergyLeaf : EnhancementLeaf
  geometryLeaf : EnhancementLeaf
  phaseMatchedFieldLeaf : EnhancementLeaf
  backgroundClosureLeaf : EnhancementLeaf
  constitutiveRatioLeaf : EnhancementLeaf
  closedEnhancementSplit : EnhancementLeaf

record EnhancementClosureState : Set where
  constructor enhancement-closure-state
  field
    sourceCurrentOwned : Bool
    sourceStressEnergyOwned : Bool
    geometryOwned : Bool
    phaseMatchedFieldOwned : Bool
    backgroundsOwned : Bool
    constitutiveRatioOwned : Bool

firstOpenEnhancementLeaf : EnhancementClosureState → EnhancementLeaf
firstOpenEnhancementLeaf (enhancement-closure-state false s g f b c) = sourceCurrentLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true false g f b c) = sourceStressEnergyLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true true false f b c) = geometryLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true true true false b c) = phaseMatchedFieldLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true true true true false c) = backgroundClosureLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true true true true true false) = constitutiveRatioLeaf
firstOpenEnhancementLeaf (enhancement-closure-state true true true true true true) = closedEnhancementSplit

currentEnhancementFrontier : EnhancementClosureState
currentEnhancementFrontier = enhancement-closure-state false false false false false false

currentFirstOpenEnhancementLeaf : EnhancementLeaf
currentFirstOpenEnhancementLeaf = firstOpenEnhancementLeaf currentEnhancementFrontier

------------------------------------------------------------------------
-- Promotion firewall.
------------------------------------------------------------------------

record ConstitutivePromotionBoundary : Set where
  constructor constitutive-promotion-boundary
  field
    phaseCorrelationAlonePromotesEtaC : Bool
    phaseCorrelationAlonePromotesEtaCIsFalse :
      phaseCorrelationAlonePromotesEtaC ≡ false

    measuredFieldAndSourceBothRequired : Bool
    measuredFieldAndSourceBothRequiredIsTrue :
      measuredFieldAndSourceBothRequired ≡ true

    standardGRPredictionMustUseMeasuredSource : Bool
    standardGRPredictionMustUseMeasuredSourceIsTrue :
      standardGRPredictionMustUseMeasuredSource ≡ true

    etaCIsTerminalDiagnostic : Bool
    etaCIsTerminalDiagnosticIsTrue : etaCIsTerminalDiagnostic ≡ true

canonicalConstitutivePromotionBoundary : ConstitutivePromotionBoundary
canonicalConstitutivePromotionBoundary =
  constitutive-promotion-boundary false refl true refl true refl true refl
