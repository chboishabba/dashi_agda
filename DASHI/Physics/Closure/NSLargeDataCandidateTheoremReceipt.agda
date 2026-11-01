module DASHI.Physics.Closure.NSLargeDataCandidateTheoremReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Large-data Navier-Stokes candidate theorem receipt.
--
-- This receipt records the A6 candidate theorem surface only.  The candidate
-- applies to carrier-structured H^{11/8}(R^3) initial data of arbitrary norm
-- under the additional viscosity condition nu > C_cross, where C_cross is the
-- cross-lane Lipschitz constant supplied by the A5 lane.  The remaining gap is
-- exactly the small-viscosity case: Clay requires any nu > 0, while the
-- current mechanism only absorbs the cross-lane perturbation above C_cross.
--
-- No Clay, arbitrary-viscosity, global-terminal, or terminal-promotion claim is
-- made here.

data NSLargeDataCandidateTheoremStatus : Set where
  candidate :
    NSLargeDataCandidateTheoremStatus

data NSLargeDataProofSketchStep : Set where
  perLaneSystemsGloballyBoundedByDissipationDominance :
    NSLargeDataProofSketchStep

  crossLaneCouplingLipschitzPerturbationBoundedByCcross :
    NSLargeDataProofSketchStep

  viscosityAboveCcrossAbsorbsPerturbationPreservesGlobalBound :
    NSLargeDataProofSketchStep

canonicalNSLargeDataProofSketchSteps :
  List NSLargeDataProofSketchStep
canonicalNSLargeDataProofSketchSteps =
  perLaneSystemsGloballyBoundedByDissipationDominance
  ∷ crossLaneCouplingLipschitzPerturbationBoundedByCcross
  ∷ viscosityAboveCcrossAbsorbsPerturbationPreservesGlobalBound
  ∷ []

data NSLargeDataRemainingGap : Set where
  smallViscosityCase :
    NSLargeDataRemainingGap

data NSLargeDataCandidateTheoremPromotion : Set where

nsLargeDataCandidateTheoremPromotionImpossibleHere :
  NSLargeDataCandidateTheoremPromotion →
  ⊥
nsLargeDataCandidateTheoremPromotionImpossibleHere ()

nsLargeDataSobolevNumerator : Nat
nsLargeDataSobolevNumerator =
  11

nsLargeDataSobolevDenominator : Nat
nsLargeDataSobolevDenominator =
  8

cCrossLabel : String
cCrossLabel =
  "C_cross"

nsLargeDataCandidateTheoremStatement : String
nsLargeDataCandidateTheoremStatement =
  "Candidate theorem: for carrier-structured u0 in H^{11/8}(R^3) of arbitrary norm, and viscosity nu > C_cross, Navier-Stokes has a global smooth solution. Proof sketch: per-lane systems are globally bounded by dissipation dominance; cross-lane coupling is a Lipschitz perturbation bounded by C_cross; if nu > C_cross, dissipation absorbs the cross-lane perturbation and the global bound is preserved. Gap: Clay requires any nu > 0, but this mechanism only covers nu > C_cross; for small nu < C_cross, cross-lane coupling may dominate."

record NSLargeDataCandidateTheoremReceipt : Setω where
  field
    largeDataCandidateTheorem :
      NSLargeDataCandidateTheoremStatus

    largeDataCandidateTheoremIsCandidate :
      largeDataCandidateTheorem ≡ candidate

    carrierStructuredInitialData :
      Bool

    carrierStructuredInitialDataIsTrue :
      carrierStructuredInitialData ≡ true

    arbitraryNormInitialData :
      Bool

    arbitraryNormInitialDataIsTrue :
      arbitraryNormInitialData ≡ true

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ nsLargeDataSobolevNumerator

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ nsLargeDataSobolevDenominator

    ambientSpace :
      String

    ambientSpaceIsR3 :
      ambientSpace ≡ "R^3"

    crossLaneLipschitzConstant :
      String

    crossLaneLipschitzConstantIsCcross :
      crossLaneLipschitzConstant ≡ cCrossLabel

    crossLaneLipschitzConstantFromA5 :
      Bool

    crossLaneLipschitzConstantFromA5IsTrue :
      crossLaneLipschitzConstantFromA5 ≡ true

    viscosityCondition :
      String

    viscosityConditionIsAboveCcross :
      viscosityCondition ≡ "nu > C_cross"

    proofSketchSteps :
      List NSLargeDataProofSketchStep

    proofSketchStepsAreCanonical :
      proofSketchSteps ≡ canonicalNSLargeDataProofSketchSteps

    perLaneDissipationDominanceRecorded :
      Bool

    perLaneDissipationDominanceRecordedIsTrue :
      perLaneDissipationDominanceRecorded ≡ true

    crossLaneLipschitzPerturbationRecorded :
      Bool

    crossLaneLipschitzPerturbationRecordedIsTrue :
      crossLaneLipschitzPerturbationRecorded ≡ true

    viscosityAbsorptionAboveCcrossRecorded :
      Bool

    viscosityAbsorptionAboveCcrossRecordedIsTrue :
      viscosityAbsorptionAboveCcrossRecorded ≡ true

    globalSmoothSolutionUnderViscosityConditionRecorded :
      Bool

    globalSmoothSolutionUnderViscosityConditionRecordedIsTrue :
      globalSmoothSolutionUnderViscosityConditionRecorded ≡ true

    clayNSRequiresAnyNu :
      Bool

    clayNSRequiresAnyNuIsTrue :
      clayNSRequiresAnyNu ≡ true

    remainingGap :
      NSLargeDataRemainingGap

    remainingGapIsSmallViscosityCase :
      remainingGap ≡ smallViscosityCase

    smallNuBelowCcrossMayDominate :
      Bool

    smallNuBelowCcrossMayDominateIsTrue :
      smallNuBelowCcrossMayDominate ≡ true

    arbitraryPositiveViscosityTheoremPromoted :
      Bool

    arbitraryPositiveViscosityTheoremPromotedIsFalse :
      arbitraryPositiveViscosityTheoremPromoted ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    globalTerminalPromotion :
      Bool

    globalTerminalPromotionIsFalse :
      globalTerminalPromotion ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsLargeDataCandidateTheoremStatement

    promotionFlags :
      List NSLargeDataCandidateTheoremPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSLargeDataCandidateTheoremReceipt public

canonicalNSLargeDataCandidateTheoremReceipt :
  NSLargeDataCandidateTheoremReceipt
canonicalNSLargeDataCandidateTheoremReceipt =
  record
    { largeDataCandidateTheorem =
        candidate
    ; largeDataCandidateTheoremIsCandidate =
        refl
    ; carrierStructuredInitialData =
        true
    ; carrierStructuredInitialDataIsTrue =
        refl
    ; arbitraryNormInitialData =
        true
    ; arbitraryNormInitialDataIsTrue =
        refl
    ; sobolevNumerator =
        nsLargeDataSobolevNumerator
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        nsLargeDataSobolevDenominator
    ; sobolevDenominatorIs8 =
        refl
    ; ambientSpace =
        "R^3"
    ; ambientSpaceIsR3 =
        refl
    ; crossLaneLipschitzConstant =
        cCrossLabel
    ; crossLaneLipschitzConstantIsCcross =
        refl
    ; crossLaneLipschitzConstantFromA5 =
        true
    ; crossLaneLipschitzConstantFromA5IsTrue =
        refl
    ; viscosityCondition =
        "nu > C_cross"
    ; viscosityConditionIsAboveCcross =
        refl
    ; proofSketchSteps =
        canonicalNSLargeDataProofSketchSteps
    ; proofSketchStepsAreCanonical =
        refl
    ; perLaneDissipationDominanceRecorded =
        true
    ; perLaneDissipationDominanceRecordedIsTrue =
        refl
    ; crossLaneLipschitzPerturbationRecorded =
        true
    ; crossLaneLipschitzPerturbationRecordedIsTrue =
        refl
    ; viscosityAbsorptionAboveCcrossRecorded =
        true
    ; viscosityAbsorptionAboveCcrossRecordedIsTrue =
        refl
    ; globalSmoothSolutionUnderViscosityConditionRecorded =
        true
    ; globalSmoothSolutionUnderViscosityConditionRecordedIsTrue =
        refl
    ; clayNSRequiresAnyNu =
        true
    ; clayNSRequiresAnyNuIsTrue =
        refl
    ; remainingGap =
        smallViscosityCase
    ; remainingGapIsSmallViscosityCase =
        refl
    ; smallNuBelowCcrossMayDominate =
        true
    ; smallNuBelowCcrossMayDominateIsTrue =
        refl
    ; arbitraryPositiveViscosityTheoremPromoted =
        false
    ; arbitraryPositiveViscosityTheoremPromotedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; globalTerminalPromotion =
        false
    ; globalTerminalPromotionIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; statement =
        nsLargeDataCandidateTheoremStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "largeDataCandidateTheorem=candidate for nu > C_cross"
        ∷ "clayNSRequiresAnyNu=true"
        ∷ "remainingGap=smallViscosityCase"
        ∷ "The candidate is restricted to carrier-structured H^{11/8}(R^3) data of arbitrary norm"
        ∷ "No Clay/global terminal promotion is made"
        ∷ []
    }

canonicalLargeDataCandidateTheoremIsCandidate :
  largeDataCandidateTheorem canonicalNSLargeDataCandidateTheoremReceipt
    ≡ candidate
canonicalLargeDataCandidateTheoremIsCandidate =
  refl

canonicalClayNSRequiresAnyNu :
  clayNSRequiresAnyNu canonicalNSLargeDataCandidateTheoremReceipt
    ≡ true
canonicalClayNSRequiresAnyNu =
  refl

canonicalRemainingGapSmallViscosityCase :
  remainingGap canonicalNSLargeDataCandidateTheoremReceipt
    ≡ smallViscosityCase
canonicalRemainingGapSmallViscosityCase =
  refl

canonicalNSLargeDataNoClayPromotion :
  clayNavierStokesPromoted canonicalNSLargeDataCandidateTheoremReceipt
    ≡ false
canonicalNSLargeDataNoClayPromotion =
  refl

canonicalNSLargeDataNoGlobalTerminalPromotion :
  globalTerminalPromotion canonicalNSLargeDataCandidateTheoremReceipt
    ≡ false
canonicalNSLargeDataNoGlobalTerminalPromotion =
  refl
