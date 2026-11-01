module DASHI.Physics.Closure.NSCumulativeTailDominanceObstructionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt
  as Full
import DASHI.Physics.Closure.NSDangerShellMaxPrincipleConditionalProofReceipt
  as Conditional

------------------------------------------------------------------------
-- NS cumulative tail dominance obstruction.
--
-- Concrete NS worker receipt.  It consumes the fixed-K LP identity and the
-- conditional danger-shell proof, then isolates the exact non-circular
-- paraproduct/dissipation dominance problem.

data NSCumulativeTailDominanceStatus : Set where
  nsCumulativeTailDominanceObstructionRecorded_noPromotion :
    NSCumulativeTailDominanceStatus

data NSTailDominanceSublemma : Set where
  fixedKTailFluxIdentity :
    NSTailDominanceSublemma

  paraproductFluxDecomposition :
    NSTailDominanceSublemma

  highHighFluxBoundPartial :
    NSTailDominanceSublemma

  highLowFluxControlWithoutRegularity :
    NSTailDominanceSublemma

  lowHighFluxBound :
    NSTailDominanceSublemma

  tailDissipationLowerBound :
    NSTailDominanceSublemma

  fluxOverDissipationThetaLtOne :
    NSTailDominanceSublemma

  noGlobalRegularityInput :
    NSTailDominanceSublemma

canonicalNSTailDominanceSublemmas : List NSTailDominanceSublemma
canonicalNSTailDominanceSublemmas =
  fixedKTailFluxIdentity
  ∷ paraproductFluxDecomposition
  ∷ highHighFluxBoundPartial
  ∷ highLowFluxControlWithoutRegularity
  ∷ lowHighFluxBound
  ∷ tailDissipationLowerBound
  ∷ fluxOverDissipationThetaLtOne
  ∷ noGlobalRegularityInput
  ∷ []

data NSParaproductObstructionTerm : Set where
  highHighNonlinearFlux :
    NSParaproductObstructionTerm

  highLowLeakageFlux :
    NSParaproductObstructionTerm

  lowHighTransportFlux :
    NSParaproductObstructionTerm

  pressureProjectionDefect :
    NSParaproductObstructionTerm

  lpCommutatorDefect :
    NSParaproductObstructionTerm

  highLowKStarDriftObstruction :
    NSParaproductObstructionTerm

canonicalNSParaproductObstructionTerms :
  List NSParaproductObstructionTerm
canonicalNSParaproductObstructionTerms =
  highHighNonlinearFlux
  ∷ highLowLeakageFlux
  ∷ lowHighTransportFlux
  ∷ pressureProjectionDefect
  ∷ lpCommutatorDefect
  ∷ highLowKStarDriftObstruction
  ∷ []

data NSRejectedCircularInput : Set where
  serrinRegularityAssumption :
    NSRejectedCircularInput

  bkmControlAssumption :
    NSRejectedCircularInput

  globalH118Assumption :
    NSRejectedCircularInput

  hOneHalfVelocityRegularityShortcut :
    NSRejectedCircularInput

canonicalNSRejectedCircularInputs : List NSRejectedCircularInput
canonicalNSRejectedCircularInputs =
  serrinRegularityAssumption
  ∷ bkmControlAssumption
  ∷ globalH118Assumption
  ∷ hOneHalfVelocityRegularityShortcut
  ∷ []

data NSCumulativeTailDominancePromotion : Set where

nsCumulativeTailDominancePromotionImpossibleHere :
  NSCumulativeTailDominancePromotion →
  ⊥
nsCumulativeTailDominancePromotionImpossibleHere ()

dominanceTargetStatement : String
dominanceTargetStatement =
  "CumulativeTailDissipationDominance target: for fixed K above the danger cutoff, sum_{j>=K} nu*lambda_j^2*a_j >= sum_{j>=K} nonlinear injection_j. HighHigh is recorded as the absorptive partial result; HighLowFluxControlWithoutRegularity is the live non-circular Clay lemma."

obstructionBoundaryStatement : String
obstructionBoundaryStatement =
  "This receipt proves no cumulative dominance theorem. It records fixed-K identity support, HighHigh partial absorption, and the HighLow/LowHigh obstruction. Serrin, BKM, global H^{11/8}, and H^{1/2} shortcut inputs remain rejected."

highLowClayLemmaStatement : String
highLowClayLemmaStatement =
  "HighLowFluxControlWithoutRegularity: ||P_{>K}(u_{<K} * grad u_{>K})||_{H^{-1/2}} <= eps * nu * ||P_{>K}u||_{H^{3/2}} without assuming global ||u_{<K}||_{L^infty} control."

record NSCumulativeTailDominanceObstructionReceipt : Setω where
  field
    status :
      NSCumulativeTailDominanceStatus

    statusIsCanonical :
      status ≡ nsCumulativeTailDominanceObstructionRecorded_noPromotion

    activeCutoff :
      Nat

    activeCutoffIsZeroReceiptCutoff :
      activeCutoff ≡ zero

    fixedKIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt activeCutoff

    fixedKIdentityDerived :
      Full.lpIdentityDerivedHere fixedKIdentityReceipt ≡ true

    fixedKMovingCutoffAbsent :
      Full.movingCutoffTermAbsent fixedKIdentityReceipt ≡ true

    fixedKThetaStillOpen :
      Full.thetaLessThanOneProvedHere fixedKIdentityReceipt ≡ false

    fixedKNoClay :
      Full.clayNavierStokesPromoted fixedKIdentityReceipt ≡ false

    conditionalDangerReceipt :
      Conditional.NSDangerShellMaxPrincipleConditionalProofReceipt activeCutoff

    conditionalDangerRecorded :
      Conditional.conditionalMaxPrincipleProofRecorded conditionalDangerReceipt
      ≡
      true

    conditionalDangerCircular :
      Conditional.circularityIdentified conditionalDangerReceipt ≡ true

    conditionalDangerNonCircularWeakeningOpen :
      Conditional.nonCircularWeakeningProved conditionalDangerReceipt
      ≡
      false

    conditionalDangerHOneHalfShortcutRejected :
      Conditional.hOneHalfControlWouldBeCircularForClay
        conditionalDangerReceipt
      ≡
      true

    conditionalDangerNoClay :
      Conditional.clayNavierStokesPromoted conditionalDangerReceipt ≡ false

    sublemmas :
      List NSTailDominanceSublemma

    sublemmasAreCanonical :
      sublemmas ≡ canonicalNSTailDominanceSublemmas

    obstructionTerms :
      List NSParaproductObstructionTerm

    obstructionTermsAreCanonical :
      obstructionTerms ≡ canonicalNSParaproductObstructionTerms

    rejectedCircularInputs :
      List NSRejectedCircularInput

    rejectedCircularInputsAreCanonical :
      rejectedCircularInputs ≡ canonicalNSRejectedCircularInputs

    noGlobalRegularityInputRule :
      Bool

    noGlobalRegularityInputRuleIsTrue :
      noGlobalRegularityInputRule ≡ true

    paraproductDecompositionProvedHere :
      Bool

    paraproductDecompositionProvedHereIsFalse :
      paraproductDecompositionProvedHere ≡ false

    highHighFluxAbsorbedHere :
      Bool

    highHighFluxAbsorbedHereIsTrue :
      highHighFluxAbsorbedHere ≡ true

    highLowFluxControlWithoutRegularityProved :
      Bool

    highLowFluxControlWithoutRegularityProvedIsFalse :
      highLowFluxControlWithoutRegularityProved ≡ false

    projectionDefectAbsorbedHere :
      Bool

    projectionDefectAbsorbedHereIsFalse :
      projectionDefectAbsorbedHere ≡ false

    cumulativeDominanceProvedHere :
      Bool

    cumulativeDominanceProvedHereIsFalse :
      cumulativeDominanceProvedHere ≡ false

    counterfamilySearchRequired :
      Bool

    counterfamilySearchRequiredIsTrue :
      counterfamilySearchRequired ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSCumulativeTailDominancePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSCumulativeTailDominancePromotion →
      ⊥

    targetText :
      String

    targetTextIsCanonical :
      targetText ≡ dominanceTargetStatement

    highLowClayLemmaText :
      String

    highLowClayLemmaTextIsCanonical :
      highLowClayLemmaText ≡ highLowClayLemmaStatement

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ obstructionBoundaryStatement

open NSCumulativeTailDominanceObstructionReceipt public

canonicalNSCumulativeTailDominanceObstructionReceipt :
  NSCumulativeTailDominanceObstructionReceipt
canonicalNSCumulativeTailDominanceObstructionReceipt =
  record
    { status =
        nsCumulativeTailDominanceObstructionRecorded_noPromotion
    ; statusIsCanonical =
        refl
    ; activeCutoff =
        zero
    ; activeCutoffIsZeroReceiptCutoff =
        refl
    ; fixedKIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fixedKIdentityDerived =
        refl
    ; fixedKMovingCutoffAbsent =
        refl
    ; fixedKThetaStillOpen =
        refl
    ; fixedKNoClay =
        refl
    ; conditionalDangerReceipt =
        Conditional.canonicalNSDangerShellMaxPrincipleConditionalProofReceipt
    ; conditionalDangerRecorded =
        refl
    ; conditionalDangerCircular =
        refl
    ; conditionalDangerNonCircularWeakeningOpen =
        refl
    ; conditionalDangerHOneHalfShortcutRejected =
        refl
    ; conditionalDangerNoClay =
        refl
    ; sublemmas =
        canonicalNSTailDominanceSublemmas
    ; sublemmasAreCanonical =
        refl
    ; obstructionTerms =
        canonicalNSParaproductObstructionTerms
    ; obstructionTermsAreCanonical =
        refl
    ; rejectedCircularInputs =
        canonicalNSRejectedCircularInputs
    ; rejectedCircularInputsAreCanonical =
        refl
    ; noGlobalRegularityInputRule =
        true
    ; noGlobalRegularityInputRuleIsTrue =
        refl
    ; paraproductDecompositionProvedHere =
        false
    ; paraproductDecompositionProvedHereIsFalse =
        refl
    ; highHighFluxAbsorbedHere =
        true
    ; highHighFluxAbsorbedHereIsTrue =
        refl
    ; highLowFluxControlWithoutRegularityProved =
        false
    ; highLowFluxControlWithoutRegularityProvedIsFalse =
        refl
    ; projectionDefectAbsorbedHere =
        false
    ; projectionDefectAbsorbedHereIsFalse =
        refl
    ; cumulativeDominanceProvedHere =
        false
    ; cumulativeDominanceProvedHereIsFalse =
        refl
    ; counterfamilySearchRequired =
        true
    ; counterfamilySearchRequiredIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        nsCumulativeTailDominancePromotionImpossibleHere
    ; targetText =
        dominanceTargetStatement
    ; targetTextIsCanonical =
        refl
    ; highLowClayLemmaText =
        highLowClayLemmaStatement
    ; highLowClayLemmaTextIsCanonical =
        refl
    ; boundary =
        obstructionBoundaryStatement
    ; boundaryIsCanonical =
        refl
    }

canonicalNSCumulativeDominanceStillOpen :
  cumulativeDominanceProvedHere
    canonicalNSCumulativeTailDominanceObstructionReceipt
  ≡
  false
canonicalNSCumulativeDominanceStillOpen =
  refl
