module DASHI.Physics.Closure.NSGaussianSelfSimilarBalanceIdentityBoundary where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Closure.NSCascadeKappaArcsineLawBoundary
  as Arcsine
import DASHI.Physics.Closure.NSFiniteCascadeStretchingNeutralityBoundary
  as Neutrality
import DASHI.Physics.Closure.NSTypeIBlowupKappaBiasBoundBoundary
  as KappaBias

------------------------------------------------------------------------
-- NS Gaussian self-similar kappa-bias balance identity boundary.
--
-- This module records the corrected fail-closed balance target for a
-- backward-Leray self-similar vorticity profile tested against the Gaussian
-- weight
--
--   G(y) = exp(- |y|^2 / 4).
--
-- The corrected schematic identity is:
--
--   2 int |grad omega|^2 G - 1/2 int |omega|^2 G
--     = 4 Bias_G Omega_G + Drift_G Omega_G
--
-- with
--
--   Omega_G = int |omega|^2 G,
--   Bias_G  = Gaussian/Abel kappa-bias in the
--             lambda(c)(kappa^2 - 1/2) channel,
--   Drift_G = nonlinear sweeping correction normalized by Omega_G.
--
-- The Ornstein-Uhlenbeck/Poincare lower bound gives the consequence:
--
--   nontrivial omega requires 1 <= 4 Bias_G + Drift_G.
--
-- Under arcsine neutrality Bias_G = 0.  In the classical
-- Necas-Ruzicka-Sverak self-similar context, the drift term is ruled out,
-- yielding the contradiction 1 <= 0.  This module records that as a
-- classical-context boundary only.  It does not prove the Abel triadic
-- measure construction, the Type-I kappa-bias bound, CKN-scale residual
-- depletion, Navier-Stokes Clay, or terminal promotion.

data List (A : Set) : Set where
  [] :
    List A
  _∷_ :
    A →
    List A →
    List A

infixr 5 _∷_

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data ⊥ : Set where

------------------------------------------------------------------------
-- Carriers for the corrected Gaussian balance.

data GaussianSelfSimilarBalanceCarrier : Set where
  gaussianWeightExpMinusRadiusSquaredOverFour :
    GaussianSelfSimilarBalanceCarrier
  gaussianWeightedEnstrophyOmegaG :
    GaussianSelfSimilarBalanceCarrier
  gaussianWeightedGradientVorticityDissipation :
    GaussianSelfSimilarBalanceCarrier
  gaussianKappaBiasBiasG :
    GaussianSelfSimilarBalanceCarrier
  normalizedNonlinearSweepingDriftG :
    GaussianSelfSimilarBalanceCarrier
  backwardLeraySelfSimilarVorticityProfile :
    GaussianSelfSimilarBalanceCarrier

canonicalGaussianSelfSimilarBalanceCarriers :
  List GaussianSelfSimilarBalanceCarrier
canonicalGaussianSelfSimilarBalanceCarriers =
  gaussianWeightExpMinusRadiusSquaredOverFour
  ∷ gaussianWeightedEnstrophyOmegaG
  ∷ gaussianWeightedGradientVorticityDissipation
  ∷ gaussianKappaBiasBiasG
  ∷ normalizedNonlinearSweepingDriftG
  ∷ backwardLeraySelfSimilarVorticityProfile
  ∷ []

gaussianSelfSimilarBalanceCarrierCount : Nat
gaussianSelfSimilarBalanceCarrierCount =
  listLength canonicalGaussianSelfSimilarBalanceCarriers

gaussianSelfSimilarBalanceCarrierCountIs6 :
  gaussianSelfSimilarBalanceCarrierCount ≡ 6
gaussianSelfSimilarBalanceCarrierCountIs6 =
  refl

------------------------------------------------------------------------
-- The corrected identity and its OU/Poincare consequence.

data CorrectedGaussianBalanceClause : Set where
  leftSideIsTwoGradientDissipationMinusHalfEnstrophy :
    CorrectedGaussianBalanceClause
  rightSideIsFourBiasGOmegaGPlusDriftGOmegaG :
    CorrectedGaussianBalanceClause
  biasGIsGaussianAbelLambdaTimesKappaSquaredMinusOneHalf :
    CorrectedGaussianBalanceClause
  driftGIsNonlinearSweepingCorrectionNormalizedByOmegaG :
    CorrectedGaussianBalanceClause
  ouPoincareBoundsLeftSideBelowByOmegaG :
    CorrectedGaussianBalanceClause
  nontrivialOmegaRequiresOneLeqFourBiasGPlusDriftG :
    CorrectedGaussianBalanceClause

canonicalCorrectedGaussianBalanceClauses :
  List CorrectedGaussianBalanceClause
canonicalCorrectedGaussianBalanceClauses =
  leftSideIsTwoGradientDissipationMinusHalfEnstrophy
  ∷ rightSideIsFourBiasGOmegaGPlusDriftGOmegaG
  ∷ biasGIsGaussianAbelLambdaTimesKappaSquaredMinusOneHalf
  ∷ driftGIsNonlinearSweepingCorrectionNormalizedByOmegaG
  ∷ ouPoincareBoundsLeftSideBelowByOmegaG
  ∷ nontrivialOmegaRequiresOneLeqFourBiasGPlusDriftG
  ∷ []

correctedGaussianBalanceClauseCount : Nat
correctedGaussianBalanceClauseCount =
  listLength canonicalCorrectedGaussianBalanceClauses

correctedGaussianBalanceClauseCountIs6 :
  correctedGaussianBalanceClauseCount ≡ 6
correctedGaussianBalanceClauseCountIs6 =
  refl

data ClassicalContextBoundaryClause : Set where
  arcsineNeutralitySetsBiasGToZero :
    ClassicalContextBoundaryClause
  finiteCascadeNeutralitySuppliesOnlyBaselineNotPdeClosure :
    ClassicalContextBoundaryClause
  necasRuzickaSverakContextRulesOutDriftG :
    ClassicalContextBoundaryClause
  classicalSelfSimilarContradictionIsOneLeqZero :
    ClassicalContextBoundaryClause
  cknScaleTypeIProblemStillRequiresAbelStationarity :
    ClassicalContextBoundaryClause
  nonSelfSimilarTypeIBlowupNotClosedByClassicalIdentityAlone :
    ClassicalContextBoundaryClause

canonicalClassicalContextBoundaryClauses :
  List ClassicalContextBoundaryClause
canonicalClassicalContextBoundaryClauses =
  arcsineNeutralitySetsBiasGToZero
  ∷ finiteCascadeNeutralitySuppliesOnlyBaselineNotPdeClosure
  ∷ necasRuzickaSverakContextRulesOutDriftG
  ∷ classicalSelfSimilarContradictionIsOneLeqZero
  ∷ cknScaleTypeIProblemStillRequiresAbelStationarity
  ∷ nonSelfSimilarTypeIBlowupNotClosedByClassicalIdentityAlone
  ∷ []

classicalContextBoundaryClauseCount : Nat
classicalContextBoundaryClauseCount =
  listLength canonicalClassicalContextBoundaryClauses

classicalContextBoundaryClauseCountIs6 :
  classicalContextBoundaryClauseCount ≡ 6
classicalContextBoundaryClauseCountIs6 =
  refl

------------------------------------------------------------------------
-- Dependencies and blockers.

data GaussianSelfSimilarBalanceDependency : Set where
  arcsineKappaNeutralityDependency :
    GaussianSelfSimilarBalanceDependency
  finiteCascadeNeutralityDependency :
    GaussianSelfSimilarBalanceDependency
  typeIKappaBiasBoundDependency :
    GaussianSelfSimilarBalanceDependency
  gaussianOrnsteinUhlenbeckPoincareDependency :
    GaussianSelfSimilarBalanceDependency
  necasRuzickaSverakClassicalAuthorityDependency :
    GaussianSelfSimilarBalanceDependency

canonicalGaussianSelfSimilarBalanceDependencies :
  List GaussianSelfSimilarBalanceDependency
canonicalGaussianSelfSimilarBalanceDependencies =
  arcsineKappaNeutralityDependency
  ∷ finiteCascadeNeutralityDependency
  ∷ typeIKappaBiasBoundDependency
  ∷ gaussianOrnsteinUhlenbeckPoincareDependency
  ∷ necasRuzickaSverakClassicalAuthorityDependency
  ∷ []

gaussianSelfSimilarBalanceDependencyCount : Nat
gaussianSelfSimilarBalanceDependencyCount =
  listLength canonicalGaussianSelfSimilarBalanceDependencies

gaussianSelfSimilarBalanceDependencyCountIs5 :
  gaussianSelfSimilarBalanceDependencyCount ≡ 5
gaussianSelfSimilarBalanceDependencyCountIs5 =
  refl

data GaussianSelfSimilarBalanceBlocker : Set where
  missingAbelTriadicDefectMeasureConstruction :
    GaussianSelfSimilarBalanceBlocker
  missingProofOfApproximateTransferOperatorStationarity :
    GaussianSelfSimilarBalanceBlocker
  missingCknScaleGaussianBalancePassage :
    GaussianSelfSimilarBalanceBlocker
  missingTypeIKappaBiasNonpositiveEstimate :
    GaussianSelfSimilarBalanceBlocker
  missingTriadicCompensatedLeakageIdentity :
    GaussianSelfSimilarBalanceBlocker
  missingCriticalResidualAndCknBkmClosure :
    GaussianSelfSimilarBalanceBlocker

canonicalGaussianSelfSimilarBalanceBlockers :
  List GaussianSelfSimilarBalanceBlocker
canonicalGaussianSelfSimilarBalanceBlockers =
  missingAbelTriadicDefectMeasureConstruction
  ∷ missingProofOfApproximateTransferOperatorStationarity
  ∷ missingCknScaleGaussianBalancePassage
  ∷ missingTypeIKappaBiasNonpositiveEstimate
  ∷ missingTriadicCompensatedLeakageIdentity
  ∷ missingCriticalResidualAndCknBkmClosure
  ∷ []

gaussianSelfSimilarBalanceBlockerCount : Nat
gaussianSelfSimilarBalanceBlockerCount =
  listLength canonicalGaussianSelfSimilarBalanceBlockers

gaussianSelfSimilarBalanceBlockerCountIs6 :
  gaussianSelfSimilarBalanceBlockerCount ≡ 6
gaussianSelfSimilarBalanceBlockerCountIs6 =
  refl

------------------------------------------------------------------------
-- Fail-closed governance.

data NSGaussianSelfSimilarBalancePromotion : Set where

nsGaussianSelfSimilarBalancePromotionImpossibleHere :
  NSGaussianSelfSimilarBalancePromotion →
  ⊥
nsGaussianSelfSimilarBalancePromotionImpossibleHere ()

gaussianBalanceIdentityPromotesTypeIBiasBound : Bool
gaussianBalanceIdentityPromotesTypeIBiasBound =
  false

gaussianBalanceIdentityPromotesClayNS : Bool
gaussianBalanceIdentityPromotesClayNS =
  false

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

data NSGaussianSelfSimilarBalanceStatus : Set where
  gaussianSelfSimilarBalanceRecorded_classicalContextBoundary_noPromotion :
    NSGaussianSelfSimilarBalanceStatus

nsGaussianSelfSimilarBalanceSummary : String
nsGaussianSelfSimilarBalanceSummary =
  "Records corrected Gaussian self-similar kappa-bias balance: 2 int |grad omega|^2 G - 1/2 int |omega|^2 G = 4 Bias_G Omega_G + Drift_G Omega_G; nontrivial omega requires 1 <= 4 Bias_G + Drift_G. Arcsine neutrality plus classical NRS drift exclusion gives only the classical self-similar contradiction, not CKN-scale NS Clay closure."

record NSGaussianSelfSimilarBalanceIdentityBoundary : Set where
  field
    status :
      NSGaussianSelfSimilarBalanceStatus
    statusIsCanonical :
      status ≡
        gaussianSelfSimilarBalanceRecorded_classicalContextBoundary_noPromotion
    carriers :
      List GaussianSelfSimilarBalanceCarrier
    carriersAreCanonical :
      carriers ≡ canonicalGaussianSelfSimilarBalanceCarriers
    carrierCountIsSix :
      gaussianSelfSimilarBalanceCarrierCount ≡ 6
    correctedBalanceClauses :
      List CorrectedGaussianBalanceClause
    correctedBalanceClausesAreCanonical :
      correctedBalanceClauses ≡ canonicalCorrectedGaussianBalanceClauses
    correctedBalanceClauseCountIsSix :
      correctedGaussianBalanceClauseCount ≡ 6
    classicalContextClauses :
      List ClassicalContextBoundaryClause
    classicalContextClausesAreCanonical :
      classicalContextClauses ≡ canonicalClassicalContextBoundaryClauses
    classicalContextClauseCountIsSix :
      classicalContextBoundaryClauseCount ≡ 6
    dependencies :
      List GaussianSelfSimilarBalanceDependency
    dependenciesAreCanonical :
      dependencies ≡ canonicalGaussianSelfSimilarBalanceDependencies
    dependencyCountIsFive :
      gaussianSelfSimilarBalanceDependencyCount ≡ 5
    blockers :
      List GaussianSelfSimilarBalanceBlocker
    blockersAreCanonical :
      blockers ≡ canonicalGaussianSelfSimilarBalanceBlockers
    blockerCountIsSix :
      gaussianSelfSimilarBalanceBlockerCount ≡ 6
    gaussianBalanceIdentityPromotesTypeIBiasBoundIsFalse :
      gaussianBalanceIdentityPromotesTypeIBiasBound ≡ false
    gaussianBalanceIdentityPromotesClayNSIsFalse :
      gaussianBalanceIdentityPromotesClayNS ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false
    terminalPromotionIsFalse :
      terminalPromotion ≡ false
    summary :
      String
    summaryIsCanonical :
      summary ≡ nsGaussianSelfSimilarBalanceSummary

canonicalNSGaussianSelfSimilarBalanceIdentityBoundary :
  NSGaussianSelfSimilarBalanceIdentityBoundary
canonicalNSGaussianSelfSimilarBalanceIdentityBoundary =
  record
    { status =
        gaussianSelfSimilarBalanceRecorded_classicalContextBoundary_noPromotion
    ; statusIsCanonical =
        refl
    ; carriers =
        canonicalGaussianSelfSimilarBalanceCarriers
    ; carriersAreCanonical =
        refl
    ; carrierCountIsSix =
        refl
    ; correctedBalanceClauses =
        canonicalCorrectedGaussianBalanceClauses
    ; correctedBalanceClausesAreCanonical =
        refl
    ; correctedBalanceClauseCountIsSix =
        refl
    ; classicalContextClauses =
        canonicalClassicalContextBoundaryClauses
    ; classicalContextClausesAreCanonical =
        refl
    ; classicalContextClauseCountIsSix =
        refl
    ; dependencies =
        canonicalGaussianSelfSimilarBalanceDependencies
    ; dependenciesAreCanonical =
        refl
    ; dependencyCountIsFive =
        refl
    ; blockers =
        canonicalGaussianSelfSimilarBalanceBlockers
    ; blockersAreCanonical =
        refl
    ; blockerCountIsSix =
        refl
    ; gaussianBalanceIdentityPromotesTypeIBiasBoundIsFalse =
        refl
    ; gaussianBalanceIdentityPromotesClayNSIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; terminalPromotionIsFalse =
        refl
    ; summary =
        nsGaussianSelfSimilarBalanceSummary
    ; summaryIsCanonical =
        refl
    }

nsGaussianSelfSimilarBalanceKeepsTypeIBiasBoundUnpromoted :
  gaussianBalanceIdentityPromotesTypeIBiasBound ≡ false
nsGaussianSelfSimilarBalanceKeepsTypeIBiasBoundUnpromoted =
  refl

nsGaussianSelfSimilarBalanceKeepsClayFalse :
  clayNavierStokesPromoted ≡ false
nsGaussianSelfSimilarBalanceKeepsClayFalse =
  refl

nsGaussianSelfSimilarBalanceKeepsTerminalFalse :
  terminalPromotion ≡ false
nsGaussianSelfSimilarBalanceKeepsTerminalFalse =
  refl

------------------------------------------------------------------------
-- Alias witnesses that the imported support surfaces remain boundary-only.

arcsineSupportKeepsClayFalse :
  Arcsine.clayNavierStokesPromoted ≡ false
arcsineSupportKeepsClayFalse =
  refl

neutralitySupportKeepsClayFalse :
  Neutrality.clayNavierStokesPromoted ≡ false
neutralitySupportKeepsClayFalse =
  refl

kappaBiasSupportKeepsPromotionImpossible :
  KappaBias.NSTypeIBlowupKappaBiasPromotion →
  ⊥
kappaBiasSupportKeepsPromotionImpossible ()
