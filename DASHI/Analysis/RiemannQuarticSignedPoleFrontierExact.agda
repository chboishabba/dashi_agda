module DASHI.Analysis.RiemannQuarticSignedPoleFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleCompilerExact as Compiler

------------------------------------------------------------------------
-- Authoritative RH quartic signed-pole frontier
--
-- Current Clay-facing decomposition:
--
--   G1 quantitative band
--   + G3 joint signed completed residual
--   -> external strictness
--   -> high contradiction
--   -> low/high RH compiler.
--
-- G2 same-object assembly and the middle/terminal arrows are compiler-owned.
--
-- Historical routes are RETAINED.  They are not deleted and not declared
-- mathematically useless.  They are classified below as superseded donors:
-- useful for archaeology, diagnostics, component estimates and alternative
-- proof search, but no longer primitive members of the preferred min-cut.
------------------------------------------------------------------------

data QuarticFrontierCoordinate : Set where
  smoothFourWindowConstruction : QuarticFrontierCoordinate
  secondMomentCancellation : QuarticFrontierCoordinate
  fourthMomentNegative : QuarticFrontierCoordinate
  exactPrimeInvisibility : QuarticFrontierCoordinate
  exactSignedPoleCancellation : QuarticFrontierCoordinate
  explicitQuantitativeTargetRadius : QuarticFrontierCoordinate

  targetStrengthUniformLower : QuarticFrontierCoordinate
  fourthLipschitzUniformUpper : QuarticFrontierCoordinate
  uniformBandCoverage : QuarticFrontierCoordinate

  signedCombinedNMuAssembly : QuarticFrontierCoordinate
  jointSignedCompletedResidual : QuarticFrontierCoordinate
  optionalSignedNMuSplitEstimate : QuarticFrontierCoordinate
  optionalHorizontalSplitEstimate : QuarticFrontierCoordinate
  optionalSplitBudgetClosure : QuarticFrontierCoordinate

  strictExternalResidual : QuarticFrontierCoordinate
  finalHighContradiction : QuarticFrontierCoordinate

  oldSeparateGammaEstimate : QuarticFrontierCoordinate
  oldSeparatePolePayment : QuarticFrontierCoordinate
  oldNearFarPoleQuotientRoute : QuarticFrontierCoordinate
  oldActualGridZeroModeTransport : QuarticFrontierCoordinate
  oldIndependentSmoothMainLogTerm : QuarticFrontierCoordinate
  oldSchurNuisanceSelection : QuarticFrontierCoordinate

data QuarticFrontierClass : Set where
  theoremOwned : QuarticFrontierClass
  assemblyOwned : QuarticFrontierClass
  analyticWall : QuarticFrontierClass
  optionalProducer : QuarticFrontierClass
  compilerOutput : QuarticFrontierClass
  supersededDonor : QuarticFrontierClass

quarticFrontierClass :
  QuarticFrontierCoordinate -> QuarticFrontierClass
quarticFrontierClass smoothFourWindowConstruction = theoremOwned
quarticFrontierClass secondMomentCancellation = theoremOwned
quarticFrontierClass fourthMomentNegative = theoremOwned
quarticFrontierClass exactPrimeInvisibility = theoremOwned
quarticFrontierClass exactSignedPoleCancellation = theoremOwned
quarticFrontierClass explicitQuantitativeTargetRadius = theoremOwned

quarticFrontierClass targetStrengthUniformLower = analyticWall
quarticFrontierClass fourthLipschitzUniformUpper = analyticWall
quarticFrontierClass uniformBandCoverage = compilerOutput

quarticFrontierClass signedCombinedNMuAssembly = assemblyOwned
quarticFrontierClass jointSignedCompletedResidual = analyticWall
quarticFrontierClass optionalSignedNMuSplitEstimate = optionalProducer
quarticFrontierClass optionalHorizontalSplitEstimate = optionalProducer
quarticFrontierClass optionalSplitBudgetClosure = optionalProducer

quarticFrontierClass strictExternalResidual = compilerOutput
quarticFrontierClass finalHighContradiction = compilerOutput

quarticFrontierClass oldSeparateGammaEstimate = supersededDonor
quarticFrontierClass oldSeparatePolePayment = supersededDonor
quarticFrontierClass oldNearFarPoleQuotientRoute = supersededDonor
quarticFrontierClass oldActualGridZeroModeTransport = supersededDonor
quarticFrontierClass oldIndependentSmoothMainLogTerm = supersededDonor
quarticFrontierClass oldSchurNuisanceSelection = supersededDonor

record QuarticSignedPoleFrontierBoundary : Set where
  constructor quartic-signed-pole-frontier-boundary
  field
    smoothFourWindowFamilyOwned : Bool
    smoothFourWindowFamilyOwnedIsTrue :
      smoothFourWindowFamilyOwned ≡ true

    exactJ2CancellationOwned : Bool
    exactJ2CancellationOwnedIsTrue :
      exactJ2CancellationOwned ≡ true

    negativeQuarticMomentOwned : Bool
    negativeQuarticMomentOwnedIsTrue :
      negativeQuarticMomentOwned ≡ true

    shortSupportKillsPrimeChannel : Bool
    shortSupportKillsPrimeChannelIsTrue :
      shortSupportKillsPrimeChannel ≡ true

    signedPoleCancellationOwned : Bool
    signedPoleCancellationOwnedIsTrue :
      signedPoleCancellationOwned ≡ true

    explicitFourthOrderRadiusCompilerOwned : Bool
    explicitFourthOrderRadiusCompilerOwnedIsTrue :
      explicitFourthOrderRadiusCompilerOwned ≡ true

    oldExistentialEpsilonRequiredByPreferredConsumer : Bool
    oldExistentialEpsilonRequiredByPreferredConsumerIsFalse :
      oldExistentialEpsilonRequiredByPreferredConsumer ≡ false

    targetStrengthUniformLowerPaid : Bool
    targetStrengthUniformLowerPaidIsFalse :
      targetStrengthUniformLowerPaid ≡ false

    fourthLipschitzUniformUpperPaid : Bool
    fourthLipschitzUniformUpperPaidIsFalse :
      fourthLipschitzUniformUpperPaid ≡ false

    uniformEightOverTBandIsCompilerOutputFromBounds : Bool
    uniformEightOverTBandIsCompilerOutputFromBoundsIsTrue :
      uniformEightOverTBandIsCompilerOutputFromBounds ≡ true

    signedCombinedNMuSameObjectAssemblyOwned : Bool
    signedCombinedNMuSameObjectAssemblyOwnedIsTrue :
      signedCombinedNMuSameObjectAssemblyOwned ≡ true

    jointSignedCompletedResidualPaid : Bool
    jointSignedCompletedResidualPaidIsFalse :
      jointSignedCompletedResidualPaid ≡ false

    splitNMuAndHorizontalRequiredByClayConsumer : Bool
    splitNMuAndHorizontalRequiredByClayConsumerIsFalse :
      splitNMuAndHorizontalRequiredByClayConsumer ≡ false

    splitNMuAndHorizontalRetainedAsOptionalProducer : Bool
    splitNMuAndHorizontalRetainedAsOptionalProducerIsTrue :
      splitNMuAndHorizontalRetainedAsOptionalProducer ≡ true

    strictExternalCompilerOwned : Bool
    strictExternalCompilerOwnedIsTrue :
      strictExternalCompilerOwned ≡ true

    finalHighContradictionCompilerOwned : Bool
    finalHighContradictionCompilerOwnedIsTrue :
      finalHighContradictionCompilerOwned ≡ true

    supersededRoutesRetainedInRepository : Bool
    supersededRoutesRetainedInRepositoryIsTrue :
      supersededRoutesRetainedInRepository ≡ true

    oldSeparateGammaEstimateOnPreferredMinCut : Bool
    oldSeparateGammaEstimateOnPreferredMinCutIsFalse :
      oldSeparateGammaEstimateOnPreferredMinCut ≡ false

    oldSeparatePolePaymentOnPreferredMinCut : Bool
    oldSeparatePolePaymentOnPreferredMinCutIsFalse :
      oldSeparatePolePaymentOnPreferredMinCut ≡ false

    oldNearFarPoleQuotientOnPreferredMinCut : Bool
    oldNearFarPoleQuotientOnPreferredMinCutIsFalse :
      oldNearFarPoleQuotientOnPreferredMinCut ≡ false

    oldActualGridZeroModeTransportOnPreferredMinCut : Bool
    oldActualGridZeroModeTransportOnPreferredMinCutIsFalse :
      oldActualGridZeroModeTransportOnPreferredMinCut ≡ false

    oldIndependentSmoothMainLogOnPreferredMinCut : Bool
    oldIndependentSmoothMainLogOnPreferredMinCutIsFalse :
      oldIndependentSmoothMainLogOnPreferredMinCut ≡ false

    oldSchurNuisanceSelectionOnPreferredMinCut : Bool
    oldSchurNuisanceSelectionOnPreferredMinCutIsFalse :
      oldSchurNuisanceSelectionOnPreferredMinCut ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    quantitativeWall : String
    externalWall : String
    supersessionPolicy : String
    preferredTerminalReading : String

canonicalQuarticSignedPoleFrontierBoundary :
  QuarticSignedPoleFrontierBoundary
canonicalQuarticSignedPoleFrontierBoundary =
  quartic-signed-pole-frontier-boundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    "Preferred G1 proof search: prove a uniform lower bound for signed target strength S(W_t), prove a uniform upper bound for the compact-cosh fourth-derivative Lipschitz constant K(W_t), then use the scalar threshold compiler. For t > 8, 4*(K+1)/t < S is sufficient for 8/t < min(1,2*S/(K+1))."
    "Primitive G3: prove directly that one half of the signed literal N-mu discrepancy plus the signed horizontal remainder is strictly below twice the reflected combined target contribution. Separate N-mu and horizontal bounds are retained only as an optional producer decomposition."
    "Superseded means retained and attributable but not on the preferred Clay-facing min-cut. Separate Gamma, separate pole payment, near/far pole-quotient, actual-grid zero-mode transport, independent smooth-main log and Schur nuisance routes remain available as historical/donor machinery and alternative proof-search surfaces."
    "Authoritative high cut: G1 quantitative band + G3 joint signed completed residual -> external strictness -> high contradiction. G2 same-object assembly and all middle/terminal arrows are compiler output. RH itself remains unproved until G1/G3 plus the low/carrier terminal requirements are discharged."

quarticTerminalCompilerShape :
  {ell : Level} ->
  (C : Compiler.QuarticSignedPoleCompiler {ell}) ->
  Compiler.BandCoverage C ->
  Compiler.JointSignedCompletedResidual C ->
  Compiler.Contradiction
quarticTerminalCompilerShape =
  Compiler.compileQuarticSignedPoleContradiction
