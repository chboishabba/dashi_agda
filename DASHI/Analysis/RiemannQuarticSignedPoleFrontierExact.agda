module DASHI.Analysis.RiemannQuarticSignedPoleFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannQuarticSignedPoleCompilerExact as Compiler

------------------------------------------------------------------------
-- Authoritative RH quartic signed-pole frontier
--
-- Cross-prover provenance:
--   dashi_lean4 exact source base
--     6b5891f3e2f3bafd37a2e1635a4fa2256464309b
--
-- The Lean continuation installs:
--   * explicit quantitative fourth-order target radius;
--   * exact four-window Off+Gamma = 1/2(N-mu)+horizontal assembly;
--   * signed endpoint composition;
--   * final contradiction compiler from the explicit band inequality and the
--     strict signed external residual.
--
-- This Agda surface records the new cut and prevents older pole-quotient,
-- Schur, near/far, or positive-pole routes from being mistaken for the current
-- primitive theorem.
------------------------------------------------------------------------

data QuarticFrontierCoordinate : Set where
  smoothFourWindowConstruction : QuarticFrontierCoordinate
  secondMomentCancellation : QuarticFrontierCoordinate
  fourthMomentNegative : QuarticFrontierCoordinate
  exactPrimeInvisibility : QuarticFrontierCoordinate
  exactSignedPoleCancellation : QuarticFrontierCoordinate
  explicitQuantitativeTargetRadius : QuarticFrontierCoordinate
  uniformBandCoverage : QuarticFrontierCoordinate
  signedCombinedNMuAssembly : QuarticFrontierCoordinate
  signedNMuDiscrepancyEstimate : QuarticFrontierCoordinate
  signedHorizontalRemainderEstimate : QuarticFrontierCoordinate
  strictExternalResidual : QuarticFrontierCoordinate
  finalHighContradiction : QuarticFrontierCoordinate

data QuarticFrontierClass : Set where
  theoremOwned : QuarticFrontierClass
  assemblyOwned : QuarticFrontierClass
  analyticWall : QuarticFrontierClass
  compilerOutput : QuarticFrontierClass

quarticFrontierClass :
  QuarticFrontierCoordinate -> QuarticFrontierClass
quarticFrontierClass smoothFourWindowConstruction = theoremOwned
quarticFrontierClass secondMomentCancellation = theoremOwned
quarticFrontierClass fourthMomentNegative = theoremOwned
quarticFrontierClass exactPrimeInvisibility = theoremOwned
quarticFrontierClass exactSignedPoleCancellation = theoremOwned
quarticFrontierClass explicitQuantitativeTargetRadius = theoremOwned
quarticFrontierClass uniformBandCoverage = analyticWall
quarticFrontierClass signedCombinedNMuAssembly = assemblyOwned
quarticFrontierClass signedNMuDiscrepancyEstimate = analyticWall
quarticFrontierClass signedHorizontalRemainderEstimate = analyticWall
quarticFrontierClass strictExternalResidual = compilerOutput
quarticFrontierClass finalHighContradiction = compilerOutput

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

    uniformEightOverTBandPaid : Bool
    uniformEightOverTBandPaidIsFalse :
      uniformEightOverTBandPaid ≡ false

    signedCombinedNMuSameObjectAssemblyOwned : Bool
    signedCombinedNMuSameObjectAssemblyOwnedIsTrue :
      signedCombinedNMuSameObjectAssemblyOwned ≡ true

    signedNMuDiscrepancyEstimatePaid : Bool
    signedNMuDiscrepancyEstimatePaidIsFalse :
      signedNMuDiscrepancyEstimatePaid ≡ false

    signedHorizontalRemainderEstimatePaid : Bool
    signedHorizontalRemainderEstimatePaidIsFalse :
      signedHorizontalRemainderEstimatePaid ≡ false

    strictExternalCompilerOwned : Bool
    strictExternalCompilerOwnedIsTrue :
      strictExternalCompilerOwned ≡ true

    finalHighContradictionCompilerOwned : Bool
    finalHighContradictionCompilerOwnedIsTrue :
      finalHighContradictionCompilerOwned ≡ true

    oldSchurNuisanceControlRequired : Bool
    oldSchurNuisanceControlRequiredIsFalse :
      oldSchurNuisanceControlRequired ≡ false

    oldPositivePolePaymentRequired : Bool
    oldPositivePolePaymentRequiredIsFalse :
      oldPositivePolePaymentRequired ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    quantitativeWall : String
    externalWall : String
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
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "Prove uniformly on the constructed four-window signed-pole witness that 8/t is below the explicit quantitativeFourthOrderRadius determined by the quartic target margin and compact-cosh fourth-derivative Lipschitz constant."
    "Prove the strict bound for 1/2 times the signed literal N-mu discrepancy plus the signed horizontal remainder against twice the combined reflected target contribution. The N-mu representation itself is compiler-owned; only the estimate remains analytic."
    "The preferred high-zero route is now: four-window J2 cancellation -> exact signed pole cancellation -> explicit quantitative target band -> exact signed N-mu plus horizontal representation -> one strict external residual theorem -> contradiction. Schur nuisance selection, the old near/far terminal wall, and positive-pole payment are not primitive requirements."

-- The final logical dependency is intentionally generic.  It proves that once
-- the two analytic controls inhabit the compiler selected for the concrete
-- scalar carrier, no further RH-high mathematics is needed.
quarticTerminalCompilerShape :
  {ell : Level} ->
  (C : Compiler.QuarticSignedPoleCompiler {ell}) ->
  Compiler.BandCoverage C ->
  Compiler.SignedNMuDiscrepancyControl C ->
  Compiler.HorizontalRemainderControl C ->
  Compiler.Contradiction
quarticTerminalCompilerShape =
  Compiler.compileQuarticSignedPoleContradiction
