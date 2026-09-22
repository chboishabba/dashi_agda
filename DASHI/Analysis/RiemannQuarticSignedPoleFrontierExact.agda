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
-- G1 has now been recut existentially in the witness.  For every t>=200 the
-- Lean construction selects one sufficiently narrow witness with
--
--   S(W_t) >= 7*pi^4/1600.
--
-- Hence target strength is no longer an analytic leaf.  The remaining G1
-- norm debt is a uniform L1 bound for the exact signed combined profile;
-- support in |u|<pi+1 and the K-from-support-and-mass compiler are owned.
--
-- Historical routes remain retained as superseded donors.
------------------------------------------------------------------------

data QuarticFrontierCoordinate : Set where
  smoothFourWindowConstruction : QuarticFrontierCoordinate
  secondMomentCancellation : QuarticFrontierCoordinate
  fourthMomentNegative : QuarticFrontierCoordinate
  exactPrimeInvisibility : QuarticFrontierCoordinate
  exactSignedPoleCancellation : QuarticFrontierCoordinate
  explicitQuantitativeTargetRadius : QuarticFrontierCoordinate

  constructedTargetStrengthFloor : QuarticFrontierCoordinate
  combinedProfileSupportPiAddOne : QuarticFrontierCoordinate
  combinedProfileUniformL1 : QuarticFrontierCoordinate
  fourthLipschitzUniformUpper : QuarticFrontierCoordinate
  uniformBandCoverage : QuarticFrontierCoordinate

  signedCombinedNMuAssembly : QuarticFrontierCoordinate
  jointSignedCompletedResidual : QuarticFrontierCoordinate
  optionalSignedNMuSplitEstimate : QuarticFrontierCoordinate
  optionalHorizontalSplitEstimate : QuarticFrontierCoordinate
  optionalSplitBudgetClosure : QuarticFrontierCoordinate

  strictExternalResidual : QuarticFrontierCoordinate
  finalHighContradiction : QuarticFrontierCoordinate

  oldUniversalTargetStrengthForEveryWitness : QuarticFrontierCoordinate
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

quarticFrontierClass constructedTargetStrengthFloor = theoremOwned
quarticFrontierClass combinedProfileSupportPiAddOne = theoremOwned
quarticFrontierClass combinedProfileUniformL1 = theoremOwned
quarticFrontierClass fourthLipschitzUniformUpper = theoremOwned
quarticFrontierClass uniformBandCoverage = compilerOutput

quarticFrontierClass signedCombinedNMuAssembly = assemblyOwned
quarticFrontierClass jointSignedCompletedResidual = analyticWall
quarticFrontierClass optionalSignedNMuSplitEstimate = optionalProducer
quarticFrontierClass optionalHorizontalSplitEstimate = optionalProducer
quarticFrontierClass optionalSplitBudgetClosure = optionalProducer

quarticFrontierClass strictExternalResidual = compilerOutput
quarticFrontierClass finalHighContradiction = compilerOutput

quarticFrontierClass oldUniversalTargetStrengthForEveryWitness = supersededDonor
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
    exactJ2CancellationOwned : Bool
    negativeQuarticMomentOwned : Bool
    shortSupportKillsPrimeChannel : Bool
    signedPoleCancellationOwned : Bool
    explicitFourthOrderRadiusCompilerOwned : Bool

    existentialWitnessQuantifierIsAuthoritative : Bool
    constructedStrengthFloorSevenPi4Over1600Paid : Bool
    combinedProfileSupportPiAddOnePaid : Bool
    combinedProfileUniformL1Paid : Bool
    explicitFourthLipschitzK0Paid : Bool
    fourthLipschitzFromSupportMassCompilerOwned : Bool
    scalarThresholdBelowPlattTrudgianPaid : Bool
    uniformEightOverTBandIsCompilerOutputFromBounds : Bool

    oldUniversalAllWitnessStrengthLowerRequired : Bool
    oldExistentialEpsilonRequiredByPreferredConsumer : Bool

    signedCombinedNMuSameObjectAssemblyOwned : Bool
    jointSignedCompletedResidualPaid : Bool
    splitNMuAndHorizontalRequiredByClayConsumer : Bool
    splitNMuAndHorizontalRetainedAsOptionalProducer : Bool

    strictExternalCompilerOwned : Bool
    finalHighContradictionCompilerOwned : Bool
    supersededRoutesRetainedInRepository : Bool

    rhDerived : Bool

    smoothFourWindowFamilyOwnedIsTrue :
      smoothFourWindowFamilyOwned ≡ true
    exactJ2CancellationOwnedIsTrue :
      exactJ2CancellationOwned ≡ true
    negativeQuarticMomentOwnedIsTrue :
      negativeQuarticMomentOwned ≡ true
    shortSupportKillsPrimeChannelIsTrue :
      shortSupportKillsPrimeChannel ≡ true
    signedPoleCancellationOwnedIsTrue :
      signedPoleCancellationOwned ≡ true
    explicitFourthOrderRadiusCompilerOwnedIsTrue :
      explicitFourthOrderRadiusCompilerOwned ≡ true

    existentialWitnessQuantifierIsAuthoritativeIsTrue :
      existentialWitnessQuantifierIsAuthoritative ≡ true
    constructedStrengthFloorSevenPi4Over1600PaidIsTrue :
      constructedStrengthFloorSevenPi4Over1600Paid ≡ true
    combinedProfileSupportPiAddOnePaidIsTrue :
      combinedProfileSupportPiAddOnePaid ≡ true
    combinedProfileUniformL1PaidIsTrue :
      combinedProfileUniformL1Paid ≡ true
    explicitFourthLipschitzK0PaidIsTrue :
      explicitFourthLipschitzK0Paid ≡ true
    fourthLipschitzFromSupportMassCompilerOwnedIsTrue :
      fourthLipschitzFromSupportMassCompilerOwned ≡ true
    scalarThresholdBelowPlattTrudgianPaidIsFalse :
      scalarThresholdBelowPlattTrudgianPaid ≡ false
    uniformEightOverTBandIsCompilerOutputFromBoundsIsTrue :
      uniformEightOverTBandIsCompilerOutputFromBounds ≡ true

    oldUniversalAllWitnessStrengthLowerRequiredIsFalse :
      oldUniversalAllWitnessStrengthLowerRequired ≡ false
    oldExistentialEpsilonRequiredByPreferredConsumerIsFalse :
      oldExistentialEpsilonRequiredByPreferredConsumer ≡ false

    signedCombinedNMuSameObjectAssemblyOwnedIsTrue :
      signedCombinedNMuSameObjectAssemblyOwned ≡ true
    jointSignedCompletedResidualPaidIsFalse :
      jointSignedCompletedResidualPaid ≡ false
    splitNMuAndHorizontalRequiredByClayConsumerIsFalse :
      splitNMuAndHorizontalRequiredByClayConsumer ≡ false
    splitNMuAndHorizontalRetainedAsOptionalProducerIsTrue :
      splitNMuAndHorizontalRetainedAsOptionalProducer ≡ true

    strictExternalCompilerOwnedIsTrue :
      strictExternalCompilerOwned ≡ true
    finalHighContradictionCompilerOwnedIsTrue :
      finalHighContradictionCompilerOwned ≡ true
    supersededRoutesRetainedInRepositoryIsTrue :
      supersededRoutesRetainedInRepository ≡ true

    rhDerivedIsFalse : rhDerived ≡ false

    quantitativeWall : String
    externalWall : String
    supersessionPolicy : String
    preferredTerminalReading : String

canonicalQuarticSignedPoleFrontierBoundary :
  QuarticSignedPoleFrontierBoundary
canonicalQuarticSignedPoleFrontierBoundary =
  quartic-signed-pole-frontier-boundary
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    true
    false
    true
    false
    false
    true
    false
    false
    true
    true
    true
    true
    false
    refl refl refl refl refl refl
    refl refl refl refl refl refl refl refl
    refl refl
    refl refl refl refl
    refl refl refl
    refl
    "G1 has been reduced to scalar arithmetic. The Lean source now constructs a witness with S(W_t)>=7*pi^4/1600, proves endpoint taper L1<=83/30, compiles this through the exact projective profile, bounds the smooth pole coordinates, obtains an explicit combined-profile L1 bound and hence an explicit K0. It defines T_Q=4*(K0+1)/(7*pi^4/1600). The sole remaining G1 payment is the certified scalar comparison T_Q < the Platt-Trudgian cutoff; numerically the coarse constants give T_Q about 1.041e9 versus T_PT about 3.000e12, but that numerical comparison is not marked paid here."
    "Primitive G3 remains the joint theorem: one half of the signed literal N-mu discrepancy plus the signed horizontal remainder is strictly below twice the reflected combined target contribution. Separate N-mu and horizontal bounds are optional proof-search producers only."
    "Superseded means retained and attributable but not on the preferred Clay-facing min-cut. In particular the old universal lower bound over every arbitrary QuarticFourSignedPolePair is stronger than needed and is retained only as a donor interface."
    "Authoritative high cut: one scalar G1 threshold comparison plus G3 joint signed completed residual -> external strictness -> high contradiction. G2 same-object assembly and all middle/terminal arrows are compiler output. RH remains unproved because G3 is open and the scalar T_Q<T_PT comparison has not yet been kernel-paid."

quarticTerminalCompilerShape :
  {ell : Level} ->
  (C : Compiler.QuarticSignedPoleCompiler {ell}) ->
  Compiler.BandCoverage C ->
  Compiler.JointSignedCompletedResidual C ->
  Compiler.Contradiction
quarticTerminalCompilerShape =
  Compiler.compileQuarticSignedPoleContradiction
