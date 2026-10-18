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
  signedPsiDerivativeAssembly : QuarticFrontierCoordinate
  signedPsiCenteredJetAssembly : QuarticFrontierCoordinate
  signedPsiQuantitativeRadialDerivativeSign : QuarticFrontierCoordinate
  signedPsiFiniteWindowAbelAssembly : QuarticFrontierCoordinate
  signedPsiCenteredFiniteAbelAssembly : QuarticFrontierCoordinate
  signedPsiGlobalPointwiseNMuWeld : QuarticFrontierCoordinate
  signedPsiGlobalCenteredAbelExhaustion : QuarticFrontierCoordinate
  signedPsiRightBoundaryDecayEnvelope : QuarticFrontierCoordinate
  signedPsiFarLeftReflectionExhaustion : QuarticFrontierCoordinate
  signedPsiLeftBoundaryTendstoZero : QuarticFrontierCoordinate
  signedPsiRightBoundaryTendstoZero : QuarticFrontierCoordinate
  signedPsiCorrelationIntegralExhaustion : QuarticFrontierCoordinate
  signedPsiFiniteResidualToGlobalNMu : QuarticFrontierCoordinate
  signedPsiFullLineMuIntegrability : QuarticFrontierCoordinate
  completedResidualEqualsCombinedCluster : QuarticFrontierCoordinate
  outwardCenteredDiscrepancyNoGo : QuarticFrontierCoordinate
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
quarticFrontierClass signedPsiDerivativeAssembly = assemblyOwned
quarticFrontierClass signedPsiCenteredJetAssembly = assemblyOwned
quarticFrontierClass signedPsiQuantitativeRadialDerivativeSign = assemblyOwned
quarticFrontierClass signedPsiFiniteWindowAbelAssembly = assemblyOwned
quarticFrontierClass signedPsiCenteredFiniteAbelAssembly = assemblyOwned
quarticFrontierClass signedPsiGlobalPointwiseNMuWeld = assemblyOwned
quarticFrontierClass signedPsiGlobalCenteredAbelExhaustion = theoremOwned
quarticFrontierClass signedPsiRightBoundaryDecayEnvelope = theoremOwned
quarticFrontierClass signedPsiFarLeftReflectionExhaustion = assemblyOwned
quarticFrontierClass signedPsiLeftBoundaryTendstoZero = assemblyOwned
quarticFrontierClass signedPsiRightBoundaryTendstoZero = assemblyOwned
quarticFrontierClass signedPsiCorrelationIntegralExhaustion = optionalProducer
quarticFrontierClass signedPsiFiniteResidualToGlobalNMu = theoremOwned
quarticFrontierClass signedPsiFullLineMuIntegrability = assemblyOwned
quarticFrontierClass completedResidualEqualsCombinedCluster = theoremOwned
quarticFrontierClass outwardCenteredDiscrepancyNoGo = theoremOwned
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
    signedPsiDerivativeAssemblySourceWritten : Bool
    signedPsiCenteredJetSourceWritten : Bool
    signedPsiQuantitativeRadialDerivativeSignSourceWritten : Bool
    signedPsiFiniteWindowAbelSourceWritten : Bool
    signedPsiCenteredFiniteAbelSourceWritten : Bool
    signedPsiGlobalPointwiseNMuWeldSourceWrittenFailClosed : Bool
    signedPsiGlobalCenteredAbelExhaustionPaid : Bool
    signedPsiRightBoundaryDecayEnvelopePaid : Bool
    signedPsiFarLeftReflectionExhaustionPaid : Bool
    signedPsiLeftBoundaryTendstoZeroSourceWritten : Bool
    signedPsiRightBoundaryTendstoZeroSourceWritten : Bool
    signedPsiCorrelationIntegralExhaustionPaid : Bool
    signedPsiFiniteResidualToGlobalNMuPaid : Bool
    signedPsiFullLineMuIntegrabilityPaid : Bool
    completedResidualEqualsCombinedClusterPaid : Bool
    outwardCenteredDiscrepancyNoGoPaid : Bool
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
    scalarThresholdBelowPlattTrudgianPaidIsTrue :
      scalarThresholdBelowPlattTrudgianPaid ≡ true
    uniformEightOverTBandIsCompilerOutputFromBoundsIsTrue :
      uniformEightOverTBandIsCompilerOutputFromBounds ≡ true

    oldUniversalAllWitnessStrengthLowerRequiredIsFalse :
      oldUniversalAllWitnessStrengthLowerRequired ≡ false
    oldExistentialEpsilonRequiredByPreferredConsumerIsFalse :
      oldExistentialEpsilonRequiredByPreferredConsumer ≡ false

    signedCombinedNMuSameObjectAssemblyOwnedIsTrue :
      signedCombinedNMuSameObjectAssemblyOwned ≡ true
    signedPsiDerivativeAssemblySourceWrittenIsTrue :
      signedPsiDerivativeAssemblySourceWritten ≡ true
    signedPsiCenteredJetSourceWrittenIsTrue :
      signedPsiCenteredJetSourceWritten ≡ true
    signedPsiQuantitativeRadialDerivativeSignSourceWrittenIsTrue :
      signedPsiQuantitativeRadialDerivativeSignSourceWritten ≡ true
    signedPsiFiniteWindowAbelSourceWrittenIsTrue :
      signedPsiFiniteWindowAbelSourceWritten ≡ true
    signedPsiCenteredFiniteAbelSourceWrittenIsTrue :
      signedPsiCenteredFiniteAbelSourceWritten ≡ true
    signedPsiGlobalPointwiseNMuWeldSourceWrittenFailClosedIsTrue :
      signedPsiGlobalPointwiseNMuWeldSourceWrittenFailClosed ≡ true
    signedPsiGlobalCenteredAbelExhaustionPaidIsTrue :
      signedPsiGlobalCenteredAbelExhaustionPaid ≡ true
    signedPsiRightBoundaryDecayEnvelopePaidIsTrue :
      signedPsiRightBoundaryDecayEnvelopePaid ≡ true
    signedPsiFarLeftReflectionExhaustionPaidIsTrue :
      signedPsiFarLeftReflectionExhaustionPaid ≡ true
    signedPsiLeftBoundaryTendstoZeroSourceWrittenIsTrue :
      signedPsiLeftBoundaryTendstoZeroSourceWritten ≡ true
    signedPsiRightBoundaryTendstoZeroSourceWrittenIsTrue :
      signedPsiRightBoundaryTendstoZeroSourceWritten ≡ true
    signedPsiCorrelationIntegralExhaustionPaidIsFalse :
      signedPsiCorrelationIntegralExhaustionPaid ≡ false
    signedPsiFiniteResidualToGlobalNMuPaidIsTrue :
      signedPsiFiniteResidualToGlobalNMuPaid ≡ true
    signedPsiFullLineMuIntegrabilityPaidIsTrue :
      signedPsiFullLineMuIntegrabilityPaid ≡ true
    completedResidualEqualsCombinedClusterPaidIsTrue :
      completedResidualEqualsCombinedClusterPaid ≡ true
    outwardCenteredDiscrepancyNoGoPaidIsTrue :
      outwardCenteredDiscrepancyNoGoPaid ≡ true
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
    true
    true
    false
    false
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
    true
    true
    true
    false
    false
    true
    true
    true
    true
    false
    refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl
    refl refl refl refl refl refl refl refl
    refl refl
    refl refl refl refl refl refl refl refl
    refl refl refl refl refl refl
    refl refl refl
    refl
    "G1 is source-written closed. The Lean companion constructs the floor-certified witness, proves the explicit combined L1 and K0 bounds, defines T_Q, and certifies T_Q<T_PT without decimal approximations. The scalar proof uses deliberately coarse theorem-bearing inequalities: cosh(1)<2, cosh(pi+1)<243, pi+1<5 and pi>3, yielding K0<4e9 and T_Q<5e10<3000175332800. Above the Platt-Trudgian cutoff the quantitative-band witness therefore has no remaining G1 hypothesis."
    "G3 representation is now source-written through the preferred symmetric global t-centred Abel consumer. Negative-height transport is endpoint-correct, both boundary terms tend to zero, the literal half-open zero windows are exhausted cofinally on the actual Zeros subtype, the smooth mu windows exhaust the full-line integral, and therefore the finite centred residual tends to global signedNMuPair. The preferred combined Abel partial L_n+R_n then tends to -signedNMuPair directly from the finite Abel identity. Separate one-sided correlation-integral limits remain retained as a strictly stronger optional producer interface rather than Clay-facing debt. Full-line mu-integrability is source-written from Zeta23.EF.integrable_paperFT_mul_mu. The exact completedSignedResidual=combinedCluster identity is paid, and outward-pointing centred discrepancy remains a wrong-sign diagnostic."
    "Superseded means retained and attributable but not on the preferred Clay-facing min-cut. In particular the old universal lower bound over every arbitrary QuarticFourSignedPolePair is stronger than needed and is retained only as a donor interface."
    "Authoritative high cut: G1 is source-written closed, and the preferred global symmetric centered-Abel representation is source-written. The only Clay-facing high-side analytic wall is now the joint G3 completed-residual inequality W.completedSignedResidual < 2*W.combinedZeroHeightDefect rho. Individual one-sided improper correlation limits remain optional stronger producers only. RH remains unproved because G3 is unpaid, and no exact-head Lean/Agda kernel receipt is claimed for this source tranche."

quarticTerminalCompilerShape :
  {ell : Level} ->
  (C : Compiler.QuarticSignedPoleCompiler {ell}) ->
  Compiler.BandCoverage C ->
  Compiler.JointSignedCompletedResidual C ->
  Compiler.Contradiction
quarticTerminalCompilerShape =
  Compiler.compileQuarticSignedPoleContradiction
