module DASHI.Analysis.RiemannAristotleG2CurrentCutExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record AristotleG2CurrentCut : Set where
  constructor aristotle-g2-current-cut
  field
    g1ThreeCoordinateToGenericGramClosed : Bool
    g1ThreeCoordinateToGenericGramClosedIsTrue :
      g1ThreeCoordinateToGenericGramClosed ≡ true

    g2aOrderedPairGramDebtClosed : Bool
    g2aOrderedPairGramDebtClosedIsTrue : g2aOrderedPairGramDebtClosed ≡ true

    g2bRawThreeTaperBilinearCompilerClosed : Bool
    g2bRawThreeTaperBilinearCompilerClosedIsTrue :
      g2bRawThreeTaperBilinearCompilerClosed ≡ true

    checkedLeanNormDeterminantIdentityExists : Bool
    checkedLeanNormDeterminantIdentityExistsIsTrue :
      checkedLeanNormDeterminantIdentityExists ≡ true

    g2cPolarizationDerivationClosedInAgda : Bool
    g2cPolarizationDerivationClosedInAgdaIsTrue :
      g2cPolarizationDerivationClosedInAgda ≡ true

    g2cFreshLeanBilinearKernelReceiptPresent : Bool
    g2cFreshLeanBilinearKernelReceiptPresentIsTrue :
      g2cFreshLeanBilinearKernelReceiptPresent ≡ true

    finiteSignedGramLedgerKernelCheckedInLean : Bool
    finiteSignedGramLedgerKernelCheckedInLeanIsTrue :
      finiteSignedGramLedgerKernelCheckedInLean ≡ true

    scalarGramDebtIdentityKernelCheckedInLean : Bool
    scalarGramDebtIdentityKernelCheckedInLeanIsTrue :
      scalarGramDebtIdentityKernelCheckedInLean ≡ true

    reflectionPairOddSinhSinCancellationClosedInLean : Bool
    reflectionPairOddSinhSinCancellationClosedInLeanIsTrue :
      reflectionPairOddSinhSinCancellationClosedInLean ≡ true

    reflectionOnlyForcesRemainingGramCancellation : Bool
    reflectionOnlyForcesRemainingGramCancellationIsFalse :
      reflectionOnlyForcesRemainingGramCancellation ≡ false

    reflectionDuplicatePositiveNoGoKernelCheckedInLean : Bool
    reflectionDuplicatePositiveNoGoKernelCheckedInLeanIsTrue :
      reflectionDuplicatePositiveNoGoKernelCheckedInLean ≡ true

    g2dReducedToSingleSignedScalarDeterminantSum : Bool
    g2dReducedToSingleSignedScalarDeterminantSumIsTrue :
      g2dReducedToSingleSignedScalarDeterminantSum ≡ true

    g2eDeterminantTaperKernelCompressionClosed : Bool
    g2eDeterminantTaperKernelCompressionClosedIsTrue :
      g2eDeterminantTaperKernelCompressionClosed ≡ true

    literalNearCoreSingleIntegralKernelCheckedInLean : Bool
    literalNearCoreSingleIntegralKernelCheckedInLeanIsTrue :
      literalNearCoreSingleIntegralKernelCheckedInLean ≡ true

    literalNearCoreEnergyScalarizationKernelCheckedInLean : Bool
    literalNearCoreEnergyScalarizationKernelCheckedInLeanIsTrue :
      literalNearCoreEnergyScalarizationKernelCheckedInLean ≡ true

    literalFarRemainderInSameScalarCoordinateKernelCheckedInLean : Bool
    literalFarRemainderInSameScalarCoordinateKernelCheckedInLeanIsTrue :
      literalFarRemainderInSameScalarCoordinateKernelCheckedInLean ≡ true

    literalScalarOffEnergyConsumerKernelCheckedInLean : Bool
    literalScalarOffEnergyConsumerKernelCheckedInLeanIsTrue :
      literalScalarOffEnergyConsumerKernelCheckedInLean ≡ true

    functionalAndConjugationSymmetriesGiveTargetCenteredGapPairing : Bool
    functionalAndConjugationSymmetriesGiveTargetCenteredGapPairingIsFalse :
      functionalAndConjugationSymmetriesGiveTargetCenteredGapPairing ≡ false

    localZeroCountControlsRemainingOscillatoryPhase : Bool
    localZeroCountControlsRemainingOscillatoryPhaseIsFalse :
      localZeroCountControlsRemainingOscillatoryPhase ≡ false

    montgomeryVaughanDirectlyClosesLocalZeroCosineSum : Bool
    montgomeryVaughanDirectlyClosesLocalZeroCosineSumIsFalse :
      montgomeryVaughanDirectlyClosesLocalZeroCosineSum ≡ false

    targetCenteredLocalZeroExponentialSumBoundClosed : Bool
    targetCenteredLocalZeroExponentialSumBoundClosedIsFalse :
      targetCenteredLocalZeroExponentialSumBoundClosed ≡ false

    projectiveBalanceStrictInequalityNoGoKernelCheckedInLean : Bool
    projectiveBalanceStrictInequalityNoGoKernelCheckedInLeanIsTrue :
      projectiveBalanceStrictInequalityNoGoKernelCheckedInLean ≡ true

    projectiveBalanceStrictInequalityNoGoClosedInAgda : Bool
    projectiveBalanceStrictInequalityNoGoClosedInAgdaIsTrue :
      projectiveBalanceStrictInequalityNoGoClosedInAgda ≡ true

    strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissible : Bool
    strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissibleIsFalse :
      strictOffEnergyBelowClusterUnderUnbrokenBalanceAdmissible ≡ false

    balanceBreakingPremiseRequiredForStrictContradictionRoute : Bool
    balanceBreakingPremiseRequiredForStrictContradictionRouteIsTrue :
      balanceBreakingPremiseRequiredForStrictContradictionRoute ≡ true

    genericGramOrSchurAlgebraRemaining : Bool
    genericGramOrSchurAlgebraRemainingIsFalse :
      genericGramOrSchurAlgebraRemaining ≡ false

    firstUnprovedHarmonicAnalysisTheorem : String
    contradictionArchitectureBoundary : String

    leanProofsTransportedIntoAgda : Bool
    leanProofsTransportedIntoAgdaIsFalse : leanProofsTransportedIntoAgda ≡ false

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    boundedReading : String

open AristotleG2CurrentCut public

canonicalAristotleG2CurrentCut : AristotleG2CurrentCut
canonicalAristotleG2CurrentCut =
  aristotle-g2-current-cut
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    false refl
    "For a constructed three-taper family g, radius r, deterministic nuisance directions n1,n2 with positive wedgeSq, and cutoff J>=1, bound the target-centered scalar integral integral q(u) * sum_{sigma in nearOffFinset(t,J)} m_sigma cosh(a_sigma u) cos((b_sigma-t)u) du with the exact constants needed by NearCoreDeterminantTaper.normSqP_elim2_offVec_lt_of_scalar_bound."
    "NearCoreDeterminantTaper.not_normSqP_elim2_offVec_lt_of_balance is kernel checked: if literal projective balance identifies the surviving off-ordinate energy with the cluster margin, the same energy cannot be strictly below that margin. Therefore a strict contradiction route must expose a genuine balance-breaking premise or changed comparison object; sharpening the scalar estimate while retaining unbroken balance is not an admissible final consumer."
    false refl
    false refl
    "The 8885-job Lean return closes G2c itself, the finite signed Gram ledger, scalar Gram-debt identity, reflection-duplicate no-go, the literal determinant-taper near scalarization, the finite exponential-sum form, the far remainder in the same determinant coordinate, and the scalar off-energy consumer. Agda retains these as checked-Lean provenance rather than imported proof terms. The first unproved harmonic-analysis theorem is the target-centered local zero cosine/exponential-sum bound. Separately, the newly checked projective-balance no-go blocks the old strict off-energy-below-cluster consumer under unbroken balance, so any final contradiction architecture must make the balance-breaking step explicit. No generic Gram or Schur algebra remains and RH is not derived."
