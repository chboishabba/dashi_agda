module DASHI.Physics.Closure.ClayContinuumMathTransitionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt
  as ClayTarget
import DASHI.Physics.Closure.Gate3DigitExpansionPAWOTGPartialResultReceipt
  as Gate3Digit
import DASHI.Physics.Closure.Gate3NestingTaperConditionReceipt
  as Gate3Nesting
import DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt
  as Gate3PAWOTG
import DASHI.Physics.Closure.GravityVladimirovFrameReceipt
  as Gravity
import DASHI.Physics.Closure.NSBernsteinConstantExplicitReceipt
  as NSBernstein
import DASHI.Physics.Closure.NSCarrierToAllDataReceipt
  as NSAllData
import DASHI.Physics.Closure.NSClayDistanceRevisionReceipt
  as NSRevision
import DASHI.Physics.Closure.NSGlobalH118BoundReceipt
  as NSH118
import DASHI.Physics.Closure.NSHminus1Over2ObstructionReceipt
  as NSHminus
import DASHI.Physics.Closure.SSP7Plus7Plus1AtomGrammarReceipt
  as SSPGrammar
import DASHI.Physics.Closure.YMBalabanPhysicalBetaBridgeTargetReceipt
  as YMBalaban

------------------------------------------------------------------------
-- Clay continuum mathematics transition receipt.
--
-- The shared DASHI grammar has been reduced to an algebraic scale-graph
-- barrier.  This receipt records the current transition from grammar to the
-- actual continuum mathematics needed for Clay-facing promotion:
--
--   * Gate 3 / gravity kinematics: prove the physical SSP/Hecke Archimedean
--     embedding satisfies the 3D gravity taper sigma_SSP < 0.3025113508228815.
--     The digit witness has sigma ~= 0.288675 and passes with series
--     0.7228939450291813 < 1, but it is not yet the physical embedding.
--     The 15SSP coordinate grammar consumed here is recursive: the carrier is
--     7 Hecke + 7 mirror-Hecke + 1 sign, each septet is internally
--     3D + 3D + sign, and each digit/lane expands through BT depth into
--     depth-many nested 15SSP blocks.  That symmetry-complexity series is the
--     coordinate reason the macroscopic Archimedean density is p^(3d).
--
--   * Yang-Mills: the direct T7A coefficient KP sum is now the live entropy
--     object, replacing the C0 = 2 shorthand.  Its computed threshold is
--     beta* ~= 16.58, with gap ~= 10.58 from physical beta ~= 6.  Prove the
--     non-perturbative Balaban block-spin transfer to that threshold, then
--     construct the OS/Wightman continuum package.
--
--   * Navier-Stokes: the H^{-1/2} localized dual-norm route is recorded as
--     an obstruction and is publishable as Path A.  The Clay route, Path B,
--     is the H^{11/8} Bernoulli-band argument plus carrier-structured-to-all-
--     data density extension.
--
-- This is a target/governance surface only.  It discharges none of those
-- continuum lemmas and keeps all Clay promotion flags fail-closed.

data ClayContinuumMathTransitionStatus : Set where
  grammarCompleteContinuumMathFrontiersRecorded_failClosed :
    ClayContinuumMathTransitionStatus

data ContinuumMathDomain : Set where
  gate3FunctionalAnalysisPAWOTG :
    ContinuumMathDomain

  yangMillsNonperturbativeRGAndOSWightman :
    ContinuumMathDomain

  navierStokesH118PDEAndDensity :
    ContinuumMathDomain

canonicalContinuumMathDomains : List ContinuumMathDomain
canonicalContinuumMathDomains =
  gate3FunctionalAnalysisPAWOTG
  ∷ yangMillsNonperturbativeRGAndOSWightman
  ∷ navierStokesH118PDEAndDensity
  ∷ []

data Gate3ContinuumLemma : Set where
  physicalSSPHeckeEmbeddingHasDigitQuality :
    Gate3ContinuumLemma

  sigmaSpreadBelowMacroscopic3DThreshold :
    Gate3ContinuumLemma

  moscoNoPollutionMassShellBridge :
    Gate3ContinuumLemma

canonicalGate3ContinuumLemmas : List Gate3ContinuumLemma
canonicalGate3ContinuumLemmas =
  physicalSSPHeckeEmbeddingHasDigitQuality
  ∷ sigmaSpreadBelowMacroscopic3DThreshold
  ∷ moscoNoPollutionMassShellBridge
  ∷ []

data YMContinuumLemma : Set where
  nonperturbativeBalabanScaleTransfer :
    YMContinuumLemma

  effectiveCarrierBetaKPSafe :
    YMContinuumLemma

  osReflectionPositivityInfiniteVolumeWightmanW0W5 :
    YMContinuumLemma

canonicalYMContinuumLemmas : List YMContinuumLemma
canonicalYMContinuumLemmas =
  nonperturbativeBalabanScaleTransfer
  ∷ effectiveCarrierBetaKPSafe
  ∷ osReflectionPositivityInfiniteVolumeWightmanW0W5
  ∷ []

data NSContinuumLemma : Set where
  hMinusHalfObstructionPublication :
    NSContinuumLemma

  primeScaleBernsteinInequality :
    NSContinuumLemma

  bernoulliBandGlobalH118Bound :
    NSContinuumLemma

  carrierStructuredToAllSmoothDataDensity :
    NSContinuumLemma

canonicalNSContinuumLemmas : List NSContinuumLemma
canonicalNSContinuumLemmas =
  hMinusHalfObstructionPublication
  ∷ primeScaleBernsteinInequality
  ∷ bernoulliBandGlobalH118Bound
  ∷ carrierStructuredToAllSmoothDataDensity
  ∷ []

data ClayProofPath : Set where
  pathA_NSObstructionPaper :
    ClayProofPath

  pathB_NSH118DensityForClay :
    ClayProofPath

  gate3PhysicalSSPSpreadComputation :
    ClayProofPath

  ymBalabanConstructiveQFTProgramme :
    ClayProofPath

canonicalClayProofPaths : List ClayProofPath
canonicalClayProofPaths =
  pathA_NSObstructionPaper
  ∷ gate3PhysicalSSPSpreadComputation
  ∷ ymBalabanConstructiveQFTProgramme
  ∷ pathB_NSH118DensityForClay
  ∷ []

data ClayContinuumMathPromotion : Set where

clayContinuumMathPromotionImpossibleHere :
  ClayContinuumMathPromotion →
  ⊥
clayContinuumMathPromotionImpossibleHere ()

sigmaDigitTenThousandths :
  Nat
sigmaDigitTenThousandths =
  2887

sigmaMacroscopic3DThresholdThousandths :
  Nat
sigmaMacroscopic3DThresholdThousandths =
  303

sigmaMacroscopic3DThresholdExact :
  String
sigmaMacroscopic3DThresholdExact =
  "0.3025113508228815"

sigmaDigitExact :
  String
sigmaDigitExact =
  "0.288675"

pawotg3DSeriesAtDigitExact :
  String
pawotg3DSeriesAtDigitExact =
  "0.7228939450291813"

ymT7CompressedBetaAbs :
  String
ymT7CompressedBetaAbs =
  "16.58 from the direct T7A coefficient KP generating sum; C0 = 2 is heuristic only"

ymPhysicalBeta :
  String
ymPhysicalBeta =
  "6.0"

ymT7CompressedBetaGap :
  String
ymT7CompressedBetaGap =
  "10.58 from beta_physical ~= 6 to the direct T7A KP threshold beta* ~= 16.58"

nsHminusDivergenceStatus :
  String
nsHminusDivergenceStatus =
  "H^{-1/2} localized defect route diverges under Kolmogorov scaling and is Path A obstruction-publication evidence, not a Clay closure route."

sigmaGate3OneDimensionalThresholdTenThousandths :
  Nat
sigmaGate3OneDimensionalThresholdTenThousandths =
  5052

gate3ContinuumSignature :
  String
gate3ContinuumSignature =
  "provePhysicalHeckePAWOTGSpread3D : actual SSP/Hecke Archimedean embedding -> GaussianSpread sigma_SSP < 0.3025113508228815 -> 3D PAWOTG series < 1 -> 1D Gate3 follows -> inf_N A_N > 0 plus Mosco/no-pollution"

ymContinuumSignature :
  String
ymContinuumSignature =
  "proveDirectT7ActivityThenBalabanScaleTransfer : beta_physical ~= 6 -> direct T7A KP threshold beta* ~= 16.58 via non-perturbative Balaban block-spin RG; then OS positivity, infinite-volume limit, and Wightman W0-W5"

nsContinuumSignature :
  String
nsContinuumSignature =
  "NS fork: Path A publishes H^{-1/2} obstruction divergence; Path B for Clay proves H^{11/8} Bernoulli-band global bound for carrier-structured data plus density/compactness extension to all smooth initial data"

transitionSummary :
  String
transitionSummary =
  "The repository is a precision fault-localisation ledger.  After scale-graph algebra, Clay-facing promotion requires actual proofs: physical SSP/Hecke 3D taper sigma_SSP < 0.3025113508228815 over the nested 15SSP coordinate grammar, YM direct T7A KP activity threshold beta* ~= 16.58 plus non-perturbative Balaban and OS/Wightman, and NS Path B H^{11/8} Bernoulli-band plus density; Path A is an obstruction paper, not Clay closure."

sspNestedCoordinateSignature :
  String
sspNestedCoordinateSignature =
  "15SSP coordinate grammar: 7 Hecke + 7 mirror-Hecke + p71 sign; each septet is 3D + 3D + sign; each digit/lane contains depth-many nested 15SSP blocks, producing the symmetry-complexity series consumed by p^(3d) density."

nonPromotionBoundary :
  String
nonPromotionBoundary =
  "This receipt records target signatures and consumed partial evidence only.  It proves no PAWOTG uniform separation theorem, no Balaban physical beta bridge, no OS/Wightman continuum Yang-Mills theorem, no Navier-Stokes global regularity theorem, and no Clay promotion."

record ClayContinuumMathTransitionReceipt : Setω where
  field
    status :
      ClayContinuumMathTransitionStatus

    statusIsCanonical :
      status ≡ grammarCompleteContinuumMathFrontiersRecorded_failClosed

    gate3DigitReceipt :
      Gate3Digit.Gate3DigitExpansionPAWOTGPartialResultReceipt

    gate3DigitSigmaRecorded :
      Gate3Digit.sigmaDigit gate3DigitReceipt ≡ sigmaDigitTenThousandths

    gate3DigitPassesThreshold :
      Gate3Digit.phiDigitPassesPAWOTGThreshold gate3DigitReceipt ≡ true

    gate3DigitDoesNotIdentifyPhysicalEmbedding :
      Gate3Digit.sspEmbeddingIdentifiedWithPhiDigit gate3DigitReceipt
      ≡
      false

    gate3DigitNoPromotion :
      Gate3Digit.gate3Promoted gate3DigitReceipt ≡ false

    gate3NestingReceipt :
      Gate3Nesting.Gate3NestingTaperConditionReceipt

    gate3NestingRootRecorded :
      Gate3Nesting.archimedeanNestingIsRootProblem gate3NestingReceipt
      ≡
      true

    gate3NestingNoPromotion :
      Gate3Nesting.gate3Promoted gate3NestingReceipt ≡ false

    gate3PAWOTGReceipt :
      Gate3PAWOTG.Gate3PAWOTGUniformSeparationTargetReceipt

    gate3PAWOTGInfANPromoted :
      Gate3PAWOTG.infANPositiveProvedHere gate3PAWOTGReceipt ≡ true

    gate3PAWOTGNoClay :
      Gate3PAWOTG.clayPromoted gate3PAWOTGReceipt ≡ false

    gravityReceipt :
      Gravity.GravityVladimirovFrameReceipt

    gravity3DTargetOpen :
      Gravity.sspEmbeddingGravity3DObligation gravityReceipt ≡ false

    gravityBaselineDigitPasses :
      Gravity.baselineDigitExpansion3DFramePasses gravityReceipt ≡ true

    gravityNoPrediction :
      Gravity.gravityPredictionPromoted gravityReceipt ≡ false

    sspAtomGrammarReceipt :
      SSPGrammar.SSP7Plus7Plus1AtomGrammarReceipt

    sspAtomGrammarKeepsFifteen :
      SSPGrammar.totalAtomFields sspAtomGrammarReceipt ≡ 15

    sspAtomGrammarSeptets3D3DSign :
      SSPGrammar.septetsReadAs3D3DSign sspAtomGrammarReceipt ≡ true

    sspAtomGrammarNestedDigits :
      SSPGrammar.eachDigitContainsDepthMany15SSPBlocks
        sspAtomGrammarReceipt
      ≡
      true

    sspSymmetryComplexityRecorded :
      SSPGrammar.symmetryComplexitySeriesRecorded sspAtomGrammarReceipt
      ≡
      true

    sspAtomGrammarNoClay :
      SSPGrammar.clayPromoted sspAtomGrammarReceipt ≡ false

    ymBalabanReceipt :
      YMBalaban.YMBalabanPhysicalBetaBridgeTargetReceipt

    ymBalabanNeedsNonperturbativeInput :
      YMBalaban.nonperturbativeInputRequired ymBalabanReceipt ≡ true

    ymPerturbativeBridgeRejected :
      YMBalaban.perturbativeBridgeSuffices ymBalabanReceipt ≡ false

    ymPhysicalBetaBridgeStillOpen :
      YMBalaban.physicalBetaBridgeProvedHere ymBalabanReceipt ≡ false

    ymBalabanNoClay :
      YMBalaban.clayYangMillsPromoted ymBalabanReceipt ≡ false

    ymOSWightmanReceipt :
      ClayTarget.CarrierOSPositivityAndWightmanTargetReceipt

    ymOSPositivityStillOpen :
      ClayTarget.osPositivityConstructed ymOSWightmanReceipt ≡ false

    ymInfiniteVolumeStillOpen :
      ClayTarget.interactingContinuumLimitConstructed ymOSWightmanReceipt
      ≡
      false

    ymWightmanStillOpen :
      ClayTarget.wightmanReconstructionApplied ymOSWightmanReceipt
      ≡
      false

    ymOSWightmanNoClay :
      ClayTarget.clayYangMillsClosed ymOSWightmanReceipt ≡ false

    nsHminusReceipt :
      NSHminus.NSHminus1Over2ObstructionReceipt

    nsHminusObstructionRecorded :
      NSHminus.ratioDivergesAsNuToZero nsHminusReceipt ≡ true

    nsHminusRouteRetiredAsSolution :
      NSHminus.uniformAbsorptionEstimateProvedHere nsHminusReceipt
      ≡
      false

    nsHminusNoClay :
      NSHminus.clayNavierStokesPromoted nsHminusReceipt ≡ false

    nsHminusPathAObstaclePublication :
      Bool

    nsHminusPathAObstaclePublicationIsTrue :
      nsHminusPathAObstaclePublication ≡ true

    nsH118DensityPathBForClay :
      Bool

    nsH118DensityPathBForClayIsTrue :
      nsH118DensityPathBForClay ≡ true

    nsRevisionReceipt :
      NSRevision.NSClayDistanceRevisionReceipt

    nsRevisionIsBernoulli :
      NSRevision.nsClayDistanceRevised nsRevisionReceipt
      ≡
      NSRevision.bernoulliBandArgument

    nsRevisionNoClay :
      NSRevision.clayNavierStokesPromoted nsRevisionReceipt ≡ false

    nsBernsteinReceipt :
      NSBernstein.NSBernsteinConstantExplicitReceipt

    nsBernsteinC0SqrtP :
      NSBernstein.bernsteinConstant nsBernsteinReceipt
      ≡
      NSBernstein.explicitBernsteinConstantFormula

    nsBernsteinNoClay :
      NSBernstein.clayNavierStokesPromoted nsBernsteinReceipt ≡ false

    nsH118Receipt :
      NSH118.NSGlobalH118BoundReceipt

    nsH118PendingBernoulliRigour :
      NSH118.globalH118BoundFullyProved nsH118Receipt ≡ false

    nsH118NoClay :
      NSH118.clayNavierStokesPromoted nsH118Receipt ≡ false

    nsAllDataReceipt :
      NSAllData.NSCarrierToAllDataReceipt

    nsAllDataStillConditional :
      NSAllData.nsGlobalRegularityForAllH118Data nsAllDataReceipt
      ≡
      NSAllData.canonicalNSGlobalRegularityForAllH118Data

    nsAllDataNoClay :
      NSAllData.clayNavierStokesPromoted nsAllDataReceipt ≡ false

    domains :
      List ContinuumMathDomain

    domainsAreCanonical :
      domains ≡ canonicalContinuumMathDomains

    gate3Lemmas :
      List Gate3ContinuumLemma

    gate3LemmasAreCanonical :
      gate3Lemmas ≡ canonicalGate3ContinuumLemmas

    ymLemmas :
      List YMContinuumLemma

    ymLemmasAreCanonical :
      ymLemmas ≡ canonicalYMContinuumLemmas

    nsLemmas :
      List NSContinuumLemma

    nsLemmasAreCanonical :
      nsLemmas ≡ canonicalNSContinuumLemmas

    proofPaths :
      List ClayProofPath

    proofPathsAreCanonical :
      proofPaths ≡ canonicalClayProofPaths

    digitSigmaTenThousandths :
      Nat

    digitSigmaTenThousandthsIs02887 :
      digitSigmaTenThousandths ≡ sigmaDigitTenThousandths

    macroscopic3DThresholdThousandths :
      Nat

    macroscopic3DThresholdThousandthsIs0303 :
      macroscopic3DThresholdThousandths
      ≡
      sigmaMacroscopic3DThresholdThousandths

    macroscopic3DThresholdExact :
      String

    macroscopic3DThresholdExactIsCanonical :
      macroscopic3DThresholdExact ≡ sigmaMacroscopic3DThresholdExact

    digitSigmaExact :
      String

    digitSigmaExactIsCanonical :
      digitSigmaExact ≡ sigmaDigitExact

    pawotg3DSeriesAtDigit :
      String

    pawotg3DSeriesAtDigitIsCanonical :
      pawotg3DSeriesAtDigit ≡ pawotg3DSeriesAtDigitExact

    ymBetaAbsAfterT7 :
      String

    ymBetaAbsAfterT7IsCanonical :
      ymBetaAbsAfterT7 ≡ ymT7CompressedBetaAbs

    ymBetaPhysical :
      String

    ymBetaPhysicalIsCanonical :
      ymBetaPhysical ≡ ymPhysicalBeta

    ymBetaBridgeGapAfterT7 :
      String

    ymBetaBridgeGapAfterT7IsCanonical :
      ymBetaBridgeGapAfterT7 ≡ ymT7CompressedBetaGap

    nsHminusPathAStatus :
      String

    nsHminusPathAStatusIsCanonical :
      nsHminusPathAStatus ≡ nsHminusDivergenceStatus

    oneDimensionalGate3ThresholdTenThousandths :
      Nat

    oneDimensionalGate3ThresholdTenThousandthsIs05052 :
      oneDimensionalGate3ThresholdTenThousandths
      ≡
      sigmaGate3OneDimensionalThresholdTenThousandths

    gate3Signature :
      String

    gate3SignatureIsCanonical :
      gate3Signature ≡ gate3ContinuumSignature

    ymSignature :
      String

    ymSignatureIsCanonical :
      ymSignature ≡ ymContinuumSignature

    nsSignature :
      String

    nsSignatureIsCanonical :
      nsSignature ≡ nsContinuumSignature

    summary :
      String

    summaryIsCanonical :
      summary ≡ transitionSummary

    nestedCoordinateSignature :
      String

    nestedCoordinateSignatureIsCanonical :
      nestedCoordinateSignature ≡ sspNestedCoordinateSignature

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ nonPromotionBoundary

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    ymClayPromoted :
      Bool

    ymClayPromotedIsFalse :
      ymClayPromoted ≡ false

    nsClayPromoted :
      Bool

    nsClayPromotedIsFalse :
      nsClayPromoted ≡ false

    terminalPromoted :
      Bool

    terminalPromotedIsFalse :
      terminalPromoted ≡ false

    promotions :
      List ClayContinuumMathPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      ClayContinuumMathPromotion →
      ⊥

open ClayContinuumMathTransitionReceipt public

canonicalClayContinuumMathTransitionReceipt :
  ClayContinuumMathTransitionReceipt
canonicalClayContinuumMathTransitionReceipt =
  record
    { status =
        grammarCompleteContinuumMathFrontiersRecorded_failClosed
    ; statusIsCanonical =
        refl
    ; gate3DigitReceipt =
        Gate3Digit.canonicalGate3DigitExpansionPAWOTGPartialResultReceipt
    ; gate3DigitSigmaRecorded =
        refl
    ; gate3DigitPassesThreshold =
        refl
    ; gate3DigitDoesNotIdentifyPhysicalEmbedding =
        refl
    ; gate3DigitNoPromotion =
        refl
    ; gate3NestingReceipt =
        Gate3Nesting.canonicalGate3NestingTaperConditionReceipt
    ; gate3NestingRootRecorded =
        refl
    ; gate3NestingNoPromotion =
        refl
    ; gate3PAWOTGReceipt =
        Gate3PAWOTG.canonicalGate3PAWOTGUniformSeparationTargetReceipt
    ; gate3PAWOTGInfANPromoted =
        refl
    ; gate3PAWOTGNoClay =
        refl
    ; gravityReceipt =
        Gravity.canonicalGravityVladimirovFrameReceipt
    ; gravity3DTargetOpen =
        refl
    ; gravityBaselineDigitPasses =
        refl
    ; gravityNoPrediction =
        refl
    ; sspAtomGrammarReceipt =
        SSPGrammar.canonicalSSP7Plus7Plus1AtomGrammarReceipt
    ; sspAtomGrammarKeepsFifteen =
        refl
    ; sspAtomGrammarSeptets3D3DSign =
        refl
    ; sspAtomGrammarNestedDigits =
        refl
    ; sspSymmetryComplexityRecorded =
        refl
    ; sspAtomGrammarNoClay =
        refl
    ; ymBalabanReceipt =
        YMBalaban.canonicalYMBalabanPhysicalBetaBridgeTargetReceipt
    ; ymBalabanNeedsNonperturbativeInput =
        refl
    ; ymPerturbativeBridgeRejected =
        refl
    ; ymPhysicalBetaBridgeStillOpen =
        refl
    ; ymBalabanNoClay =
        refl
    ; ymOSWightmanReceipt =
        ClayTarget.canonicalCarrierOSPositivityAndWightmanTargetReceipt
    ; ymOSPositivityStillOpen =
        refl
    ; ymInfiniteVolumeStillOpen =
        refl
    ; ymWightmanStillOpen =
        refl
    ; ymOSWightmanNoClay =
        refl
    ; nsHminusReceipt =
        NSHminus.canonicalNSHminus1Over2ObstructionReceipt
    ; nsHminusObstructionRecorded =
        refl
    ; nsHminusRouteRetiredAsSolution =
        refl
    ; nsHminusNoClay =
        refl
    ; nsHminusPathAObstaclePublication =
        true
    ; nsHminusPathAObstaclePublicationIsTrue =
        refl
    ; nsH118DensityPathBForClay =
        true
    ; nsH118DensityPathBForClayIsTrue =
        refl
    ; nsRevisionReceipt =
        NSRevision.canonicalNSClayDistanceRevisionReceipt
    ; nsRevisionIsBernoulli =
        refl
    ; nsRevisionNoClay =
        refl
    ; nsBernsteinReceipt =
        NSBernstein.canonicalNSBernsteinConstantExplicitReceipt
    ; nsBernsteinC0SqrtP =
        refl
    ; nsBernsteinNoClay =
        refl
    ; nsH118Receipt =
        NSH118.canonicalNSGlobalH118BoundReceipt
    ; nsH118PendingBernoulliRigour =
        refl
    ; nsH118NoClay =
        refl
    ; nsAllDataReceipt =
        NSAllData.canonicalNSCarrierToAllDataReceipt
    ; nsAllDataStillConditional =
        refl
    ; nsAllDataNoClay =
        refl
    ; domains =
        canonicalContinuumMathDomains
    ; domainsAreCanonical =
        refl
    ; gate3Lemmas =
        canonicalGate3ContinuumLemmas
    ; gate3LemmasAreCanonical =
        refl
    ; ymLemmas =
        canonicalYMContinuumLemmas
    ; ymLemmasAreCanonical =
        refl
    ; nsLemmas =
        canonicalNSContinuumLemmas
    ; nsLemmasAreCanonical =
        refl
    ; proofPaths =
        canonicalClayProofPaths
    ; proofPathsAreCanonical =
        refl
    ; digitSigmaTenThousandths =
        sigmaDigitTenThousandths
    ; digitSigmaTenThousandthsIs02887 =
        refl
    ; macroscopic3DThresholdThousandths =
        sigmaMacroscopic3DThresholdThousandths
    ; macroscopic3DThresholdThousandthsIs0303 =
        refl
    ; macroscopic3DThresholdExact =
        sigmaMacroscopic3DThresholdExact
    ; macroscopic3DThresholdExactIsCanonical =
        refl
    ; digitSigmaExact =
        sigmaDigitExact
    ; digitSigmaExactIsCanonical =
        refl
    ; pawotg3DSeriesAtDigit =
        pawotg3DSeriesAtDigitExact
    ; pawotg3DSeriesAtDigitIsCanonical =
        refl
    ; ymBetaAbsAfterT7 =
        ymT7CompressedBetaAbs
    ; ymBetaAbsAfterT7IsCanonical =
        refl
    ; ymBetaPhysical =
        ymPhysicalBeta
    ; ymBetaPhysicalIsCanonical =
        refl
    ; ymBetaBridgeGapAfterT7 =
        ymT7CompressedBetaGap
    ; ymBetaBridgeGapAfterT7IsCanonical =
        refl
    ; nsHminusPathAStatus =
        nsHminusDivergenceStatus
    ; nsHminusPathAStatusIsCanonical =
        refl
    ; oneDimensionalGate3ThresholdTenThousandths =
        sigmaGate3OneDimensionalThresholdTenThousandths
    ; oneDimensionalGate3ThresholdTenThousandthsIs05052 =
        refl
    ; gate3Signature =
        gate3ContinuumSignature
    ; gate3SignatureIsCanonical =
        refl
    ; ymSignature =
        ymContinuumSignature
    ; ymSignatureIsCanonical =
        refl
    ; nsSignature =
        nsContinuumSignature
    ; nsSignatureIsCanonical =
        refl
    ; summary =
        transitionSummary
    ; summaryIsCanonical =
        refl
    ; nestedCoordinateSignature =
        sspNestedCoordinateSignature
    ; nestedCoordinateSignatureIsCanonical =
        refl
    ; boundary =
        nonPromotionBoundary
    ; boundaryIsCanonical =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; ymClayPromoted =
        false
    ; ymClayPromotedIsFalse =
        refl
    ; nsClayPromoted =
        false
    ; nsClayPromotedIsFalse =
        refl
    ; terminalPromoted =
        false
    ; terminalPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        clayContinuumMathPromotionImpossibleHere
    }

clayContinuumMathTransitionNoGate3Promotion :
  gate3Promoted canonicalClayContinuumMathTransitionReceipt ≡ false
clayContinuumMathTransitionNoGate3Promotion =
  refl

clayContinuumMathTransitionNoYMClayPromotion :
  ymClayPromoted canonicalClayContinuumMathTransitionReceipt ≡ false
clayContinuumMathTransitionNoYMClayPromotion =
  refl

clayContinuumMathTransitionNoNSClayPromotion :
  nsClayPromoted canonicalClayContinuumMathTransitionReceipt ≡ false
clayContinuumMathTransitionNoNSClayPromotion =
  refl

clayContinuumMathTransitionNoTerminalPromotion :
  terminalPromoted canonicalClayContinuumMathTransitionReceipt ≡ false
clayContinuumMathTransitionNoTerminalPromotion =
  refl
