module DASHI.Physics.Closure.YMBruhatTitsToOSLatticeTransferBoundary where

-- Bruhat-Tits to OS/Wightman lattice-transfer boundary.
--
-- This receipt records the current honest Yang-Mills continuum-transfer
-- frontier:
--
--   finite BT/building gauge model
--   -> Wilson/lattice action comparison
--   -> reflection positivity
--   -> Dobrushin-Shlosman / exponential-clustering hypotheses
--   -> observable-class inclusion
--   -> no spectral pollution through the depth/continuum limit
--   -> OS/Wightman reconstruction candidate authority.
--
-- Recent external OS/mass-gap preprints are recorded here as authority
-- candidates only.  They do not, by themselves, instantiate the DASHI
-- Bruhat-Tits carrier, do not discharge the Wilson-action comparison, do not
-- prove BT reflection positivity or DS hypotheses, do not prove observable
-- inclusion, do not prove no spectral pollution, and do not promote Clay
-- Yang-Mills.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.YMGaugeZeroModeVacuumRigidityBoundary as Rigidity
import DASHI.Physics.Closure.YMHamiltonianDominatesFiniteHodgeDefectBoundary as Ham
import DASHI.Physics.Closure.YMLatticeMassGapAuthority as Authority
import DASHI.Physics.Closure.YMSelfAdjointHamiltonianQuotientGapBoundary as Gap

------------------------------------------------------------------------
-- Small local counting utility for ledger invariants.

listCount : {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Status and stages.

data YMBruhatTitsToOSLatticeTransferStatus : Set where
  externalOSCandidatessRecordedBTTransferStillMissing :
    YMBruhatTitsToOSLatticeTransferStatus

  bruhatTitsTransferBoundaryFailClosedClayPromotionBlocked :
    YMBruhatTitsToOSLatticeTransferStatus

data YMBruhatTitsToOSLatticeTransferStage : Set where
  finiteBTGaugeCarrierStage :
    YMBruhatTitsToOSLatticeTransferStage

  finiteGaugeZeroModeSheafRigidityStage :
    YMBruhatTitsToOSLatticeTransferStage

  hamiltonianDominatesDefectPlusHolonomyStage :
    YMBruhatTitsToOSLatticeTransferStage

  selfAdjointGaugeQuotientHamiltonianStage :
    YMBruhatTitsToOSLatticeTransferStage

  bTToWilsonActionComparisonStage :
    YMBruhatTitsToOSLatticeTransferStage

  reflectionPositiveTransferMatrixStage :
    YMBruhatTitsToOSLatticeTransferStage

  dobrushinShlosmanClusterHypothesesStage :
    YMBruhatTitsToOSLatticeTransferStage

  observableClassInclusionStage :
    YMBruhatTitsToOSLatticeTransferStage

  noSpectralPollutionDepthContinuumStage :
    YMBruhatTitsToOSLatticeTransferStage

  externalOSMassGapAuthorityCandidateStage :
    YMBruhatTitsToOSLatticeTransferStage

  clayPromotionGovernanceStage :
    YMBruhatTitsToOSLatticeTransferStage

canonicalYMBruhatTitsToOSLatticeTransferStages :
  List YMBruhatTitsToOSLatticeTransferStage
canonicalYMBruhatTitsToOSLatticeTransferStages =
  finiteBTGaugeCarrierStage
  ∷ finiteGaugeZeroModeSheafRigidityStage
  ∷ hamiltonianDominatesDefectPlusHolonomyStage
  ∷ selfAdjointGaugeQuotientHamiltonianStage
  ∷ bTToWilsonActionComparisonStage
  ∷ reflectionPositiveTransferMatrixStage
  ∷ dobrushinShlosmanClusterHypothesesStage
  ∷ observableClassInclusionStage
  ∷ noSpectralPollutionDepthContinuumStage
  ∷ externalOSMassGapAuthorityCandidateStage
  ∷ clayPromotionGovernanceStage
  ∷ []

------------------------------------------------------------------------
-- External authority candidates and required transfer hypotheses.

data ExternalYMMassGapAuthorityCandidate : Set where
  kirkTwentyTwentySixOSMassGapPreprintCandidate :
    ExternalYMMassGapAuthorityCandidate

  erikssonTwentyTwentySixVolumeUniformGapCandidate :
    ExternalYMMassGapAuthorityCandidate

  hasseltTwentyTwentySixReflectionPositiveReconstructionCandidate :
    ExternalYMMassGapAuthorityCandidate

canonicalExternalYMMassGapAuthorityCandidates :
  List ExternalYMMassGapAuthorityCandidate
canonicalExternalYMMassGapAuthorityCandidates =
  kirkTwentyTwentySixOSMassGapPreprintCandidate
  ∷ erikssonTwentyTwentySixVolumeUniformGapCandidate
  ∷ hasseltTwentyTwentySixReflectionPositiveReconstructionCandidate
  ∷ []

data BruhatTitsToOSRequiredHypothesis : Set where
  bTCarrierInstantiatesFiniteGaugeLattice :
    BruhatTitsToOSRequiredHypothesis

  bTWilsonActionComparison :
    BruhatTitsToOSRequiredHypothesis

  transferMatrixReflectionPositivity :
    BruhatTitsToOSRequiredHypothesis

  gaugeQuotientReflectionPositivity :
    BruhatTitsToOSRequiredHypothesis

  dobrushinShlosmanCompleteAnalyticity :
    BruhatTitsToOSRequiredHypothesis

  exponentialClusterHypothesis :
    BruhatTitsToOSRequiredHypothesis

  osAxiomSchwingerFunctionHypotheses :
    BruhatTitsToOSRequiredHypothesis

  wightmanReconstructionCompatibility :
    BruhatTitsToOSRequiredHypothesis

  observableClassInclusion :
    BruhatTitsToOSRequiredHypothesis

  gaugeInvariantObservableCompleteness :
    BruhatTitsToOSRequiredHypothesis

  noSpectralPollutionDepthLimit :
    BruhatTitsToOSRequiredHypothesis

  noSpectralPollutionContinuumLimit :
    BruhatTitsToOSRequiredHypothesis

  externalAuthorityAcceptanceToken :
    BruhatTitsToOSRequiredHypothesis

canonicalBruhatTitsToOSRequiredHypotheses :
  List BruhatTitsToOSRequiredHypothesis
canonicalBruhatTitsToOSRequiredHypotheses =
  bTCarrierInstantiatesFiniteGaugeLattice
  ∷ bTWilsonActionComparison
  ∷ transferMatrixReflectionPositivity
  ∷ gaugeQuotientReflectionPositivity
  ∷ dobrushinShlosmanCompleteAnalyticity
  ∷ exponentialClusterHypothesis
  ∷ osAxiomSchwingerFunctionHypotheses
  ∷ wightmanReconstructionCompatibility
  ∷ observableClassInclusion
  ∷ gaugeInvariantObservableCompleteness
  ∷ noSpectralPollutionDepthLimit
  ∷ noSpectralPollutionContinuumLimit
  ∷ externalAuthorityAcceptanceToken
  ∷ []

data BruhatTitsToOSLatticeTransferBlocker : Set where
  missingBTWilsonActionComparison :
    BruhatTitsToOSLatticeTransferBlocker

  missingBTReflectionPositiveTransferMatrix :
    BruhatTitsToOSLatticeTransferBlocker

  missingGaugeQuotientReflectionPositivity :
    BruhatTitsToOSLatticeTransferBlocker

  missingDobrusinShlosmanOrClusterHypotheses :
    BruhatTitsToOSLatticeTransferBlocker

  missingObservableClassInclusion :
    BruhatTitsToOSLatticeTransferBlocker

  missingGaugeInvariantObservableCompleteness :
    BruhatTitsToOSLatticeTransferBlocker

  missingNoSpectralPollutionDepthLimit :
    BruhatTitsToOSLatticeTransferBlocker

  missingNoSpectralPollutionContinuumLimit :
    BruhatTitsToOSLatticeTransferBlocker

  externalCandidatesNotAcceptedAuthority :
    BruhatTitsToOSLatticeTransferBlocker

  missingClayYangMillsAuthorityToken :
    BruhatTitsToOSLatticeTransferBlocker

canonicalBruhatTitsToOSLatticeTransferBlockers :
  List BruhatTitsToOSLatticeTransferBlocker
canonicalBruhatTitsToOSLatticeTransferBlockers =
  missingBTWilsonActionComparison
  ∷ missingBTReflectionPositiveTransferMatrix
  ∷ missingGaugeQuotientReflectionPositivity
  ∷ missingDobrusinShlosmanOrClusterHypotheses
  ∷ missingObservableClassInclusion
  ∷ missingGaugeInvariantObservableCompleteness
  ∷ missingNoSpectralPollutionDepthLimit
  ∷ missingNoSpectralPollutionContinuumLimit
  ∷ externalCandidatesNotAcceptedAuthority
  ∷ missingClayYangMillsAuthorityToken
  ∷ []

data BruhatTitsToOSLatticeTransferRow : Set where
  gaugeZeroModeRigidityBoundaryConsumedRow :
    BruhatTitsToOSLatticeTransferRow

  hamiltonianDominationBoundaryConsumedRow :
    BruhatTitsToOSLatticeTransferRow

  selfAdjointQuotientGapBoundaryConsumedRow :
    BruhatTitsToOSLatticeTransferRow

  latticeMassGapAuthorityCandidateConsumedRow :
    BruhatTitsToOSLatticeTransferRow

  externalTwentyTwentySixOSCandidatessRecordedRow :
    BruhatTitsToOSLatticeTransferRow

  externalCandidatesAreNotPromotionTokensRow :
    BruhatTitsToOSLatticeTransferRow

  bTToWilsonActionComparisonRequiredRow :
    BruhatTitsToOSLatticeTransferRow

  reflectionPositivityRequiredRow :
    BruhatTitsToOSLatticeTransferRow

  dSClusterHypothesesRequiredRow :
    BruhatTitsToOSLatticeTransferRow

  observableClassInclusionRequiredRow :
    BruhatTitsToOSLatticeTransferRow

  noSpectralPollutionRequiredRow :
    BruhatTitsToOSLatticeTransferRow

  oSWightmanTransferStillOpenRow :
    BruhatTitsToOSLatticeTransferRow

  continuumMassGapTransferStillOpenRow :
    BruhatTitsToOSLatticeTransferRow

  clayYangMillsPromotionHeldFalseRow :
    BruhatTitsToOSLatticeTransferRow

canonicalBruhatTitsToOSLatticeTransferRows :
  List BruhatTitsToOSLatticeTransferRow
canonicalBruhatTitsToOSLatticeTransferRows =
  gaugeZeroModeRigidityBoundaryConsumedRow
  ∷ hamiltonianDominationBoundaryConsumedRow
  ∷ selfAdjointQuotientGapBoundaryConsumedRow
  ∷ latticeMassGapAuthorityCandidateConsumedRow
  ∷ externalTwentyTwentySixOSCandidatessRecordedRow
  ∷ externalCandidatesAreNotPromotionTokensRow
  ∷ bTToWilsonActionComparisonRequiredRow
  ∷ reflectionPositivityRequiredRow
  ∷ dSClusterHypothesesRequiredRow
  ∷ observableClassInclusionRequiredRow
  ∷ noSpectralPollutionRequiredRow
  ∷ oSWightmanTransferStillOpenRow
  ∷ continuumMassGapTransferStillOpenRow
  ∷ clayYangMillsPromotionHeldFalseRow
  ∷ []

------------------------------------------------------------------------
-- Exact transfer targets.

data BruhatTitsWilsonActionComparisonTarget : Set where
  finiteBTGaugeActionComparesToWilsonPlaquetteActionTarget :
    BruhatTitsWilsonActionComparisonTarget

data ReflectionPositiveBTTransferMatrixTarget : Set where
  reflectionPositiveTransferMatrixOnBTGaugeQuotientTarget :
    ReflectionPositiveBTTransferMatrixTarget

data DobrushinShlosmanClusterTarget : Set where
  bTPRegularInfluenceCoefficientsSatisfyClusterHypothesesTarget :
    DobrushinShlosmanClusterTarget

data ObservableClassInclusionTarget : Set where
  dashiGaugeInvariantObservablesIncludedInExternalOSClassTarget :
    ObservableClassInclusionTarget

data NoSpectralPollutionTarget : Set where
  noBottomSpectrumPollutionAcrossDepthAndContinuumLimitTarget :
    NoSpectralPollutionTarget

data BruhatTitsToOSLatticeTransferTarget : Set where
  bruhatTitsToOSLatticeTransferTarget :
    BruhatTitsWilsonActionComparisonTarget →
    ReflectionPositiveBTTransferMatrixTarget →
    DobrushinShlosmanClusterTarget →
    ObservableClassInclusionTarget →
    NoSpectralPollutionTarget →
    BruhatTitsToOSLatticeTransferTarget

canonicalBruhatTitsWilsonActionComparisonTarget :
  BruhatTitsWilsonActionComparisonTarget
canonicalBruhatTitsWilsonActionComparisonTarget =
  finiteBTGaugeActionComparesToWilsonPlaquetteActionTarget

canonicalReflectionPositiveBTTransferMatrixTarget :
  ReflectionPositiveBTTransferMatrixTarget
canonicalReflectionPositiveBTTransferMatrixTarget =
  reflectionPositiveTransferMatrixOnBTGaugeQuotientTarget

canonicalDobrushinShlosmanClusterTarget :
  DobrushinShlosmanClusterTarget
canonicalDobrushinShlosmanClusterTarget =
  bTPRegularInfluenceCoefficientsSatisfyClusterHypothesesTarget

canonicalObservableClassInclusionTarget :
  ObservableClassInclusionTarget
canonicalObservableClassInclusionTarget =
  dashiGaugeInvariantObservablesIncludedInExternalOSClassTarget

canonicalNoSpectralPollutionTarget :
  NoSpectralPollutionTarget
canonicalNoSpectralPollutionTarget =
  noBottomSpectrumPollutionAcrossDepthAndContinuumLimitTarget

canonicalBruhatTitsToOSLatticeTransferTarget :
  BruhatTitsToOSLatticeTransferTarget
canonicalBruhatTitsToOSLatticeTransferTarget =
  bruhatTitsToOSLatticeTransferTarget
    canonicalBruhatTitsWilsonActionComparisonTarget
    canonicalReflectionPositiveBTTransferMatrixTarget
    canonicalDobrushinShlosmanClusterTarget
    canonicalObservableClassInclusionTarget
    canonicalNoSpectralPollutionTarget

------------------------------------------------------------------------
-- Governance booleans.

externalTwentyTwentySixOSMassGapPreprintsRecorded : Bool
externalTwentyTwentySixOSMassGapPreprintsRecorded =
  true

externalCandidateYMMassGapAuthorityRecorded : Bool
externalCandidateYMMassGapAuthorityRecorded =
  true

externalCandidatesAcceptedAsClayAuthority : Bool
externalCandidatesAcceptedAsClayAuthority =
  false

bTWilsonActionComparisonProved : Bool
bTWilsonActionComparisonProved =
  false

bTReflectionPositiveTransferMatrixProved : Bool
bTReflectionPositiveTransferMatrixProved =
  false

gaugeQuotientReflectionPositivityProved : Bool
gaugeQuotientReflectionPositivityProved =
  false

dSClusterHypothesesVerifiedForBT : Bool
dSClusterHypothesesVerifiedForBT =
  false

observableClassInclusionProved : Bool
observableClassInclusionProved =
  false

gaugeInvariantObservableCompletenessProved : Bool
gaugeInvariantObservableCompletenessProved =
  false

noSpectralPollutionDepthLimitProved : Bool
noSpectralPollutionDepthLimitProved =
  false

noSpectralPollutionContinuumLimitProved : Bool
noSpectralPollutionContinuumLimitProved =
  false

bruhatTitsToOSLatticeTransferProved : Bool
bruhatTitsToOSLatticeTransferProved =
  false

oSWightmanReconstructionTransferredToBT : Bool
oSWightmanReconstructionTransferredToBT =
  false

continuumMassGapTransferredToBT : Bool
continuumMassGapTransferredToBT =
  false

clayYangMillsPromoted : Bool
clayYangMillsPromoted =
  false

terminalPromotion : Bool
terminalPromotion =
  false

externalTwentyTwentySixOSMassGapPreprintsRecordedIsTrue :
  externalTwentyTwentySixOSMassGapPreprintsRecorded ≡ true
externalTwentyTwentySixOSMassGapPreprintsRecordedIsTrue =
  refl

externalCandidateYMMassGapAuthorityRecordedIsTrue :
  externalCandidateYMMassGapAuthorityRecorded ≡ true
externalCandidateYMMassGapAuthorityRecordedIsTrue =
  refl

externalCandidatesAcceptedAsClayAuthorityIsFalse :
  externalCandidatesAcceptedAsClayAuthority ≡ false
externalCandidatesAcceptedAsClayAuthorityIsFalse =
  refl

bTWilsonActionComparisonProvedIsFalse :
  bTWilsonActionComparisonProved ≡ false
bTWilsonActionComparisonProvedIsFalse =
  refl

bTReflectionPositiveTransferMatrixProvedIsFalse :
  bTReflectionPositiveTransferMatrixProved ≡ false
bTReflectionPositiveTransferMatrixProvedIsFalse =
  refl

gaugeQuotientReflectionPositivityProvedIsFalse :
  gaugeQuotientReflectionPositivityProved ≡ false
gaugeQuotientReflectionPositivityProvedIsFalse =
  refl

dSClusterHypothesesVerifiedForBTIsFalse :
  dSClusterHypothesesVerifiedForBT ≡ false
dSClusterHypothesesVerifiedForBTIsFalse =
  refl

observableClassInclusionProvedIsFalse :
  observableClassInclusionProved ≡ false
observableClassInclusionProvedIsFalse =
  refl

gaugeInvariantObservableCompletenessProvedIsFalse :
  gaugeInvariantObservableCompletenessProved ≡ false
gaugeInvariantObservableCompletenessProvedIsFalse =
  refl

noSpectralPollutionDepthLimitProvedIsFalse :
  noSpectralPollutionDepthLimitProved ≡ false
noSpectralPollutionDepthLimitProvedIsFalse =
  refl

noSpectralPollutionContinuumLimitProvedIsFalse :
  noSpectralPollutionContinuumLimitProved ≡ false
noSpectralPollutionContinuumLimitProvedIsFalse =
  refl

bruhatTitsToOSLatticeTransferProvedIsFalse :
  bruhatTitsToOSLatticeTransferProved ≡ false
bruhatTitsToOSLatticeTransferProvedIsFalse =
  refl

oSWightmanReconstructionTransferredToBTIsFalse :
  oSWightmanReconstructionTransferredToBT ≡ false
oSWightmanReconstructionTransferredToBTIsFalse =
  refl

continuumMassGapTransferredToBTIsFalse :
  continuumMassGapTransferredToBT ≡ false
continuumMassGapTransferredToBTIsFalse =
  refl

clayYangMillsPromotedIsFalse :
  clayYangMillsPromoted ≡ false
clayYangMillsPromotedIsFalse =
  refl

terminalPromotionIsFalse :
  terminalPromotion ≡ false
terminalPromotionIsFalse =
  refl

------------------------------------------------------------------------
-- Promotion token is uninhabited in this boundary.

data BruhatTitsToOSLatticeTransferPromotionToken : Set where

bruhatTitsToOSLatticeTransferPromotionImpossibleHere :
  BruhatTitsToOSLatticeTransferPromotionToken →
  ⊥
bruhatTitsToOSLatticeTransferPromotionImpossibleHere ()

------------------------------------------------------------------------
-- Fail-closed non-promotion ledger.

data BruhatTitsToOSLatticeTransferNonPromotion : Set where
  notAProofOfBTWilsonActionComparison :
    BruhatTitsToOSLatticeTransferNonPromotion

  notAProofOfReflectionPositivity :
    BruhatTitsToOSLatticeTransferNonPromotion

  notAProofOfDSOrClusterHypotheses :
    BruhatTitsToOSLatticeTransferNonPromotion

  notAProofOfObservableClassInclusion :
    BruhatTitsToOSLatticeTransferNonPromotion

  notAProofOfNoSpectralPollution :
    BruhatTitsToOSLatticeTransferNonPromotion

  notAClayYangMillsPromotion :
    BruhatTitsToOSLatticeTransferNonPromotion

canonicalBruhatTitsToOSLatticeTransferNonPromotions :
  List BruhatTitsToOSLatticeTransferNonPromotion
canonicalBruhatTitsToOSLatticeTransferNonPromotions =
  notAProofOfBTWilsonActionComparison
  ∷ notAProofOfReflectionPositivity
  ∷ notAProofOfDSOrClusterHypotheses
  ∷ notAProofOfObservableClassInclusion
  ∷ notAProofOfNoSpectralPollution
  ∷ notAClayYangMillsPromotion
  ∷ []

canonicalBruhatTitsToOSLatticeTransferFindings :
  List String
canonicalBruhatTitsToOSLatticeTransferFindings =
  "External 2026 OS and mass-gap preprints are authority candidates only."
  ∷ "BT-to-Wilson action comparison remains an explicit transfer hypothesis."
  ∷ "Reflection positivity must be proved on the BT/gauge quotient carrier."
  ∷ "Dobrushin-Shlosman or clustering hypotheses must be verified for BT geometry."
  ∷ "The external observable class must contain DASHI gauge-invariant observables."
  ∷ "No spectral pollution is required across depth and continuum limits."
  ∷ "clayYangMillsPromoted remains false."
  ∷ []

------------------------------------------------------------------------
-- Main receipt.

record YMBruhatTitsToOSLatticeTransferBoundary : Setω where
  field
    status :
      YMBruhatTitsToOSLatticeTransferStatus

    stages :
      List YMBruhatTitsToOSLatticeTransferStage

    stagesAreCanonical :
      stages ≡ canonicalYMBruhatTitsToOSLatticeTransferStages

    rows :
      List BruhatTitsToOSLatticeTransferRow

    rowsAreCanonical :
      rows ≡ canonicalBruhatTitsToOSLatticeTransferRows

    requiredHypotheses :
      List BruhatTitsToOSRequiredHypothesis

    requiredHypothesesAreCanonical :
      requiredHypotheses ≡ canonicalBruhatTitsToOSRequiredHypotheses

    externalCandidates :
      List ExternalYMMassGapAuthorityCandidate

    externalCandidatesAreCanonical :
      externalCandidates ≡ canonicalExternalYMMassGapAuthorityCandidates

    blockers :
      List BruhatTitsToOSLatticeTransferBlocker

    blockersAreCanonical :
      blockers ≡ canonicalBruhatTitsToOSLatticeTransferBlockers

    target :
      BruhatTitsToOSLatticeTransferTarget

    targetIsCanonical :
      target ≡ canonicalBruhatTitsToOSLatticeTransferTarget

    consumedGaugeZeroModeRigidity :
      Rigidity.YMGaugeZeroModeVacuumRigidityFailClosedReceipt

    consumedGaugeZeroModeRigidityCanonical :
      Bool

    consumedGaugeZeroModeRigidityCanonicalIsTrue :
      consumedGaugeZeroModeRigidityCanonical ≡ true

    canonicalGaugeZeroModeRigidityKeepsClayFalse :
      Rigidity.clayPromotionStillFalse
        Rigidity.canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
      ≡
      refl

    consumedHamiltonianDomination :
      Ham.YMHamiltonianDominationFailClosedReceipt

    consumedHamiltonianDominationCanonical :
      Bool

    consumedHamiltonianDominationCanonicalIsTrue :
      consumedHamiltonianDominationCanonical ≡ true

    canonicalHamiltonianDominationKeepsClayFalse :
      Ham.clayPromotionStillFalse
        Ham.canonicalYMHamiltonianDominationFailClosedReceipt
      ≡
      refl

    consumedSelfAdjointQuotientGap :
      Gap.YMSelfAdjointHamiltonianQuotientGapBoundary

    consumedSelfAdjointQuotientGapCanonical :
      Bool

    consumedSelfAdjointQuotientGapCanonicalIsTrue :
      consumedSelfAdjointQuotientGapCanonical ≡ true

    canonicalSelfAdjointQuotientKeepsClayFalse :
      Gap.clayYangMillsPromotedField
        Gap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
      ≡
      false

    consumedLatticeMassGapAuthorityBoundary :
      Authority.LatticeMassGapAuthorityBoundary

    canonicalLatticeAuthorityKeepsClayFalse :
      Authority.LatticeMassGapAuthorityBoundary.noClayPromotion
        Authority.latticeMassGapAuthorityBoundary
      ≡
      refl

    externalCandidatesRecorded :
      externalCandidateYMMassGapAuthorityRecorded ≡ true

    externalCandidatesNotAccepted :
      externalCandidatesAcceptedAsClayAuthority ≡ false

    bTWilsonActionComparisonStillMissing :
      bTWilsonActionComparisonProved ≡ false

    reflectionPositiveBTTransferStillMissing :
      bTReflectionPositiveTransferMatrixProved ≡ false

    gaugeQuotientReflectionPositivityStillMissing :
      gaugeQuotientReflectionPositivityProved ≡ false

    dSClusterHypothesesStillMissing :
      dSClusterHypothesesVerifiedForBT ≡ false

    observableClassInclusionStillMissing :
      observableClassInclusionProved ≡ false

    gaugeInvariantObservableCompletenessStillMissing :
      gaugeInvariantObservableCompletenessProved ≡ false

    noSpectralPollutionDepthStillMissing :
      noSpectralPollutionDepthLimitProved ≡ false

    noSpectralPollutionContinuumStillMissing :
      noSpectralPollutionContinuumLimitProved ≡ false

    transferTheoremStillMissing :
      bruhatTitsToOSLatticeTransferProved ≡ false

    osWightmanTransferStillMissing :
      oSWightmanReconstructionTransferredToBT ≡ false

    continuumMassGapTransferStillMissing :
      continuumMassGapTransferredToBT ≡ false

    clayPromotionStillFalse :
      clayYangMillsPromoted ≡ false

    terminalPromotionStillFalse :
      terminalPromotion ≡ false

    firstBlocker :
      BruhatTitsToOSLatticeTransferBlocker

    firstBlockerIsBTWilsonComparison :
      firstBlocker ≡ missingBTWilsonActionComparison

    authorityBlocker :
      BruhatTitsToOSLatticeTransferBlocker

    authorityBlockerIsExternalCandidateNotAccepted :
      authorityBlocker ≡ externalCandidatesNotAcceptedAuthority

    noPromotionTokenEliminator :
      BruhatTitsToOSLatticeTransferPromotionToken →
      ⊥

    nonPromotions :
      List BruhatTitsToOSLatticeTransferNonPromotion

    nonPromotionsAreCanonical :
      nonPromotions ≡ canonicalBruhatTitsToOSLatticeTransferNonPromotions

    findings :
      List String

    findingsAreCanonical :
      findings ≡ canonicalBruhatTitsToOSLatticeTransferFindings

open YMBruhatTitsToOSLatticeTransferBoundary public

canonicalYMBruhatTitsToOSLatticeTransferBoundary :
  YMBruhatTitsToOSLatticeTransferBoundary
canonicalYMBruhatTitsToOSLatticeTransferBoundary =
  record
    { status =
        bruhatTitsTransferBoundaryFailClosedClayPromotionBlocked
    ; stages =
        canonicalYMBruhatTitsToOSLatticeTransferStages
    ; stagesAreCanonical =
        refl
    ; rows =
        canonicalBruhatTitsToOSLatticeTransferRows
    ; rowsAreCanonical =
        refl
    ; requiredHypotheses =
        canonicalBruhatTitsToOSRequiredHypotheses
    ; requiredHypothesesAreCanonical =
        refl
    ; externalCandidates =
        canonicalExternalYMMassGapAuthorityCandidates
    ; externalCandidatesAreCanonical =
        refl
    ; blockers =
        canonicalBruhatTitsToOSLatticeTransferBlockers
    ; blockersAreCanonical =
        refl
    ; target =
        canonicalBruhatTitsToOSLatticeTransferTarget
    ; targetIsCanonical =
        refl
    ; consumedGaugeZeroModeRigidity =
        Rigidity.canonicalYMGaugeZeroModeVacuumRigidityFailClosedReceipt
    ; consumedGaugeZeroModeRigidityCanonical =
        true
    ; consumedGaugeZeroModeRigidityCanonicalIsTrue =
        refl
    ; canonicalGaugeZeroModeRigidityKeepsClayFalse =
        refl
    ; consumedHamiltonianDomination =
        Ham.canonicalYMHamiltonianDominationFailClosedReceipt
    ; consumedHamiltonianDominationCanonical =
        true
    ; consumedHamiltonianDominationCanonicalIsTrue =
        refl
    ; canonicalHamiltonianDominationKeepsClayFalse =
        refl
    ; consumedSelfAdjointQuotientGap =
        Gap.canonicalYMSelfAdjointHamiltonianQuotientGapBoundary
    ; consumedSelfAdjointQuotientGapCanonical =
        true
    ; consumedSelfAdjointQuotientGapCanonicalIsTrue =
        refl
    ; canonicalSelfAdjointQuotientKeepsClayFalse =
        refl
    ; consumedLatticeMassGapAuthorityBoundary =
        Authority.latticeMassGapAuthorityBoundary
    ; canonicalLatticeAuthorityKeepsClayFalse =
        refl
    ; externalCandidatesRecorded =
        refl
    ; externalCandidatesNotAccepted =
        refl
    ; bTWilsonActionComparisonStillMissing =
        refl
    ; reflectionPositiveBTTransferStillMissing =
        refl
    ; gaugeQuotientReflectionPositivityStillMissing =
        refl
    ; dSClusterHypothesesStillMissing =
        refl
    ; observableClassInclusionStillMissing =
        refl
    ; gaugeInvariantObservableCompletenessStillMissing =
        refl
    ; noSpectralPollutionDepthStillMissing =
        refl
    ; noSpectralPollutionContinuumStillMissing =
        refl
    ; transferTheoremStillMissing =
        refl
    ; osWightmanTransferStillMissing =
        refl
    ; continuumMassGapTransferStillMissing =
        refl
    ; clayPromotionStillFalse =
        refl
    ; terminalPromotionStillFalse =
        refl
    ; firstBlocker =
        missingBTWilsonActionComparison
    ; firstBlockerIsBTWilsonComparison =
        refl
    ; authorityBlocker =
        externalCandidatesNotAcceptedAuthority
    ; authorityBlockerIsExternalCandidateNotAccepted =
        refl
    ; noPromotionTokenEliminator =
        bruhatTitsToOSLatticeTransferPromotionImpossibleHere
    ; nonPromotions =
        canonicalBruhatTitsToOSLatticeTransferNonPromotions
    ; nonPromotionsAreCanonical =
        refl
    ; findings =
        canonicalBruhatTitsToOSLatticeTransferFindings
    ; findingsAreCanonical =
        refl
    }

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsCandidatesOnly :
  externalCandidatesNotAccepted
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsCandidatesOnly =
  refl

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsTransferFalse :
  transferTheoremStillMissing
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsTransferFalse =
  refl

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsOSFalse :
  osWightmanTransferStillMissing
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsOSFalse =
  refl

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsNoPollutionFalse :
  noSpectralPollutionContinuumStillMissing
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsNoPollutionFalse =
  refl

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsClayFalse :
  clayPromotionStillFalse
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsClayFalse =
  refl

canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsTerminalFalse :
  terminalPromotionStillFalse
    canonicalYMBruhatTitsToOSLatticeTransferBoundary
  ≡
  refl
canonicalYMBruhatTitsToOSLatticeTransferBoundaryKeepsTerminalFalse =
  refl

canonicalYMBruhatTitsToOSLatticeTransferStageCount :
  listCount canonicalYMBruhatTitsToOSLatticeTransferStages ≡ 11
canonicalYMBruhatTitsToOSLatticeTransferStageCount =
  refl

canonicalBruhatTitsToOSRequiredHypothesisCount :
  listCount canonicalBruhatTitsToOSRequiredHypotheses ≡ 13
canonicalBruhatTitsToOSRequiredHypothesisCount =
  refl

canonicalBruhatTitsToOSLatticeTransferBlockerCount :
  listCount canonicalBruhatTitsToOSLatticeTransferBlockers ≡ 10
canonicalBruhatTitsToOSLatticeTransferBlockerCount =
  refl
