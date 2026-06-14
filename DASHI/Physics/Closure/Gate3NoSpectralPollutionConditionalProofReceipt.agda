module DASHI.Physics.Closure.Gate3NoSpectralPollutionConditionalProofReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3FiniteCutoffFrameLowerBoundProofReceipt
  as Finite
import DASHI.Physics.Closure.Gate3UniformLowerBoundObstructionReceipt
  as Uniform
import DASHI.Physics.Closure.Gate3MoscoConstructiveSequenceReceipt
  as ConstructiveMosco
import DASHI.Physics.Closure.Gate3MoscoRecoveryPreciseReceipt
  as MoscoRecovery
import DASHI.Physics.Closure.NoSpectralPollutionReceipt
  as NSP
import DASHI.Physics.Closure.SpectralConvergenceGate3Receipt
  as Spectral

------------------------------------------------------------------------
-- Gate 3 conditional no-spectral-pollution proof receipt.
--
-- This receipt consumes both the constructive Gate 3 Mosco sequence receipt
-- and the precise Gate 3 Mosco recovery surface.
--
-- This receipt records the conditional Attouch/Mosco chain only:
--
--   Attouch/Mosco hypotheses for closed semibounded forms
--     -> strong resolvent convergence
--     -> no-spectral-pollution only with the extra compactness/tightness,
--        isolated-sector, and spectral-projection hypotheses.
--
-- It also records the PAWOTG transfer blocker and explicitly blocks Gate 3,
-- continuum mass-gap, and Clay promotion.

data Gate3ConditionalNoPollutionStatus : Set where
  conditionalAttouchMoscoChainRecorded_pawotgBlocked_noGate3NoClay :
    Gate3ConditionalNoPollutionStatus

data AttouchMoscoHypothesis : Set where
  closedSemiboundedFormsHypothesis :
    AttouchMoscoHypothesis

  commonLowerBoundHypothesis :
    AttouchMoscoHypothesis

  moscoLiminfHypothesis :
    AttouchMoscoHypothesis

  moscoRecoverySequenceHypothesis :
    AttouchMoscoHypothesis

  domainCompatibilityHypothesis :
    AttouchMoscoHypothesis

canonicalAttouchMoscoHypotheses :
  List AttouchMoscoHypothesis
canonicalAttouchMoscoHypotheses =
  closedSemiboundedFormsHypothesis
  ∷ commonLowerBoundHypothesis
  ∷ moscoLiminfHypothesis
  ∷ moscoRecoverySequenceHypothesis
  ∷ domainCompatibilityHypothesis
  ∷ []

data NoSpectralPollutionExtraHypothesis : Set where
  compactnessOrTightnessAgainstEscapingModesHypothesis :
    NoSpectralPollutionExtraHypothesis

  isolatedTrackedSectorHypothesis :
    NoSpectralPollutionExtraHypothesis

  spectralProjectionContinuityOnIsolatedContourHypothesis :
    NoSpectralPollutionExtraHypothesis

canonicalNoSpectralPollutionExtraHypotheses :
  List NoSpectralPollutionExtraHypothesis
canonicalNoSpectralPollutionExtraHypotheses =
  compactnessOrTightnessAgainstEscapingModesHypothesis
  ∷ isolatedTrackedSectorHypothesis
  ∷ spectralProjectionContinuityOnIsolatedContourHypothesis
  ∷ []

data Gate3ConditionalChainStep : Set where
  attouchMoscoHypothesesStated :
    Gate3ConditionalChainStep

  moscoGivesStrongResolventStep :
    Gate3ConditionalChainStep

  strongResolventAloneInsufficientStep :
    Gate3ConditionalChainStep

  noSpectralPollutionRequiresExtraHypothesesStep :
    Gate3ConditionalChainStep

  noSpectralPollutionOnlyConditionalStep :
    Gate3ConditionalChainStep

canonicalGate3ConditionalChain :
  List Gate3ConditionalChainStep
canonicalGate3ConditionalChain =
  attouchMoscoHypothesesStated
  ∷ moscoGivesStrongResolventStep
  ∷ strongResolventAloneInsufficientStep
  ∷ noSpectralPollutionRequiresExtraHypothesesStep
  ∷ noSpectralPollutionOnlyConditionalStep
  ∷ []

data Gate3PAWOTGBlockingCondition : Set where
  kozyrevToArchimedeanPAWOTGTransferOpen :
    Gate3PAWOTGBlockingCondition

  densityForMoscoConditionINotDischarged :
    Gate3PAWOTGBlockingCondition

  uniformInfiniteLowerBoundObstructed :
    Gate3PAWOTGBlockingCondition

  noCrossBoundarySpectralTransferProof :
    Gate3PAWOTGBlockingCondition

canonicalGate3PAWOTGBlockingConditions :
  List Gate3PAWOTGBlockingCondition
canonicalGate3PAWOTGBlockingConditions =
  kozyrevToArchimedeanPAWOTGTransferOpen
  ∷ densityForMoscoConditionINotDischarged
  ∷ uniformInfiniteLowerBoundObstructed
  ∷ noCrossBoundarySpectralTransferProof
  ∷ []

data Gate3ConditionalNoPollutionNonClaim : Set where
  noUnconditionalNoSpectralPollutionTheorem :
    Gate3ConditionalNoPollutionNonClaim

  noNormResolventUpgrade :
    Gate3ConditionalNoPollutionNonClaim

  noUniformInfiniteFrameLowerBound :
    Gate3ConditionalNoPollutionNonClaim

  noGate3Promotion :
    Gate3ConditionalNoPollutionNonClaim

  noContinuumMassGapPromotion :
    Gate3ConditionalNoPollutionNonClaim

  noClayPromotion :
    Gate3ConditionalNoPollutionNonClaim

canonicalGate3ConditionalNoPollutionNonClaims :
  List Gate3ConditionalNoPollutionNonClaim
canonicalGate3ConditionalNoPollutionNonClaims =
  noUnconditionalNoSpectralPollutionTheorem
  ∷ noNormResolventUpgrade
  ∷ noUniformInfiniteFrameLowerBound
  ∷ noGate3Promotion
  ∷ noContinuumMassGapPromotion
  ∷ noClayPromotion
  ∷ []

data Gate3ConditionalNoPollutionPromotion : Set where

gate3ConditionalNoPollutionPromotionImpossibleHere :
  Gate3ConditionalNoPollutionPromotion →
  ⊥
gate3ConditionalNoPollutionPromotionImpossibleHere ()

conditionalChainStatement :
  String
conditionalChainStatement =
  "Conditional Gate3 chain: Attouch/Mosco hypotheses for closed semibounded forms give strong resolvent convergence; no-spectral-pollution is available only as an extra compactness/tightness, isolated-sector, and spectral-projection hypothesis."

pawotgBlockingStatement :
  String
pawotgBlockingStatement =
  "PAWOTG blocks promotion here: Kozyrev-to-Archimedean transfer, density for Mosco condition I, a uniform infinite lower frame bound, and cross-boundary spectral transfer are not proved."

noPromotionStatement :
  String
noPromotionStatement =
  "This receipt proves no unconditional no-spectral-pollution theorem, no norm-resolvent upgrade, no Gate3 closure, no continuum mass gap, and no Clay result."

record Gate3NoSpectralPollutionConditionalProofReceipt : Setω where
  field
    status :
      Gate3ConditionalNoPollutionStatus

    statusIsCanonical :
      status
      ≡
      conditionalAttouchMoscoChainRecorded_pawotgBlocked_noGate3NoClay

    finiteCutoffReceipt :
      Finite.Gate3FiniteCutoffFrameLowerBoundProofReceipt

    finiteCutoffLowerBoundRecorded :
      Finite.finiteLowerBoundANPositiveRecorded finiteCutoffReceipt
      ≡
      true

    finiteCutoffNoContinuumGate3 :
      Finite.continuumGate3Promoted finiteCutoffReceipt
      ≡
      false

    uniformObstructionReceipt :
      Uniform.Gate3UniformLowerBoundObstructionReceipt

    uniformInfiniteLowerBoundBlocked :
      Uniform.uniformAOnInfiniteH uniformObstructionReceipt
      ≡
      false

    uniformObstructionNoGate3Promotion :
      Uniform.continuumGate3Promoted uniformObstructionReceipt
      ≡
      false

    moscoRecoveryReceipt :
      MoscoRecovery.Gate3MoscoRecoveryPreciseReceipt

    moscoConditionIRequiresDensity :
      MoscoRecovery.moscoConditionIRequiresDensity moscoRecoveryReceipt
      ≡
      true

    moscoConditionIIRecorded :
      MoscoRecovery.moscoConditionIITrivial moscoRecoveryReceipt
      ≡
      true

    pawotgTransferOpen :
      MoscoRecovery.pawotgTransferOpen moscoRecoveryReceipt
      ≡
      true

    kozyrevToPAWOTGTransferNotProved :
      MoscoRecovery.kozyrevToPAWOTGTransferProved moscoRecoveryReceipt
      ≡
      false

    moscoRecoveryNoGate3Closure :
      MoscoRecovery.gate3Closure moscoRecoveryReceipt
      ≡
      false

    moscoRecoveryNoClayClosure :
      MoscoRecovery.clayClosure moscoRecoveryReceipt
      ≡
      false

    constructiveMoscoReceipt :
      ConstructiveMosco.Gate3MoscoConstructiveSequenceReceipt

    constructiveMoscoRecoveryRecorded :
      ConstructiveMosco.constructiveRecoveryCandidateRecorded
        constructiveMoscoReceipt
      ≡
      true

    constructiveMoscoConditionIStillOpen :
      ConstructiveMosco.moscoConditionIConstructed constructiveMoscoReceipt
      ≡
      false

    constructiveMoscoNoGate3Promotion :
      ConstructiveMosco.gate3Promotion constructiveMoscoReceipt
      ≡
      false

    noSpectralPollutionReceipt :
      NSP.NoSpectralPollutionReceipt

    noSpectralPollutionMoscoInputIsMosco :
      NSP.moscoInput noSpectralPollutionReceipt
      ≡
      NSP.moscoFormConvergence

    noSpectralPollutionResolventOutputIsStrong :
      NSP.resolventOutput noSpectralPollutionReceipt
      ≡
      NSP.strongResolventConvergence

    moscoGivesStrongResolventRecorded :
      NSP.moscoGivesStrongResolvent noSpectralPollutionReceipt
      ≡
      true

    moscoDoesNotGiveNormResolvent :
      NSP.moscoGivesNormResolvent noSpectralPollutionReceipt
      ≡
      true

    strongResolventAloneInsufficient :
      NSP.strongResolventAloneExcludesSpectralPollution
        noSpectralPollutionReceipt
      ≡
      false

    noSpectralPollutionKeptAsHypothesis :
      NSP.noSpectralPollutionRecordedAsHypothesis
        noSpectralPollutionReceipt
      ≡
      true

    isolatedSectorHypothesesRequired :
      NSP.isolatedSectorHypothesesRequired noSpectralPollutionReceipt
      ≡
      true

    spectralReceipt :
      Spectral.SpectralConvergenceGate3Receipt

    spectralGate3RequiresNoPollution :
      Spectral.gate3NoSpectralPollutionRequired spectralReceipt
      ≡
      true

    spectralGate3NoPollutionProvedHere :
      Spectral.gate3NoSpectralPollutionProvedHere spectralReceipt
      ≡
      true

    spectralGate3NoClayPromotion :
      Spectral.clayYangMillsPromoted spectralReceipt
      ≡
      false

    attouchMoscoHypotheses :
      List AttouchMoscoHypothesis

    attouchMoscoHypothesesAreCanonical :
      attouchMoscoHypotheses ≡ canonicalAttouchMoscoHypotheses

    noSpectralPollutionExtraHypotheses :
      List NoSpectralPollutionExtraHypothesis

    noSpectralPollutionExtraHypothesesAreCanonical :
      noSpectralPollutionExtraHypotheses
      ≡
      canonicalNoSpectralPollutionExtraHypotheses

    conditionalChain :
      List Gate3ConditionalChainStep

    conditionalChainIsCanonical :
      conditionalChain ≡ canonicalGate3ConditionalChain

    pawotgBlockingConditions :
      List Gate3PAWOTGBlockingCondition

    pawotgBlockingConditionsAreCanonical :
      pawotgBlockingConditions
      ≡
      canonicalGate3PAWOTGBlockingConditions

    nonClaims :
      List Gate3ConditionalNoPollutionNonClaim

    nonClaimsAreCanonical :
      nonClaims ≡ canonicalGate3ConditionalNoPollutionNonClaims

    conditionalOnly :
      Bool

    conditionalOnlyIsTrue :
      conditionalOnly ≡ true

    unconditionalNoSpectralPollutionProved :
      Bool

    unconditionalNoSpectralPollutionProvedIsFalse :
      unconditionalNoSpectralPollutionProved ≡ false

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    chainBoundary :
      String

    chainBoundaryIsCanonical :
      chainBoundary ≡ conditionalChainStatement

    pawotgBoundary :
      String

    pawotgBoundaryIsCanonical :
      pawotgBoundary ≡ pawotgBlockingStatement

    noPromotionBoundary :
      String

    noPromotionBoundaryIsCanonical :
      noPromotionBoundary ≡ noPromotionStatement

    promotionFlags :
      List Gate3ConditionalNoPollutionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    noPromotionPossibleHere :
      Gate3ConditionalNoPollutionPromotion →
      ⊥

open Gate3NoSpectralPollutionConditionalProofReceipt public

canonicalGate3NoSpectralPollutionConditionalProofReceipt :
  Gate3NoSpectralPollutionConditionalProofReceipt
canonicalGate3NoSpectralPollutionConditionalProofReceipt =
  record
    { status =
        conditionalAttouchMoscoChainRecorded_pawotgBlocked_noGate3NoClay
    ; statusIsCanonical =
        refl
    ; finiteCutoffReceipt =
        Finite.canonicalGate3FiniteCutoffFrameLowerBoundProofReceipt
    ; finiteCutoffLowerBoundRecorded =
        refl
    ; finiteCutoffNoContinuumGate3 =
        refl
    ; uniformObstructionReceipt =
        Uniform.canonicalGate3UniformLowerBoundObstructionReceipt
    ; uniformInfiniteLowerBoundBlocked =
        refl
    ; uniformObstructionNoGate3Promotion =
        refl
    ; moscoRecoveryReceipt =
        MoscoRecovery.canonicalGate3MoscoRecoveryPreciseReceipt
    ; moscoConditionIRequiresDensity =
        refl
    ; moscoConditionIIRecorded =
        refl
    ; pawotgTransferOpen =
        refl
    ; kozyrevToPAWOTGTransferNotProved =
        refl
    ; moscoRecoveryNoGate3Closure =
        refl
    ; moscoRecoveryNoClayClosure =
        refl
    ; constructiveMoscoReceipt =
        ConstructiveMosco.canonicalGate3MoscoConstructiveSequenceReceipt
    ; constructiveMoscoRecoveryRecorded =
        refl
    ; constructiveMoscoConditionIStillOpen =
        refl
    ; constructiveMoscoNoGate3Promotion =
        refl
    ; noSpectralPollutionReceipt =
        NSP.canonicalNoSpectralPollutionReceipt
    ; noSpectralPollutionMoscoInputIsMosco =
        refl
    ; noSpectralPollutionResolventOutputIsStrong =
        refl
    ; moscoGivesStrongResolventRecorded =
        refl
    ; moscoDoesNotGiveNormResolvent =
        refl
    ; strongResolventAloneInsufficient =
        refl
    ; noSpectralPollutionKeptAsHypothesis =
        refl
    ; isolatedSectorHypothesesRequired =
        refl
    ; spectralReceipt =
        Spectral.canonicalSpectralConvergenceGate3Receipt
    ; spectralGate3RequiresNoPollution =
        refl
    ; spectralGate3NoPollutionProvedHere =
        refl
    ; spectralGate3NoClayPromotion =
        refl
    ; attouchMoscoHypotheses =
        canonicalAttouchMoscoHypotheses
    ; attouchMoscoHypothesesAreCanonical =
        refl
    ; noSpectralPollutionExtraHypotheses =
        canonicalNoSpectralPollutionExtraHypotheses
    ; noSpectralPollutionExtraHypothesesAreCanonical =
        refl
    ; conditionalChain =
        canonicalGate3ConditionalChain
    ; conditionalChainIsCanonical =
        refl
    ; pawotgBlockingConditions =
        canonicalGate3PAWOTGBlockingConditions
    ; pawotgBlockingConditionsAreCanonical =
        refl
    ; nonClaims =
        canonicalGate3ConditionalNoPollutionNonClaims
    ; nonClaimsAreCanonical =
        refl
    ; conditionalOnly =
        true
    ; conditionalOnlyIsTrue =
        refl
    ; unconditionalNoSpectralPollutionProved =
        false
    ; unconditionalNoSpectralPollutionProvedIsFalse =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; chainBoundary =
        conditionalChainStatement
    ; chainBoundaryIsCanonical =
        refl
    ; pawotgBoundary =
        pawotgBlockingStatement
    ; pawotgBoundaryIsCanonical =
        refl
    ; noPromotionBoundary =
        noPromotionStatement
    ; noPromotionBoundaryIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3ConditionalNoPollutionPromotionImpossibleHere
    }

gate3ConditionalNoPollutionIsConditional :
  conditionalOnly canonicalGate3NoSpectralPollutionConditionalProofReceipt
  ≡
  true
gate3ConditionalNoPollutionIsConditional =
  refl

gate3ConditionalNoPollutionPAWOTGBlocked :
  MoscoRecovery.pawotgTransferOpen
    (moscoRecoveryReceipt
      canonicalGate3NoSpectralPollutionConditionalProofReceipt)
  ≡
  true
gate3ConditionalNoPollutionPAWOTGBlocked =
  refl

gate3ConditionalNoPollutionNoGate3Promotion :
  gate3Promoted canonicalGate3NoSpectralPollutionConditionalProofReceipt
  ≡
  false
gate3ConditionalNoPollutionNoGate3Promotion =
  refl

gate3ConditionalNoPollutionNoClayPromotion :
  clayPromoted canonicalGate3NoSpectralPollutionConditionalProofReceipt
  ≡
  false
gate3ConditionalNoPollutionNoClayPromotion =
  refl
