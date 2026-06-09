module DASHI.Physics.Closure.Gate3PAWOTGUniformSeparationTargetReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.Gate3AdelicLocalizationReductionReceipt
  as Localization
import DASHI.Physics.Closure.Gate3AdelicSobolevNormBindingReceipt
  as NormBinding
import DASHI.Physics.Closure.Gate3MoscoRecoveryPreciseReceipt as Mosco
import DASHI.Physics.Closure.Gate3NoSpectralPollutionReceipt as NoPollution
import DASHI.Physics.Closure.Gate3PAWOTGConcreteConditionReceipt as PAWOTG
import DASHI.Physics.Closure.Gate3ScaleGraphBarrierInstantiationReceipt
  as Barrier

------------------------------------------------------------------------
-- Gate 3 PAWOTG uniform-separation target receipt.
--
-- This receipt pins the next exact Gate 3 theorem target.  It consumes the
-- current PAWOTG concrete condition, adelic localization reduction, adelic
-- Sobolev norm binding, Mosco recovery, no-spectral-pollution, and scale
-- graph barrier receipts.
--
-- The target theorem is:
--
--   ExplicitAdelicEmbedding phi
--     + GaussianSpreadBelow sigmaCrit phi
--     + sigmaCrit < 0.5052 at p=3
--     -> inf_N A_N > 0
--     -> Mosco/no-pollution/mass-shell route becomes available.
--
-- This file records that theorem target and the exact open obligations.  It
-- does not construct phi, does not prove p>=3 Archimedean localization, does
-- not prove uniform-in-depth spread, and does not promote Gate 3 or Clay.

data Gate3PAWOTGUniformSeparationTargetStatus : Set where
  pawotgUniformSeparationTargetRecorded_exactNextTheorem_noPromotion :
    Gate3PAWOTGUniformSeparationTargetStatus

data PAWOTGUniformSeparationHypothesis : Set where
  explicitAdelicEmbeddingPhi :
    PAWOTGUniformSeparationHypothesis

  gaussianSpreadBelowSigmaCritPhi :
    PAWOTGUniformSeparationHypothesis

  sigmaCritBelowP3Threshold :
    PAWOTGUniformSeparationHypothesis

canonicalPAWOTGUniformSeparationHypotheses :
  List PAWOTGUniformSeparationHypothesis
canonicalPAWOTGUniformSeparationHypotheses =
  explicitAdelicEmbeddingPhi
  ∷ gaussianSpreadBelowSigmaCritPhi
  ∷ sigmaCritBelowP3Threshold
  ∷ []

data PAWOTGUniformSeparationConclusion : Set where
  uniformFrameLowerControlInfANPositive :
    PAWOTGUniformSeparationConclusion

  moscoRecoveryRouteAvailable :
    PAWOTGUniformSeparationConclusion

  noSpectralPollutionRouteAvailable :
    PAWOTGUniformSeparationConclusion

  massShellRouteAvailable :
    PAWOTGUniformSeparationConclusion

canonicalPAWOTGUniformSeparationConclusions :
  List PAWOTGUniformSeparationConclusion
canonicalPAWOTGUniformSeparationConclusions =
  uniformFrameLowerControlInfANPositive
  ∷ moscoRecoveryRouteAvailable
  ∷ noSpectralPollutionRouteAvailable
  ∷ massShellRouteAvailable
  ∷ []

data PAWOTGUniformSeparationOpenObligation : Set where
  constructExplicitAdelicEmbeddingPhi :
    PAWOTGUniformSeparationOpenObligation

  provePGeThreeArchimedeanLocalization :
    PAWOTGUniformSeparationOpenObligation

  proveUniformInDepthGaussianSpread :
    PAWOTGUniformSeparationOpenObligation

  transferUniformSeparationToMosco :
    PAWOTGUniformSeparationOpenObligation

  transferMoscoToNoSpectralPollution :
    PAWOTGUniformSeparationOpenObligation

canonicalPAWOTGUniformSeparationOpenObligations :
  List PAWOTGUniformSeparationOpenObligation
canonicalPAWOTGUniformSeparationOpenObligations =
  constructExplicitAdelicEmbeddingPhi
  ∷ provePGeThreeArchimedeanLocalization
  ∷ proveUniformInDepthGaussianSpread
  ∷ transferUniformSeparationToMosco
  ∷ transferMoscoToNoSpectralPollution
  ∷ []

data PAWOTGUniformSeparationBoundary : Set where
  finiteGershgorinEvidenceDoesNotProveUniformSeparation :
    PAWOTGUniformSeparationBoundary

  kozyrevP2ModelCaseDoesNotCoverSSPPGeThree :
    PAWOTGUniformSeparationBoundary

  adelicLocalizationReductionNotInhabitant :
    PAWOTGUniformSeparationBoundary

  moscoRecoveryStillNeedsTransfer :
    PAWOTGUniformSeparationBoundary

  boundaryNoSpectralPollutionStillConditional :
    PAWOTGUniformSeparationBoundary

  gate3AndClayPromotionBlocked :
    PAWOTGUniformSeparationBoundary

canonicalPAWOTGUniformSeparationBoundaries :
  List PAWOTGUniformSeparationBoundary
canonicalPAWOTGUniformSeparationBoundaries =
  finiteGershgorinEvidenceDoesNotProveUniformSeparation
  ∷ kozyrevP2ModelCaseDoesNotCoverSSPPGeThree
  ∷ adelicLocalizationReductionNotInhabitant
  ∷ moscoRecoveryStillNeedsTransfer
  ∷ boundaryNoSpectralPollutionStillConditional
  ∷ gate3AndClayPromotionBlocked
  ∷ []

data Gate3PAWOTGUniformSeparationPromotion : Set where

gate3PAWOTGUniformSeparationPromotionImpossibleHere :
  Gate3PAWOTGUniformSeparationPromotion →
  ⊥
gate3PAWOTGUniformSeparationPromotionImpossibleHere ()

p3BindingPrime :
  Nat
p3BindingPrime =
  3

sigmaCritP3TenThousandths :
  Nat
sigmaCritP3TenThousandths =
  5052

uniformSeparationTargetStatement :
  String
uniformSeparationTargetStatement =
  "PAWOTGUniformSeparation target: ExplicitAdelicEmbedding phi plus GaussianSpreadBelow sigmaCrit phi plus sigmaCrit < 0.5052 at p=3 implies inf_N A_N > 0, making the Mosco/no-pollution/mass-shell route available."

openObligationStatement :
  String
openObligationStatement =
  "Open obligations: construct phi, prove p>=3 Archimedean localization, prove uniform-in-depth Gaussian spread, transfer uniform separation to Mosco, and transfer Mosco to no spectral pollution."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "This receipt records the next theorem target only; Gate 3 closure, mass-shell transfer, and Clay promotion remain false."

record Gate3PAWOTGUniformSeparationTargetReceipt : Setω where
  field
    status :
      Gate3PAWOTGUniformSeparationTargetStatus

    statusIsCanonical :
      status
      ≡
      pawotgUniformSeparationTargetRecorded_exactNextTheorem_noPromotion

    localizationReductionReceipt :
      Localization.Gate3AdelicLocalizationReductionReceipt

    localizationUniformSeparationStillOpen :
      Localization.uniformSeparationProvedHere localizationReductionReceipt
      ≡
      false

    localizationGate3StillFalse :
      Localization.gate3Promoted localizationReductionReceipt ≡ false

    pawotgConcreteConditionReceipt :
      PAWOTG.Gate3PAWOTGConcreteConditionReceipt

    pawotgBindingPrimeIsP3 :
      PAWOTG.bindingConstraintFromP3 pawotgConcreteConditionReceipt ≡ true

    pawotgUniformityStillOpen :
      PAWOTG.pawotgUniformityOpen pawotgConcreteConditionReceipt ≡ true

    pawotgClayStillFalse :
      PAWOTG.clayGate3Promoted pawotgConcreteConditionReceipt ≡ false

    normBindingReceipt :
      NormBinding.Gate3AdelicSobolevNormBindingReceipt

    normBindingUniformContinuumStillOpen :
      NormBinding.uniformContinuumBoundOpen normBindingReceipt ≡ true

    moscoReceipt :
      Mosco.Gate3MoscoRecoveryPreciseReceipt

    moscoConditionIRequiresDensity :
      Mosco.moscoConditionIRequiresDensity moscoReceipt ≡ true

    moscoPAWOTGTransferStillOpen :
      Mosco.pawotgTransferOpen moscoReceipt ≡ true

    moscoGate3StillFalse :
      Mosco.gate3Closure moscoReceipt ≡ false

    noSpectralPollutionReceipt :
      NoPollution.Gate3NoSpectralPollutionReceipt

    noSpectralPollutionStillConditional :
      NoPollution.noSpectralPollutionConditional
        noSpectralPollutionReceipt
      ≡
      true

    noSpectralPollutionNotUnconditional :
      NoPollution.provedUnconditionally noSpectralPollutionReceipt ≡ false

    noSpectralPollutionGate3StillFalse :
      NoPollution.gate3Promoted noSpectralPollutionReceipt ≡ false

    scaleGraphBarrierReceipt :
      Barrier.Gate3ScaleGraphBarrierInstantiationReceipt

    scaleGraphBarrierPAWOTGBlocks :
      Barrier.pawotgBlocks scaleGraphBarrierReceipt ≡ true

    scaleGraphBarrierGate3StillFalse :
      Barrier.gate3Closed scaleGraphBarrierReceipt ≡ false

    hypotheses :
      List PAWOTGUniformSeparationHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalPAWOTGUniformSeparationHypotheses

    conclusions :
      List PAWOTGUniformSeparationConclusion

    conclusionsAreCanonical :
      conclusions ≡ canonicalPAWOTGUniformSeparationConclusions

    openObligations :
      List PAWOTGUniformSeparationOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalPAWOTGUniformSeparationOpenObligations

    boundaries :
      List PAWOTGUniformSeparationBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalPAWOTGUniformSeparationBoundaries

    bindingPrime :
      Nat

    bindingPrimeIsP3 :
      bindingPrime ≡ p3BindingPrime

    sigmaCritP3 :
      Nat

    sigmaCritP3Is5052TenThousandths :
      sigmaCritP3 ≡ sigmaCritP3TenThousandths

    explicitAdelicEmbeddingConstructedHere :
      Bool

    explicitAdelicEmbeddingConstructedHereIsFalse :
      explicitAdelicEmbeddingConstructedHere ≡ false

    pGeThreeArchimedeanLocalizationProvedHere :
      Bool

    pGeThreeArchimedeanLocalizationProvedHereIsFalse :
      pGeThreeArchimedeanLocalizationProvedHere ≡ false

    uniformInDepthSpreadProvedHere :
      Bool

    uniformInDepthSpreadProvedHereIsFalse :
      uniformInDepthSpreadProvedHere ≡ false

    infANPositiveProvedHere :
      Bool

    infANPositiveProvedHereIsFalse :
      infANPositiveProvedHere ≡ false

    moscoTransferProvedHere :
      Bool

    moscoTransferProvedHereIsFalse :
      moscoTransferProvedHere ≡ false

    noSpectralPollutionTransferProvedHere :
      Bool

    noSpectralPollutionTransferProvedHereIsFalse :
      noSpectralPollutionTransferProvedHere ≡ false

    massShellRouteAvailableConditionally :
      Bool

    massShellRouteAvailableConditionallyIsTrue :
      massShellRouteAvailableConditionally ≡ true

    gate3Promoted :
      Bool

    gate3PromotedIsFalse :
      gate3Promoted ≡ false

    clayPromoted :
      Bool

    clayPromotedIsFalse :
      clayPromoted ≡ false

    promotions :
      List Gate3PAWOTGUniformSeparationPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      Gate3PAWOTGUniformSeparationPromotion →
      ⊥

    targetStatement :
      String

    targetStatementIsCanonical :
      targetStatement ≡ uniformSeparationTargetStatement

    openObligationText :
      String

    openObligationTextIsCanonical :
      openObligationText ≡ openObligationStatement

    promotionBoundary :
      String

    promotionBoundaryIsCanonical :
      promotionBoundary ≡ promotionBoundaryStatement

open Gate3PAWOTGUniformSeparationTargetReceipt public

canonicalGate3PAWOTGUniformSeparationTargetReceipt :
  Gate3PAWOTGUniformSeparationTargetReceipt
canonicalGate3PAWOTGUniformSeparationTargetReceipt =
  record
    { status =
        pawotgUniformSeparationTargetRecorded_exactNextTheorem_noPromotion
    ; statusIsCanonical =
        refl
    ; localizationReductionReceipt =
        Localization.canonicalGate3AdelicLocalizationReductionReceipt
    ; localizationUniformSeparationStillOpen =
        refl
    ; localizationGate3StillFalse =
        refl
    ; pawotgConcreteConditionReceipt =
        PAWOTG.canonicalGate3PAWOTGConcreteConditionReceipt
    ; pawotgBindingPrimeIsP3 =
        refl
    ; pawotgUniformityStillOpen =
        refl
    ; pawotgClayStillFalse =
        refl
    ; normBindingReceipt =
        NormBinding.canonicalGate3AdelicSobolevNormBindingReceipt
    ; normBindingUniformContinuumStillOpen =
        refl
    ; moscoReceipt =
        Mosco.canonicalGate3MoscoRecoveryPreciseReceipt
    ; moscoConditionIRequiresDensity =
        refl
    ; moscoPAWOTGTransferStillOpen =
        refl
    ; moscoGate3StillFalse =
        refl
    ; noSpectralPollutionReceipt =
        NoPollution.canonicalGate3NoSpectralPollutionReceipt
    ; noSpectralPollutionStillConditional =
        refl
    ; noSpectralPollutionNotUnconditional =
        refl
    ; noSpectralPollutionGate3StillFalse =
        refl
    ; scaleGraphBarrierReceipt =
        Barrier.canonicalGate3ScaleGraphBarrierInstantiationReceipt
    ; scaleGraphBarrierPAWOTGBlocks =
        refl
    ; scaleGraphBarrierGate3StillFalse =
        refl
    ; hypotheses =
        canonicalPAWOTGUniformSeparationHypotheses
    ; hypothesesAreCanonical =
        refl
    ; conclusions =
        canonicalPAWOTGUniformSeparationConclusions
    ; conclusionsAreCanonical =
        refl
    ; openObligations =
        canonicalPAWOTGUniformSeparationOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; boundaries =
        canonicalPAWOTGUniformSeparationBoundaries
    ; boundariesAreCanonical =
        refl
    ; bindingPrime =
        p3BindingPrime
    ; bindingPrimeIsP3 =
        refl
    ; sigmaCritP3 =
        sigmaCritP3TenThousandths
    ; sigmaCritP3Is5052TenThousandths =
        refl
    ; explicitAdelicEmbeddingConstructedHere =
        false
    ; explicitAdelicEmbeddingConstructedHereIsFalse =
        refl
    ; pGeThreeArchimedeanLocalizationProvedHere =
        false
    ; pGeThreeArchimedeanLocalizationProvedHereIsFalse =
        refl
    ; uniformInDepthSpreadProvedHere =
        false
    ; uniformInDepthSpreadProvedHereIsFalse =
        refl
    ; infANPositiveProvedHere =
        false
    ; infANPositiveProvedHereIsFalse =
        refl
    ; moscoTransferProvedHere =
        false
    ; moscoTransferProvedHereIsFalse =
        refl
    ; noSpectralPollutionTransferProvedHere =
        false
    ; noSpectralPollutionTransferProvedHereIsFalse =
        refl
    ; massShellRouteAvailableConditionally =
        true
    ; massShellRouteAvailableConditionallyIsTrue =
        refl
    ; gate3Promoted =
        false
    ; gate3PromotedIsFalse =
        refl
    ; clayPromoted =
        false
    ; clayPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        gate3PAWOTGUniformSeparationPromotionImpossibleHere
    ; targetStatement =
        uniformSeparationTargetStatement
    ; targetStatementIsCanonical =
        refl
    ; openObligationText =
        openObligationStatement
    ; openObligationTextIsCanonical =
        refl
    ; promotionBoundary =
        promotionBoundaryStatement
    ; promotionBoundaryIsCanonical =
        refl
    }

gate3PAWOTGUniformSeparationTargetKeepsInfAOpen :
  infANPositiveProvedHere
    canonicalGate3PAWOTGUniformSeparationTargetReceipt
  ≡
  false
gate3PAWOTGUniformSeparationTargetKeepsInfAOpen =
  refl

gate3PAWOTGUniformSeparationTargetRecordsConditionalMassShellRoute :
  massShellRouteAvailableConditionally
    canonicalGate3PAWOTGUniformSeparationTargetReceipt
  ≡
  true
gate3PAWOTGUniformSeparationTargetRecordsConditionalMassShellRoute =
  refl

gate3PAWOTGUniformSeparationTargetNoGate3Promotion :
  gate3Promoted canonicalGate3PAWOTGUniformSeparationTargetReceipt ≡ false
gate3PAWOTGUniformSeparationTargetNoGate3Promotion =
  refl

gate3PAWOTGUniformSeparationTargetNoClayPromotion :
  clayPromoted canonicalGate3PAWOTGUniformSeparationTargetReceipt ≡ false
gate3PAWOTGUniformSeparationTargetNoClayPromotion =
  refl
