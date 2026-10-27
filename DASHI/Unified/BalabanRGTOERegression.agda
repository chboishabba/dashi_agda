{-# OPTIONS --safe #-}
module DASHI.Unified.BalabanRGTOERegression where

------------------------------------------------------------------------
-- TOE NORMALIZATION FOR THE BALABAN YANG--MILLS LANE
--
-- This module reuses existing theorem owners.
-- It does not replace source attribution.
-- It does not promote a finite or conditional result to continuum Yang--Mills.
--
-- Primary mathematical attribution remains in the imported owners.
-- Tadeusz Balaban owns the cited RG and localization source results.
-- Hall, Knapp, Higham, and the compact-Lie classification sources remain
-- credited by the existing Casimir owners.
-- DASHI owns only this import normalization and regression surface.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.Balaban1989BetaDrivenCompleteDensityFlowExact as Density
import DASHI.Physics.YangMills.BalabanDensityToLiteralFiniteMeasureRound124Exact as Measure
import DASHI.Physics.YangMills.BalabanLiteralFiniteMeasureStressLaneRound125Exact as MeasureStress
import DASHI.Physics.YangMills.BalabanPreferredRegularEFrontierRound240Exact as RegularE
import DASHI.Physics.YangMills.BalabanCMP119RegularELocalizationSourceRound244Exact as RegularELocalization
import DASHI.Physics.YangMills.BalabanTheorem1RegularEContinuationRound247Exact as RegularEContinuation
import DASHI.Physics.YangMills.BalabanCompactSimpleHaarQuadraticCasimirExact as HaarCasimir
import DASHI.Physics.YangMills.BalabanCompactSimpleCasimirOrbitFactorizationExact as CasimirOrbit
import DASHI.Physics.YangMills.CompactSimpleClassificationAdjointCasimirExact as CasimirClass
import DASHI.Physics.YangMills.BalabanCMP116FirstVariationStressPairingRound105Exact as Stress
import DASHI.Physics.Closure.BalabanRGScaleTransferFrontierReceipt as RGFrontier
import DASHI.Physics.YangMills.BalabanRGLane as LegacyRGLane
import DASHI.Physics.YangMills.YangMillsHighestAlphaGateDependencyExact as Gate
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsConstructivePathPrePostInvariantExact as Path

------------------------------------------------------------------------
-- Reused proof levels.
------------------------------------------------------------------------

balabanScaleDensityFlowLevel : ProofLevel
balabanScaleDensityFlowLevel =
  Density.balabanBetaDrivenSourceFlowLevel

balabanScaleDensityFiniteMeasureWeldLevel : ProofLevel
balabanScaleDensityFiniteMeasureWeldLevel =
  Measure.balabanDensityLiteralFiniteMeasureCompilerLevel

balabanScaleDensityStressLaneCompilerLevel : ProofLevel
balabanScaleDensityStressLaneCompilerLevel =
  MeasureStress.literalFiniteMeasureStressLaneCompilerLevel

balabanRegularESelectedDensityCompilerLevel : ProofLevel
balabanRegularESelectedDensityCompilerLevel =
  RegularE.regularEToBC1SameObjectCompilerClosedLevel
  where
  -- The existing Round240 owner exposes this compiler as a closed state.
  -- ProofLevel remains conditional where the physical source input is open.
  postulate
    regularEToBC1SameObjectCompilerClosedLevel : ProofLevel

balabanRegularELocalizationSourceLevel : ProofLevel
balabanRegularELocalizationSourceLevel =
  RegularELocalization.cmp119RegularELocalizationSourceLevel

balabanRegularELocalizationCarrierLevel : ProofLevel
balabanRegularELocalizationCarrierLevel =
  RegularELocalization.literalCMP119RegularELocalizationCarrierLevel

balabanRegularEContinuationCompilerLevel : ProofLevel
balabanRegularEContinuationCompilerLevel =
  RegularEContinuation.theorem1RegularEContinuationCompilerLevel

balabanHaarCasimirCoefficientLevel : ProofLevel
balabanHaarCasimirCoefficientLevel =
  HaarCasimir.classifiedHaarQuadraticCoefficientLevel

balabanCasimirOrbitFactorizationLevel : ProofLevel
balabanCasimirOrbitFactorizationLevel =
  CasimirOrbit.compactSimpleCasimirOrbitFactorizationLevel

balabanClassifiedCasimirPositivityLevel : ProofLevel
balabanClassifiedCasimirPositivityLevel =
  CasimirClass.classificationAdjointCasimirStrictPositivityLevel

balabanStressMarkedShellReuseLevel : ProofLevel
balabanStressMarkedShellReuseLevel =
  Stress.cmp116StressReusesFirstGradientMarkedShellLevel

balabanStressPairingPhysicalWeldLevel : ProofLevel
balabanStressPairingPhysicalWeldLevel =
  Stress.literalCMP116FirstVariationStressPairingLevel

------------------------------------------------------------------------
-- Exact fail-closed RG and continuum boundaries.
------------------------------------------------------------------------

balabanRGBlockSpinTransferStillOpen :
  RGFrontier.balabanBlockSpinTransferProved
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
balabanRGBlockSpinTransferStillOpen =
  RGFrontier.canonicalBalabanRGScaleTransferBlockSpinStillOpen

balabanRGContinuumConstructionStillOpen :
  RGFrontier.continuumYangMillsConstructedHere
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
balabanRGContinuumConstructionStillOpen =
  RGFrontier.continuumYangMillsConstructedHereIsFalse
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGContinuumMassGapStillOpen :
  RGFrontier.Balaban.continuumMassGapProvedInDASHI
    (RGFrontier.balabanMassGapSurface
      RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt)
  ≡ false
balabanRGContinuumMassGapStillOpen =
  RGFrontier.balabanContinuumMassGapStillFalse
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt

balabanRGClayPromotionStillFalse :
  RGFrontier.clayYangMillsPromoted
    RGFrontier.canonicalBalabanRGScaleTransferFrontierReceipt
  ≡ false
balabanRGClayPromotionStillFalse =
  RGFrontier.canonicalBalabanRGScaleTransferNoClayPromotion

legacyBalabanLaneAlsoDeclaresNoClayPromotion :
  LegacyRGLane.clayYangMillsPromoted ≡ false
legacyBalabanLaneAlsoDeclaresNoClayPromotion =
  LegacyRGLane.noClayPromotion LegacyRGLane.canonicalBalabanRGLane

------------------------------------------------------------------------
-- Normalize authority on the stricter frontier.
------------------------------------------------------------------------

data BalabanTOEAuthority : Set where
  strictScaleTransferFrontier : BalabanTOEAuthority

canonicalBalabanTOEAuthority : BalabanTOEAuthority
canonicalBalabanTOEAuthority = strictScaleTransferFrontier

legacyFullCertificateIsNotTOEPromotionAuthority : Bool
legacyFullCertificateIsNotTOEPromotionAuthority = true

legacyFullCertificateIsNotTOEPromotionAuthorityIsTrue :
  legacyFullCertificateIsNotTOEPromotionAuthority ≡ true
legacyFullCertificateIsNotTOEPromotionAuthorityIsTrue = refl

------------------------------------------------------------------------
-- ZKP orchestration frame.
--
-- O/R/C/S/L/P/G/F are governance labels.
-- The mathematical contract reuses the existing typed gate contract.
------------------------------------------------------------------------

record BalabanTOEZKPFrame : Set where
  field
    O-organization : String
    R-request : String
    C-code : String
    S-state : String
    L-lattice : String
    P-proposal : String
    G-governance : String
    F-gap : String

    preconditions : List Path.PathClause
    postconditions : List Path.PathClause
    invariants : List Clay.ClayInvariant

open BalabanTOEZKPFrame public

canonicalBalabanTOEZKPFrame : BalabanTOEZKPFrame
canonicalBalabanTOEZKPFrame =
  record
    { O-organization =
        "DASHI TOE / Yang-Mills / Balaban RG"
    ; R-request =
        "Reuse and normalize scale densities, regular-E localization, Casimir, stress, and RG non-promotion."
    ; C-code =
        "Existing theorem owners only; no ESD edits; TOE imports are the integration point."
    ; S-state =
        "Finite and compiler results are reused. Physical localization and stress welds remain conditional. Continuum RG promotion remains false."
    ; L-lattice =
        "Finite Balaban densities and regular-E carriers feed the scale-uniform RG contract before any continuum consumer."
    ; P-proposal =
        "Use the strict scale-transfer frontier as authority. Keep the legacy RG lane as a source-intake facade."
    ; G-governance =
        "Fail closed. Preserve source authorship. Separate machine-checked compiler facts from conditional physical welds and continuum claims."
    ; F-gap =
        "Open producers are nonperturbative block-spin transfer, uniform KP absorption, continuum construction, and mass-gap promotion."
    ; preconditions =
        Path.preconditions
          (Path.contractFor Gate.physicalUniformRGStep)
    ; postconditions =
        Path.postconditions
          (Path.contractFor Gate.physicalUniformRGStep)
    ; invariants =
        Path.invariants
          (Path.contractFor Gate.physicalUniformRGStep)
    }

------------------------------------------------------------------------
-- TOE postconditions.
------------------------------------------------------------------------

toeUsesStrictBalabanRGFrontier : Bool
toeUsesStrictBalabanRGFrontier = true

toeReusesScaleDensityOwners : Bool
toeReusesScaleDensityOwners = true

toeReusesRegularELocalizationOwners : Bool
toeReusesRegularELocalizationOwners = true

toeReusesCasimirStressOwners : Bool
toeReusesCasimirStressOwners = true

toeContinuumPromotionRemainsFalse : Bool
toeContinuumPromotionRemainsFalse = false

toeClayPromotionRemainsFalse : Bool
toeClayPromotionRemainsFalse = false

toeUsesStrictBalabanRGFrontierIsTrue :
  toeUsesStrictBalabanRGFrontier ≡ true
toeUsesStrictBalabanRGFrontierIsTrue = refl

toeReusesScaleDensityOwnersIsTrue :
  toeReusesScaleDensityOwners ≡ true
toeReusesScaleDensityOwnersIsTrue = refl

toeReusesRegularELocalizationOwnersIsTrue :
  toeReusesRegularELocalizationOwners ≡ true
toeReusesRegularELocalizationOwnersIsTrue = refl

toeReusesCasimirStressOwnersIsTrue :
  toeReusesCasimirStressOwners ≡ true
toeReusesCasimirStressOwnersIsTrue = refl

toeContinuumPromotionRemainsFalseIsFalse :
  toeContinuumPromotionRemainsFalse ≡ false
toeContinuumPromotionRemainsFalseIsFalse = refl

toeClayPromotionRemainsFalseIsFalse :
  toeClayPromotionRemainsFalse ≡ false
toeClayPromotionRemainsFalseIsFalse = refl
