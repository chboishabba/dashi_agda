{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): CURRENT LEAST-PRIVILEGE SOURCE FRONTIER
--
-- Current preferred route after:
--   * source-sign repair to dexpPlus/Jplus/Ad(exp);
--   * direct Path13 variational specialization;
--   * R171 defect-algebra alignment;
--   * pruning full T3 to PrintedSemanticOperators + chart weld;
--   * pruning the historical 1/24 cut to the literal 74-link budget
--       37/1024 <= selected chart radius.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredR171AlignedPrintedSourceExact as Preferred
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13VariationalSpecializationExact as Specialization
import DASHI.Physics.YangMills.BalabanPath13VariationalRadiusFromSpecializationExact as SpecializedRadius
import DASHI.Physics.YangMills.BalabanR171OperatorKernelGroupDefectAdapterExact as R171Adapter
import DASHI.Physics.YangMills.BalabanPath13R171AlignedVariationalRouteExact as R171Aligned
import DASHI.Physics.YangMills.BalabanCMP98SU2OperatorDefectFromPhysicalRadiusRound171Exact as R171
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as R208
import DASHI.Physics.YangMills.BalabanCMP98Path13SplitT3SelectedSemanticsExact as T3
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalPrincipalImageRouteExact as Principal
import DASHI.Physics.YangMills.BalabanPath13DirectRelative74CutExact as Direct74

record CurrentPreferredEq119FrontierStatus : Set where
  constructor currentPreferredEq119FrontierStatus
  field
    printedRoleCorrectionClosed : Bool
    t3PrintedOperatorAdapterClosed : Bool
    path13VariationalSpecializationCompilerClosed : Bool
    path13VariationalRadiusFromSpecializationCompilerClosed : Bool
    r171KernelGroupDefectAdapterClosed : Bool
    r171AlignedVariationalRouteClosed : Bool
    selectedCutOperatorPointwiseWeldPruned : Bool
    minimalPrintedSemanticsRouteClosed : Bool
    directRelative74CutCompilerClosed : Bool
    currentPreferredEq119CompilerClosed : Bool

    -- Current independent source payments.
    r171AlignedPath13PhysicalSourceConstructed : Bool
    selectedPrintedSemanticsConstructed : Bool
    relative74CutThresholdConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool

    -- Compatibility/producer coordinates retained for archaeology and reuse.
    path13VariationalSourceSpecializationConstructed : Bool
    path13VariationalRadiusNormalizationConstructed : Bool
    selectedPath13VariationalRadiusConstructed : Bool
    selectedCutOperatorSameObjectWeldConstructed : Bool
    selectedT3NormalizationConstructed : Bool
    selectedCutThresholdConstructed : Bool
    standardR171OperatorRepresentationConstructed : Bool

    physicalEq119Closed : Bool
open CurrentPreferredEq119FrontierStatus public

canonicalCurrentPreferredEq119FrontierStatus : CurrentPreferredEq119FrontierStatus
canonicalCurrentPreferredEq119FrontierStatus =
  currentPreferredEq119FrontierStatus
    true true true true true true true true true true
    false false false false
    false false false false false false false
    false

currentPreferredEq119CompilerClosedIsTrue :
  currentPreferredEq119CompilerClosed
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
currentPreferredEq119CompilerClosedIsTrue = refl

-- Compatibility alias used by canonical consumers created before the
-- least-privilege minimization.
finalSplitT3Eq119CompilerClosed : CurrentPreferredEq119FrontierStatus → Bool
finalSplitT3Eq119CompilerClosed = currentPreferredEq119CompilerClosed

finalSplitT3Eq119CompilerClosedIsTrue :
  finalSplitT3Eq119CompilerClosed canonicalCurrentPreferredEq119FrontierStatus ≡ true
finalSplitT3Eq119CompilerClosedIsTrue = currentPreferredEq119CompilerClosedIsTrue

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalCurrentPreferredEq119FrontierStatus ≡ false
physicalEq119ClosedIsFalse = refl

------------------------------------------------------------------------
-- Typed surviving source surfaces.
------------------------------------------------------------------------

Path13R171AlignedPhysicalSourceInput : Set → Set₁
Path13R171AlignedPhysicalSourceInput =
  R171Aligned.R171AlignedPath13PhysicalInputs

Path13SelectedPrintedSemanticsInput :
  ∀ {CoarseField} →
  Path13R171AlignedPhysicalSourceInput CoarseField → Set₁
Path13SelectedPrintedSemanticsInput =
  Preferred.R171AlignedSelectedPrintedSemantics

Path13RationalRealRingEmbeddingInput : Set₁
Path13RationalRealRingEmbeddingInput = R208.RationalRealRingEmbedding

Path13SplitRepresentationInput : Set → Set₁
Path13SplitRepresentationInput = Split.SplitPath13PhysicalStandardRepresentation

Path13Relative74CutThresholdInput :
  ∀ {CoarseField} → Path13SplitRepresentationInput CoarseField → Set
Path13Relative74CutThresholdInput = Direct74.SplitPath13Relative74CutThreshold

CurrentPreferredEq119Inputs : Set → Set₁
CurrentPreferredEq119Inputs =
  Preferred.PreferredR171AlignedPrintedPath13Inputs

------------------------------------------------------------------------
-- Compatibility surfaces below the current preferred cut.
------------------------------------------------------------------------

Path13VariationalSourceSpecializationInput : Set → Set → Set₁
Path13VariationalSourceSpecializationInput =
  Specialization.Path13VariationalSpecialization

Path13VariationalRadiusNormalizationInput : Set → Set₁
Path13VariationalRadiusNormalizationInput =
  SpecializedRadius.Path13VariationalRadiusNormalization

Path13PhysicalVariationalRadiusInput : Set → Set₁
Path13PhysicalVariationalRadiusInput =
  VariationalRadius.Path13SelectedVariationalRadiusRepresentation

Path13StandardOperatorRepresentationInput : Set₁
Path13StandardOperatorRepresentationInput =
  R171.RationalSU2OperatorDefectRepresentation

Path13SelectedT3Input :
  ∀ {CoarseField} → Path13SplitRepresentationInput CoarseField → Set → Set₁
Path13SelectedT3Input representation Scalar =
  T3.SplitSelectedT3PrintedSemantics {Scalar = Scalar} representation

Path13HistoricalCutThresholdInput :
  ∀ {CoarseField} → Path13SplitRepresentationInput CoarseField → Set
Path13HistoricalCutThresholdInput = Principal.SplitPath13CutThreshold

cmp98Path13CurrentPreferredSourceFrontierLevel : ProofLevel
cmp98Path13CurrentPreferredSourceFrontierLevel = machineChecked

path13VariationalSpecializationCompilerLevel : ProofLevel
path13VariationalSpecializationCompilerLevel =
  Specialization.path13VariationalSpecializationCompilerLevel

path13VariationalRadiusFromSpecializationLevel : ProofLevel
path13VariationalRadiusFromSpecializationLevel =
  SpecializedRadius.path13VariationalRadiusFromSpecializationLevel

r171KernelGroupDefectAdapterLevel : ProofLevel
r171KernelGroupDefectAdapterLevel =
  R171Adapter.operatorKernelGroupDefectAdapterLevel

r171AlignedVariationalRouteLevel : ProofLevel
r171AlignedVariationalRouteLevel =
  R171Aligned.r171AlignedPath13VariationalRouteLevel

minimalPrintedSemanticsRouteLevel : ProofLevel
minimalPrintedSemanticsRouteLevel =
  Preferred.preferredR171AlignedPrintedSourceCompilerLevel

directRelative74CutCompilerLevel : ProofLevel
directRelative74CutCompilerLevel = Direct74.relative74DirectCutCompilerLevel

-- Current independent input surfaces.
literalCMP98Path13R171AlignedPhysicalSourceLevel : ProofLevel
literalCMP98Path13R171AlignedPhysicalSourceLevel = conditional

literalCMP98Path13SelectedPrintedSemanticsLevel : ProofLevel
literalCMP98Path13SelectedPrintedSemanticsLevel = conditional

literalCMP98Path13Relative74CutThresholdLevel : ProofLevel
literalCMP98Path13Relative74CutThresholdLevel = conditional

literalCMP98RationalRealRingEmbeddingLevel : ProofLevel
literalCMP98RationalRealRingEmbeddingLevel =
  R208.rationalRealMultiplicativeEmbeddingRound208Level

-- Compatibility authority/status surfaces.
literalCMP98Path13SelectedT3NormalizationLevel : ProofLevel
literalCMP98Path13SelectedT3NormalizationLevel = conditional

literalCMP98R171StandardOperatorRepresentationLevel : ProofLevel
literalCMP98R171StandardOperatorRepresentationLevel =
  R171.cmp98RationalSU2OperatorRepresentationRound171Level
