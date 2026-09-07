{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): CURRENT PREFERRED SOURCE FRONTIER
--
-- This status supersedes the older recovered-source archaeology without
-- deleting it.  The preferred route now also aligns the selected/cut defect
-- algebra definitionally with the R171 operator kernel.  Therefore the old
-- pointwise selected-cut/operator weld is not a separate source payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredSplitPhysicalT3SourceFamilyExact as Preferred
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
    splitPhysicalStandardCompilerClosed : Bool
    splitPrincipalImageCompilerClosed : Bool
    finalSplitT3Eq119CompilerClosed : Bool

    -- Current preferred Path13 source input.  This nests the standard R171
    -- representation and source/physical normalization facts in one same-object
    -- carrier; the pointwise cut/operator weld is compiler output.
    r171AlignedPath13PhysicalSourceConstructed : Bool

    -- Historical compatibility coordinates retained for older consumers.
    path13VariationalSourceSpecializationConstructed : Bool
    path13VariationalRadiusNormalizationConstructed : Bool
    selectedPath13VariationalRadiusConstructed : Bool
    selectedCutOperatorSameObjectWeldConstructed : Bool

    -- Still-live independent inputs after R171 alignment.
    selectedT3NormalizationConstructed : Bool
    selectedCutThresholdConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool

    -- R171 authority remains inside the aligned physical source, rather than as
    -- an independent pointwise-defect weld.
    standardR171OperatorRepresentationConstructed : Bool

    physicalEq119Closed : Bool
open CurrentPreferredEq119FrontierStatus public

canonicalCurrentPreferredEq119FrontierStatus : CurrentPreferredEq119FrontierStatus
canonicalCurrentPreferredEq119FrontierStatus =
  currentPreferredEq119FrontierStatus
    true true true true true true true true true true
    false
    false false false false
    false false false
    false
    false

printedRoleCorrectionClosedIsTrue :
  printedRoleCorrectionClosed canonicalCurrentPreferredEq119FrontierStatus ≡ true
printedRoleCorrectionClosedIsTrue = refl

t3PrintedOperatorAdapterClosedIsTrue :
  t3PrintedOperatorAdapterClosed canonicalCurrentPreferredEq119FrontierStatus ≡ true
t3PrintedOperatorAdapterClosedIsTrue = refl

path13VariationalSpecializationCompilerClosedIsTrue :
  path13VariationalSpecializationCompilerClosed
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
path13VariationalSpecializationCompilerClosedIsTrue = refl

path13VariationalRadiusFromSpecializationCompilerClosedIsTrue :
  path13VariationalRadiusFromSpecializationCompilerClosed
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
path13VariationalRadiusFromSpecializationCompilerClosedIsTrue = refl

r171KernelGroupDefectAdapterClosedIsTrue :
  r171KernelGroupDefectAdapterClosed
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
r171KernelGroupDefectAdapterClosedIsTrue = refl

r171AlignedVariationalRouteClosedIsTrue :
  r171AlignedVariationalRouteClosed
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
r171AlignedVariationalRouteClosedIsTrue = refl

selectedCutOperatorPointwiseWeldPrunedIsTrue :
  selectedCutOperatorPointwiseWeldPruned
    canonicalCurrentPreferredEq119FrontierStatus ≡ true
selectedCutOperatorPointwiseWeldPrunedIsTrue = refl

splitPhysicalStandardCompilerClosedIsTrue :
  splitPhysicalStandardCompilerClosed canonicalCurrentPreferredEq119FrontierStatus ≡ true
splitPhysicalStandardCompilerClosedIsTrue = refl

finalSplitT3Eq119CompilerClosedIsTrue :
  finalSplitT3Eq119CompilerClosed canonicalCurrentPreferredEq119FrontierStatus ≡ true
finalSplitT3Eq119CompilerClosedIsTrue = refl

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalCurrentPreferredEq119FrontierStatus ≡ false
physicalEq119ClosedIsFalse = refl

------------------------------------------------------------------------
-- Typed surviving source surfaces.
------------------------------------------------------------------------

Path13R171AlignedPhysicalSourceInput : Set → Set₁
Path13R171AlignedPhysicalSourceInput =
  R171Aligned.R171AlignedPath13PhysicalInputs

-- Compatibility surfaces below the current preferred cut.
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

Path13RationalRealRingEmbeddingInput : Set₁
Path13RationalRealRingEmbeddingInput = R208.RationalRealRingEmbedding

Path13SplitRepresentationInput : Set → Set₁
Path13SplitRepresentationInput = Split.SplitPath13PhysicalStandardRepresentation

Path13CutThresholdInput :
  ∀ {CoarseField} → Path13SplitRepresentationInput CoarseField → Set
Path13CutThresholdInput = Principal.SplitPath13CutThreshold

Path13SelectedT3Input :
  ∀ {CoarseField} → Path13SplitRepresentationInput CoarseField → Set → Set₁
Path13SelectedT3Input representation Scalar =
  T3.SplitSelectedT3PrintedSemantics {Scalar = Scalar} representation

CurrentPreferredEq119Inputs : Set → Set → Set₁
CurrentPreferredEq119Inputs = Preferred.PreferredSplitPhysicalT3Path13Inputs

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

selectedCutOperatorPointwiseWeldPruningLevel : ProofLevel
selectedCutOperatorPointwiseWeldPruningLevel = machineChecked

-- Current independent input surfaces.
literalCMP98Path13R171AlignedPhysicalSourceLevel : ProofLevel
literalCMP98Path13R171AlignedPhysicalSourceLevel = conditional

literalCMP98Path13SelectedT3NormalizationLevel : ProofLevel
literalCMP98Path13SelectedT3NormalizationLevel = conditional

literalCMP98Path13CutThresholdLevel : ProofLevel
literalCMP98Path13CutThresholdLevel = conditional

literalCMP98RationalRealRingEmbeddingLevel : ProofLevel
literalCMP98RationalRealRingEmbeddingLevel =
  R208.rationalRealMultiplicativeEmbeddingRound208Level

-- Compatibility authority/status surfaces.
literalCMP98R171StandardOperatorRepresentationLevel : ProofLevel
literalCMP98R171StandardOperatorRepresentationLevel =
  R171.cmp98RationalSU2OperatorRepresentationRound171Level
