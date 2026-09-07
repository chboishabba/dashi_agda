{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13CurrentPreferredSourceFrontierExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): CURRENT PREFERRED SOURCE FRONTIER
--
-- This status supersedes the older recovered-source archaeology without
-- deleting it.  It tracks the actual preferred compiler after:
--   * the R148/R153 source-sign correction;
--   * T3 right-Jacobian x-pollination;
--   * pruning the whole Bishop bridge to the R208 ring-embedding boundary;
--   * splitting Path13 physical variational/radius data from R171 standard
--     operator-representation authority;
--   * specializing the Bałaban variational theorem directly to the literal
--     Path13 fine-field carrier, making selected-background and selected-link
--     same-object receipts definitional;
--   * deriving the historical variational-radius record from that specialization
--     plus three exact normalization facts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98Path13PreferredSplitPhysicalT3SourceFamilyExact as Preferred
import DASHI.Physics.YangMills.BalabanPath13SplitPhysicalStandardOperatorCutExact as Split
import DASHI.Physics.YangMills.BalabanPath13SelectedVariationalRadiusExact as VariationalRadius
import DASHI.Physics.YangMills.BalabanPath13VariationalSpecializationExact as Specialization
import DASHI.Physics.YangMills.BalabanPath13VariationalRadiusFromSpecializationExact as SpecializedRadius
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
    splitPhysicalStandardCompilerClosed : Bool
    splitPrincipalImageCompilerClosed : Bool
    finalSplitT3Eq119CompilerClosed : Bool

    -- Current Path13 source/normalization inputs.
    path13VariationalSourceSpecializationConstructed : Bool
    path13VariationalRadiusNormalizationConstructed : Bool

    -- Historical compatibility summary: this larger object is compiler output
    -- once the two refined inputs above are supplied.
    selectedPath13VariationalRadiusConstructed : Bool

    selectedCutOperatorSameObjectWeldConstructed : Bool
    selectedT3NormalizationConstructed : Bool
    selectedCutThresholdConstructed : Bool

    -- Source-independent/foundational authorities still requiring inhabitants.
    standardR171OperatorRepresentationConstructed : Bool
    rationalRealRingEmbeddingConstructed : Bool

    physicalEq119Closed : Bool
open CurrentPreferredEq119FrontierStatus public

canonicalCurrentPreferredEq119FrontierStatus : CurrentPreferredEq119FrontierStatus
canonicalCurrentPreferredEq119FrontierStatus =
  currentPreferredEq119FrontierStatus
    true true true true true true true
    false false
    false
    false false false
    false false
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

Path13VariationalSourceSpecializationInput : Set → Set → Set₁
Path13VariationalSourceSpecializationInput =
  Specialization.Path13VariationalSpecialization

Path13VariationalRadiusNormalizationInput : Set → Set₁
Path13VariationalRadiusNormalizationInput =
  SpecializedRadius.Path13VariationalRadiusNormalization

-- Compatibility surface: now compiler output from the refined source cut.
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

-- These remain input surfaces, not theorem claims.
literalCMP98Path13VariationalSourceSpecializationLevel : ProofLevel
literalCMP98Path13VariationalSourceSpecializationLevel = conditional

literalCMP98Path13VariationalRadiusNormalizationLevel : ProofLevel
literalCMP98Path13VariationalRadiusNormalizationLevel = conditional

literalCMP98Path13SelectedCutOperatorWeldLevel : ProofLevel
literalCMP98Path13SelectedCutOperatorWeldLevel = conditional

literalCMP98Path13SelectedT3NormalizationLevel : ProofLevel
literalCMP98Path13SelectedT3NormalizationLevel = conditional

literalCMP98Path13CutThresholdLevel : ProofLevel
literalCMP98Path13CutThresholdLevel = conditional

literalCMP98R171StandardOperatorRepresentationLevel : ProofLevel
literalCMP98R171StandardOperatorRepresentationLevel =
  R171.cmp98RationalSU2OperatorRepresentationRound171Level

literalCMP98RationalRealRingEmbeddingLevel : ProofLevel
literalCMP98RationalRealRingEmbeddingLevel =
  R208.rationalRealMultiplicativeEmbeddingRound208Level
