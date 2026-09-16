module DASHI.Physics.YangMills.BalabanCMP102CriticalMapLipschitzRound367Exact where

------------------------------------------------------------------------
-- ROUND367 / SOURCE C-LIPSCHITZ IS A THEOREM COORDINATE, NOT A FREE SCALAR
--
-- CMP116 Part II, Sect. 1 reuses the variational/background construction from
-- CMP102 and writes the substituted-background fixed-point equation
--
--   D(A') = C(A' - H D(A')).
--
-- The source discussion around (1.12)--(1.13) places the transformation on one
-- common small ball, proves that it maps the ball into itself, and proves it is
-- contractive there.  R366 previously represented the resulting C-Lipschitz
-- step only as a scalar inequality field.
--
-- This module makes that payment proof-bearing on the SAME C carrier:
--
--   d(C x,C y) <= L_C d(x,y).
--
-- Once two R366 arguments are attached to this source carrier, its first
-- inequality is compiler output.  This file does NOT identify an arbitrary
-- older nonlinear map with CMP102/CMP116 C, and it does NOT attach CMP99's
-- propagator comparison to the selected H(s(Y0)).  Those remain independent
-- same-object payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanPublishedAnalyticAuthorities as Published
import DASHI.Physics.YangMills.BalabanCMP116OneStepMapDefectRound366Exact as R366

------------------------------------------------------------------------
-- Source theorem shape.
------------------------------------------------------------------------

record CMP102CriticalMapContractionData (Point : Set) : Set₁ where
  field
    criticalMap : Point → Point
    distance : Point → Point → ℝ
    InSourceBall : Point → Set

    lipschitzConstant : ℝ
    lipschitzConstantNonnegative : 0ℝ ≤ℝ lipschitzConstant

    -- Proof-bearing quantitative content of the source contraction step.
    criticalMapLipschitz :
      ∀ left right →
      InSourceBall left →
      InSourceBall right →
      distance (criticalMap left) (criticalMap right)
        ≤ℝ lipschitzConstant *ℝ distance left right

open CMP102CriticalMapContractionData public

------------------------------------------------------------------------
-- Same-object attachment into the R366 factorization.
------------------------------------------------------------------------

record CMP102CriticalMapToR366Data (Point : Set) : Set₁ where
  field
    source : CMP102CriticalMapContractionData Point

    leftArgument rightArgument : Point
    leftArgumentInSourceBall : InSourceBall source leftArgument
    rightArgumentInSourceBall : InSourceBall source rightArgument

    mapDefect : ℝ
    argumentDefect : ℝ
    propagatorActionDefect : ℝ
    propagatorDifference : ℝ
    candidateSize : ℝ
    candidateRadius : ℝ

    mapDefectNonnegative : 0ℝ ≤ℝ mapDefect
    argumentDefectNonnegative : 0ℝ ≤ℝ argumentDefect
    propagatorActionDefectNonnegative : 0ℝ ≤ℝ propagatorActionDefect
    propagatorDifferenceNonnegative : 0ℝ ≤ℝ propagatorDifference
    candidateSizeNonnegative : 0ℝ ≤ℝ candidateSize
    candidateRadiusNonnegative : 0ℝ ≤ℝ candidateRadius

    -- These are the only same-object welds needed for the C-Lipschitz stage.
    mapDefectIsSourceDistance :
      mapDefect ≡
      distance source
        (criticalMap source leftArgument)
        (criticalMap source rightArgument)

    argumentDefectIsSourceDistance :
      argumentDefect ≡ distance source leftArgument rightArgument

    -- Remaining R366 coordinates are intentionally not manufactured here.
    argumentDefectBelowPropagatorAction :
      argumentDefect ≤ℝ propagatorActionDefect

    propagatorActionDefectBelowDifferenceTimesCandidate :
      propagatorActionDefect ≤ℝ propagatorDifference *ℝ candidateSize

    candidateSizeBelowRadius : candidateSize ≤ℝ candidateRadius

open CMP102CriticalMapToR366Data public

sourceCriticalMapPaysR366LipschitzStep :
  ∀ {Point}
    (dataSet : CMP102CriticalMapToR366Data Point) →
  mapDefect dataSet
    ≤ℝ
  lipschitzConstant (source dataSet) *ℝ argumentDefect dataSet
sourceCriticalMapPaysR366LipschitzStep dataSet
  rewrite mapDefectIsSourceDistance dataSet
        | argumentDefectIsSourceDistance dataSet =
  criticalMapLipschitz (source dataSet)
    (leftArgument dataSet)
    (rightArgument dataSet)
    (leftArgumentInSourceBall dataSet)
    (rightArgumentInSourceBall dataSet)

round367ToR366Factors :
  ∀ {Point} →
  CMP102CriticalMapToR366Data Point →
  R366.CMP116OneStepMapDefectFactors
round367ToR366Factors dataSet = record
  { R366.mapDefect = mapDefect dataSet
  ; R366.argumentDefect = argumentDefect dataSet
  ; R366.propagatorActionDefect = propagatorActionDefect dataSet
  ; R366.nonlinearLipschitz = lipschitzConstant (source dataSet)
  ; R366.propagatorDifference = propagatorDifference dataSet
  ; R366.candidateSize = candidateSize dataSet
  ; R366.candidateRadius = candidateRadius dataSet
  ; R366.mapDefectNonnegative = mapDefectNonnegative dataSet
  ; R366.argumentDefectNonnegative = argumentDefectNonnegative dataSet
  ; R366.propagatorActionDefectNonnegative =
      propagatorActionDefectNonnegative dataSet
  ; R366.nonlinearLipschitzNonnegative =
      lipschitzConstantNonnegative (source dataSet)
  ; R366.propagatorDifferenceNonnegative =
      propagatorDifferenceNonnegative dataSet
  ; R366.candidateSizeNonnegative = candidateSizeNonnegative dataSet
  ; R366.candidateRadiusNonnegative = candidateRadiusNonnegative dataSet
  ; R366.mapDefectBelowLipschitzArgument =
      sourceCriticalMapPaysR366LipschitzStep dataSet
  ; R366.argumentDefectBelowPropagatorAction =
      argumentDefectBelowPropagatorAction dataSet
  ; R366.propagatorActionDefectBelowDifferenceTimesCandidate =
      propagatorActionDefectBelowDifferenceTimesCandidate dataSet
  ; R366.candidateSizeBelowRadius = candidateSizeBelowRadius dataSet
  }

round367MapDefectBelowAssociatedSourceProduct :
  ∀ {Point}
    (dataSet : CMP102CriticalMapToR366Data Point) →
  mapDefect dataSet
    ≤ℝ
  (lipschitzConstant (source dataSet) *ℝ propagatorDifference dataSet)
    *ℝ candidateRadius dataSet
round367MapDefectBelowAssociatedSourceProduct dataSet =
  R366.mapDefectBelowAssociatedSourceProduct
    (round367ToR366Factors dataSet)

------------------------------------------------------------------------
-- Pareto / source accounting.
------------------------------------------------------------------------

cmp102VariationalBackgroundSourceLevel : ProofLevel
cmp102VariationalBackgroundSourceLevel =
  Published.publishedVariationalBackgroundLevel

cmp102CriticalMapContractionSourceShapeLevel : ProofLevel
cmp102CriticalMapContractionSourceShapeLevel = standardImported

literalCMP102CriticalMapSameObjectAttachmentLevel : ProofLevel
literalCMP102CriticalMapSameObjectAttachmentLevel = conditional

literalCMP99ToCMP116PropagatorDifferenceAttachmentLevel : ProofLevel
literalCMP99ToCMP116PropagatorDifferenceAttachmentLevel = conditional

literalCMP116CriticalMapArgumentIdentityLevel : ProofLevel
literalCMP116CriticalMapArgumentIdentityLevel = conditional

round367SourceLipschitzCompilerLevel : ProofLevel
round367SourceLipschitzCompilerLevel = machineChecked

cLipschitzScalarInequalityPrimitiveAfterRound367 : Bool
cLipschitzScalarInequalityPrimitiveAfterRound367 = false

cLipschitzScalarInequalityPrimitiveAfterRound367IsFalse :
  cLipschitzScalarInequalityPrimitiveAfterRound367 ≡ false
cLipschitzScalarInequalityPrimitiveAfterRound367IsFalse = refl

cmp102AnalyticityAlonePaysQuantitativeLipschitz : Bool
cmp102AnalyticityAlonePaysQuantitativeLipschitz = false

cmp102AnalyticityAlonePaysQuantitativeLipschitzIsFalse :
  cmp102AnalyticityAlonePaysQuantitativeLipschitz ≡ false
cmp102AnalyticityAlonePaysQuantitativeLipschitzIsFalse = refl

sourceContractionReceiptCanPayR366FirstStage : Bool
sourceContractionReceiptCanPayR366FirstStage = true

sourceContractionReceiptCanPayR366FirstStageIsTrue :
  sourceContractionReceiptCanPayR366FirstStage ≡ true
sourceContractionReceiptCanPayR366FirstStageIsTrue = refl

cmp99StillNeedsSameObjectPropagatorAttachment : Bool
cmp99StillNeedsSameObjectPropagatorAttachment = true

cmp99StillNeedsSameObjectPropagatorAttachmentIsTrue :
  cmp99StillNeedsSameObjectPropagatorAttachment ≡ true
cmp99StillNeedsSameObjectPropagatorAttachmentIsTrue = refl

record Round367Boundary : Set where
  constructor round367-boundary
  field
    sourceContractionIsUpstreamOfR366 : Bool
    sourceContractionIsUpstreamOfR366IsTrue :
      sourceContractionIsUpstreamOfR366 ≡ true

    analyticStatusDoesNotManufactureLipschitz : Bool
    analyticStatusDoesNotManufactureLipschitzIsTrue :
      analyticStatusDoesNotManufactureLipschitz ≡ true

    sameObjectCStillRequired : Bool
    sameObjectCStillRequiredIsTrue : sameObjectCStillRequired ≡ true

    sameObjectHStillRequired : Bool
    sameObjectHStillRequiredIsTrue : sameObjectHStillRequired ≡ true

canonicalRound367Boundary : Round367Boundary
canonicalRound367Boundary =
  round367-boundary true refl true refl true refl true refl

round367FrontierRefinementLevel : ProofLevel
round367FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
