module DASHI.Physics.YangMills.BalabanCMP116OneStepMapDefectRound366Exact where

------------------------------------------------------------------------
-- ROUND366 / THE CMP116 PARAMETER DEFECT FACTORS BEFORE FIXED-POINT ABSORPTION
--
-- CMP116 Part II, Sect. 1 writes the first nonlinear substituted-background
-- fixed-point equation in the source form
--
--   D(A') = C(A' - H D(A')).
--
-- Hence, at one COMMON candidate X and two decoupling/domain choices H_L,H_R,
-- the parameter defect is controlled in the order
--
--   ||F_L(X)-F_R(X)||
--     <= L_C ||(A'-H_L X)-(A'-H_R X)||
--     <= L_C ||(H_L-H_R)X||
--     <= L_C M_H ||X||
--     <= L_C M_H R.
--
-- R365 then absorbs the contraction and turns this one-step defect into the
-- two-fixed-point substituted-background displacement consumed by R364.
--
-- This file proves only the scalar composition.  It deliberately does NOT
-- identify an older repository nonlinear map with the literal source C, nor an
-- older Green operator with the literal decoupled H(s(Y0)).  Those are
-- same-object payments, not consequences of shared names.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; ≤ℝ-trans ; mulMonotoneNonnegative ; *-assoc )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116SubstitutionContractionRound365Exact as R365
import DASHI.Physics.YangMills.BalabanMarkedHessianPublishedDecayBoundaryExact as Marked
import DASHI.Physics.YangMills.BalabanNonlinearComponentLipschitz as NonlinearDonor
import DASHI.Physics.YangMills.BalabanReferenceGreenPerturbation as GreenDonor

------------------------------------------------------------------------
-- Least-privilege scalar composition.
------------------------------------------------------------------------

record CMP116OneStepMapDefectFactors : Set where
  field
    mapDefect : ℝ
    argumentDefect : ℝ
    propagatorActionDefect : ℝ

    nonlinearLipschitz : ℝ
    propagatorDifference : ℝ
    candidateSize : ℝ
    candidateRadius : ℝ

    mapDefectNonnegative : 0ℝ ≤ℝ mapDefect
    argumentDefectNonnegative : 0ℝ ≤ℝ argumentDefect
    propagatorActionDefectNonnegative : 0ℝ ≤ℝ propagatorActionDefect
    nonlinearLipschitzNonnegative : 0ℝ ≤ℝ nonlinearLipschitz
    propagatorDifferenceNonnegative : 0ℝ ≤ℝ propagatorDifference
    candidateSizeNonnegative : 0ℝ ≤ℝ candidateSize
    candidateRadiusNonnegative : 0ℝ ≤ℝ candidateRadius

    -- Literal C-Lipschitz payment on the same CMP116 critical-map carrier.
    mapDefectBelowLipschitzArgument :
      mapDefect ≤ℝ nonlinearLipschitz *ℝ argumentDefect

    -- Algebra/same-object attachment of the two C arguments to the H defect.
    argumentDefectBelowPropagatorAction :
      argumentDefect ≤ℝ propagatorActionDefect

    -- Operator comparison for the literal H_L-H_R acting on the common X.
    propagatorActionDefectBelowDifferenceTimesCandidate :
      propagatorActionDefect ≤ℝ propagatorDifference *ℝ candidateSize

    -- Common invariant-ball radius from the CMP116 contraction construction.
    candidateSizeBelowRadius : candidateSize ≤ℝ candidateRadius

open CMP116OneStepMapDefectFactors public

argumentDefectBelowDifferenceTimesCandidate :
  (dataSet : CMP116OneStepMapDefectFactors) →
  argumentDefect dataSet
    ≤ℝ propagatorDifference dataSet *ℝ candidateSize dataSet
argumentDefectBelowDifferenceTimesCandidate dataSet =
  ≤ℝ-trans
    (argumentDefectBelowPropagatorAction dataSet)
    (propagatorActionDefectBelowDifferenceTimesCandidate dataSet)

propagatorActionDefectBelowDifferenceTimesRadius :
  (dataSet : CMP116OneStepMapDefectFactors) →
  propagatorActionDefect dataSet
    ≤ℝ propagatorDifference dataSet *ℝ candidateRadius dataSet
propagatorActionDefectBelowDifferenceTimesRadius dataSet =
  ≤ℝ-trans
    (propagatorActionDefectBelowDifferenceTimesCandidate dataSet)
    (mulMonotoneNonnegative
      {a = propagatorDifference dataSet}
      {b = propagatorDifference dataSet}
      {c = candidateSize dataSet}
      {d = candidateRadius dataSet}
      (propagatorDifferenceNonnegative dataSet)
      ≤ℝ-refl
      (candidateSizeNonnegative dataSet)
      (candidateSizeBelowRadius dataSet))

mapDefectBelowSourceProduct :
  (dataSet : CMP116OneStepMapDefectFactors) →
  mapDefect dataSet
    ≤ℝ
  nonlinearLipschitz dataSet *ℝ
    (propagatorDifference dataSet *ℝ candidateRadius dataSet)
mapDefectBelowSourceProduct dataSet =
  ≤ℝ-trans
    (mapDefectBelowLipschitzArgument dataSet)
    (mulMonotoneNonnegative
      {a = nonlinearLipschitz dataSet}
      {b = nonlinearLipschitz dataSet}
      {c = argumentDefect dataSet}
      {d = propagatorDifference dataSet *ℝ candidateRadius dataSet}
      (nonlinearLipschitzNonnegative dataSet)
      ≤ℝ-refl
      (argumentDefectNonnegative dataSet)
      (≤ℝ-trans
        (argumentDefectBelowPropagatorAction dataSet)
        (propagatorActionDefectBelowDifferenceTimesRadius dataSet)))

mapDefectBelowAssociatedSourceProduct :
  (dataSet : CMP116OneStepMapDefectFactors) →
  mapDefect dataSet
    ≤ℝ
  (nonlinearLipschitz dataSet *ℝ propagatorDifference dataSet)
    *ℝ candidateRadius dataSet
mapDefectBelowAssociatedSourceProduct dataSet =
  subst
    (λ upper → mapDefect dataSet ≤ℝ upper)
    (sym (*-assoc
      (nonlinearLipschitz dataSet)
      (propagatorDifference dataSet)
      (candidateRadius dataSet)))
    (mapDefectBelowSourceProduct dataSet)

------------------------------------------------------------------------
-- Pareto / source-boundary accounting.
------------------------------------------------------------------------

-- The source equation makes the factorization meaningful, but these four
-- coordinates still have to be attached to that exact source object:
--
--   1. C-Lipschitz on the declared CMP116 ball;
--   2. H_L-H_R marked operator comparison;
--   3. common-candidate radius;
--   4. exact map/argument/operator identities.
--
-- CMP99 is a valid donor for (2), but not by itself an inhabitant of (2) on the
-- selected R365 carrier.

cmp99MarkedPropagatorDifferenceAuthorityLevel : ProofLevel
cmp99MarkedPropagatorDifferenceAuthorityLevel =
  Marked.cmp99BackgroundPropagatorMarkedDifferenceLevel

olderNonlinearLipschitzDonorLevel : ProofLevel
olderNonlinearLipschitzDonorLevel =
  NonlinearDonor.nonlinearComponentAssemblyLevel

olderGreenCompositionDonorLevel : ProofLevel
olderGreenCompositionDonorLevel =
  GreenDonor.referenceGreenPerturbationBridgeLevel

literalCMP116CLipschitzAttachmentLevel : ProofLevel
literalCMP116CLipschitzAttachmentLevel = conditional

literalCMP116PropagatorDifferenceAttachmentLevel : ProofLevel
literalCMP116PropagatorDifferenceAttachmentLevel = conditional

literalCMP116CommonCandidateRadiusAttachmentLevel : ProofLevel
literalCMP116CommonCandidateRadiusAttachmentLevel = conditional

literalCMP116CriticalMapArgumentIdentityLevel : ProofLevel
literalCMP116CriticalMapArgumentIdentityLevel = conditional

oneStepMapDefectScalarCompilerLevel : ProofLevel
oneStepMapDefectScalarCompilerLevel = machineChecked

cmp99DirectlyPaysFullFixedPointDisplacement : Bool
cmp99DirectlyPaysFullFixedPointDisplacement = false

cmp99DirectlyPaysFullFixedPointDisplacementIsFalse :
  cmp99DirectlyPaysFullFixedPointDisplacement ≡ false
cmp99DirectlyPaysFullFixedPointDisplacementIsFalse = refl

cmp99CanFeedOneStepMapDefectAfterSameObjectAttachment : Bool
cmp99CanFeedOneStepMapDefectAfterSameObjectAttachment = true

cmp99CanFeedOneStepMapDefectAfterSameObjectAttachmentIsTrue :
  cmp99CanFeedOneStepMapDefectAfterSameObjectAttachment ≡ true
cmp99CanFeedOneStepMapDefectAfterSameObjectAttachmentIsTrue = refl

hSubScalePrimitiveAfterRound366 : Bool
hSubScalePrimitiveAfterRound366 = false

hSubScalePrimitiveAfterRound366IsFalse :
  hSubScalePrimitiveAfterRound366 ≡ false
hSubScalePrimitiveAfterRound366IsFalse = refl

record Round366Boundary : Set where
  constructor round366-boundary
  field
    criticalMapEquationDrivesFactorization : Bool
    criticalMapEquationDrivesFactorizationIsTrue :
      criticalMapEquationDrivesFactorization ≡ true

    propagatorDifferenceIsUpstreamNotFixedPointDifference : Bool
    propagatorDifferenceIsUpstreamNotFixedPointDifferenceIsTrue :
      propagatorDifferenceIsUpstreamNotFixedPointDifference ≡ true

    sourceSameObjectAttachmentsStillRequired : Bool
    sourceSameObjectAttachmentsStillRequiredIsTrue :
      sourceSameObjectAttachmentsStillRequired ≡ true

    r365ContractionAbsorptionStillDownstream : Bool
    r365ContractionAbsorptionStillDownstreamIsTrue :
      r365ContractionAbsorptionStillDownstream ≡ true

canonicalRound366Boundary : Round366Boundary
canonicalRound366Boundary =
  round366-boundary true refl true refl true refl true refl

round366FrontierRefinementLevel : ProofLevel
round366FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
