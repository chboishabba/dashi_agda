{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116MinimalFixedPointDistanceRound384Exact where

------------------------------------------------------------------------
-- ROUND384 / FIXED-POINT DISTANCE PRODUCER WITHOUT AN H_LOCAL SOCKET
--
-- R370 correctly owns the Cauchy/mean-value compiler for the CMP116 parametric
-- fixed point, but its compatibility record still contains the historical
-- `boundaryHessianStable` field because it compiles all the way to R364.
--
-- That field is not observed by the fixed-point-distance consumer.  Requiring a
-- full R370 inhabitant before constructing the newer R372/R382 Hessian payment
-- can therefore create an artificial dependency cycle:
--
--   fixed-point sensitivity -> [old Hessian socket] -> Hessian sensitivity.
--
-- This module projects the direct source theorem to the least-privilege object:
--
--   selected parametric fixed-point family
--   + common source neighbourhood
--   + parameter-distance upper
--     -> selected boundary distance <= U_par.
--
-- No Hessian scalar, Hessian Lipschitz constant, left/right domain pair or field
-- variation is needed here.  Those belong to the downstream differentiated
-- consumer, not to this producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; subst)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanCMP116PublishedParametricFixedPointRound371Exact as R371

------------------------------------------------------------------------
-- Minimal application of the generic R370 Cauchy authority.
------------------------------------------------------------------------

record CMP116MinimalFixedPointDistanceData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData
    component : Decoupled.Component decoupled

    Boundary : Set
    boundaryIndex :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → Boundary

    Parameter Background : Set
    sensitivity : R370.CauchyParametricSensitivityAuthority Parameter Background

    fixedPointFamily : Boundary → Parameter → Background
    sourceMagnitudeBound sourceParameterRadius sourceParameterDistance : ℝ
    sourceParameterDistanceNonnegative : 0ℝ ≤ℝ sourceParameterDistance

    sourceFamilyAnalytic :
      ∀ boundary → R370.AnalyticFamily sensitivity (fixedPointFamily boundary)

    sourceFamilyUniformlyBounded :
      ∀ boundary →
      R370.UniformMagnitudeBound sensitivity
        (fixedPointFamily boundary) sourceMagnitudeBound

    sourceParameterRadiusPositive :
      R370.PositiveRadiusMargin sensitivity sourceParameterRadius

    leftParameter rightParameter : Boundary → Parameter

    selectedParametersShareNeighbourhood :
      ∀ boundary →
      R370.CommonNeighbourhood sensitivity
        (leftParameter boundary) (rightParameter boundary)

    selectedParameterDistanceBelowSourceDistance :
      ∀ boundary →
      R370.parameterDistance sensitivity
        (leftParameter boundary) (rightParameter boundary)
      ≤ℝ sourceParameterDistance

    boundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    boundarySubstitutionDistanceIsParametricFixedPointDistance :
      ∀ s →
      boundarySubstitutionDistance s ≡
      R370.backgroundDistance sensitivity
        (fixedPointFamily (boundaryIndex s)
          (leftParameter (boundaryIndex s)))
        (fixedPointFamily (boundaryIndex s)
          (rightParameter (boundaryIndex s)))

open CMP116MinimalFixedPointDistanceData public

parametricLipschitz : CMP116MinimalFixedPointDistanceData → ℝ
parametricLipschitz dataSet =
  R370.lipschitzConstant (sensitivity dataSet)
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)

distanceUpper : CMP116MinimalFixedPointDistanceData → ℝ
distanceUpper dataSet =
  parametricLipschitz dataSet *ℝ sourceParameterDistance dataSet

boundaryDistanceNonnegative :
  (dataSet : CMP116MinimalFixedPointDistanceData) →
  ∀ s → 0ℝ ≤ℝ boundarySubstitutionDistance dataSet s
boundaryDistanceNonnegative dataSet s
  rewrite boundarySubstitutionDistanceIsParametricFixedPointDistance dataSet s =
  R370.backgroundDistanceNonnegative (sensitivity dataSet)
    (fixedPointFamily dataSet (boundaryIndex dataSet s)
      (leftParameter dataSet (boundaryIndex dataSet s)))
    (fixedPointFamily dataSet (boundaryIndex dataSet s)
      (rightParameter dataSet (boundaryIndex dataSet s)))

distanceUpperNonnegative :
  (dataSet : CMP116MinimalFixedPointDistanceData) →
  0ℝ ≤ℝ distanceUpper dataSet
distanceUpperNonnegative dataSet =
  R370.lipschitzTimesUpperNonnegative (sensitivity dataSet)
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)
    (sourceParameterDistance dataSet)
    (sourceParameterRadiusPositive dataSet)
    (sourceParameterDistanceNonnegative dataSet)

boundaryDistanceBelowUpper :
  (dataSet : CMP116MinimalFixedPointDistanceData) →
  ∀ s → boundarySubstitutionDistance dataSet s ≤ℝ distanceUpper dataSet
boundaryDistanceBelowUpper dataSet s
  rewrite boundarySubstitutionDistanceIsParametricFixedPointDistance dataSet s =
  R370.cauchySensitivityWithDistanceUpper (sensitivity dataSet)
    (fixedPointFamily dataSet (boundaryIndex dataSet s))
    (sourceMagnitudeBound dataSet)
    (sourceParameterRadius dataSet)
    (leftParameter dataSet (boundaryIndex dataSet s))
    (rightParameter dataSet (boundaryIndex dataSet s))
    (sourceParameterDistance dataSet)
    (sourceFamilyAnalytic dataSet (boundaryIndex dataSet s))
    (sourceFamilyUniformlyBounded dataSet (boundaryIndex dataSet s))
    (sourceParameterRadiusPositive dataSet)
    (selectedParametersShareNeighbourhood dataSet (boundaryIndex dataSet s))
    (selectedParameterDistanceBelowSourceDistance dataSet (boundaryIndex dataSet s))

------------------------------------------------------------------------
-- Compatibility projection from the older full R370 record.
------------------------------------------------------------------------

fromRound370 :
  R370.CMP116DirectParametricSensitivityData →
  CMP116MinimalFixedPointDistanceData
fromRound370 dataSet = record
  { decoupled = R370.decoupled dataSet
  ; component = R370.component dataSet
  ; Boundary = R370.Boundary dataSet
  ; boundaryIndex = R370.boundaryIndex dataSet
  ; Parameter = R370.Parameter dataSet
  ; Background = R370.Background dataSet
  ; sensitivity = R370.sensitivity dataSet
  ; fixedPointFamily = R370.fixedPointFamily dataSet
  ; sourceMagnitudeBound = R370.sourceMagnitudeBound dataSet
  ; sourceParameterRadius = R370.sourceParameterRadius dataSet
  ; sourceParameterDistance = R370.sourceParameterDistance dataSet
  ; sourceParameterDistanceNonnegative =
      R370.sourceParameterDistanceNonnegative dataSet
  ; sourceFamilyAnalytic = R370.sourceFamilyAnalytic dataSet
  ; sourceFamilyUniformlyBounded = R370.sourceFamilyUniformlyBounded dataSet
  ; sourceParameterRadiusPositive = R370.sourceParameterRadiusPositive dataSet
  ; leftParameter = R370.leftParameter dataSet
  ; rightParameter = R370.rightParameter dataSet
  ; selectedParametersShareNeighbourhood =
      R370.selectedParametersShareNeighbourhood dataSet
  ; selectedParameterDistanceBelowSourceDistance =
      R370.selectedParameterDistanceBelowSourceDistance dataSet
  ; boundarySubstitutionDistance = R370.boundarySubstitutionDistance dataSet
  ; boundarySubstitutionDistanceIsParametricFixedPointDistance =
      R370.boundarySubstitutionDistanceIsParametricFixedPointDistance dataSet
  }

------------------------------------------------------------------------
-- Source-native selected application from R371 WITHOUT boundaryHessianStable.
------------------------------------------------------------------------

record PublishedCMP116ToMinimalDistanceData : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData
    component : Decoupled.Component decoupled

    Boundary Parameter Background : Set
    sensitivity : R370.CauchyParametricSensitivityAuthority Parameter Background
    published :
      R371.PublishedCMP116ParametricFixedPoint
        Boundary Parameter Background sensitivity

    boundaryIndex :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → Boundary

    leftParameter rightParameter : Boundary → Parameter

    leftParameterInPublishedDomain :
      ∀ boundary →
      R371.InSourceParameterDomain published boundary (leftParameter boundary)

    rightParameterInPublishedDomain :
      ∀ boundary →
      R371.InSourceParameterDomain published boundary (rightParameter boundary)

    sourceParameterDistance : ℝ
    sourceParameterDistanceNonnegative : 0ℝ ≤ℝ sourceParameterDistance

    selectedParameterDistanceBelowSourceDistance :
      ∀ boundary →
      R370.parameterDistance sensitivity
        (leftParameter boundary) (rightParameter boundary)
      ≤ℝ sourceParameterDistance

    boundarySubstitutionDistance :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → ℝ

    boundarySubstitutionDistanceIsPublishedFixedPointDistance :
      ∀ s →
      boundarySubstitutionDistance s ≡
      R370.backgroundDistance sensitivity
        (R371.fixedPointFamily published (boundaryIndex s)
          (leftParameter (boundaryIndex s)))
        (R371.fixedPointFamily published (boundaryIndex s)
          (rightParameter (boundaryIndex s)))

open PublishedCMP116ToMinimalDistanceData public

publishedSelectedParametersShareNeighbourhood :
  (dataSet : PublishedCMP116ToMinimalDistanceData) →
  ∀ boundary →
  R370.CommonNeighbourhood (sensitivity dataSet)
    (leftParameter dataSet boundary) (rightParameter dataSet boundary)
publishedSelectedParametersShareNeighbourhood dataSet boundary =
  R371.sourceDomainGivesCommonNeighbourhood (published dataSet)
    boundary
    (leftParameter dataSet boundary)
    (rightParameter dataSet boundary)
    (leftParameterInPublishedDomain dataSet boundary)
    (rightParameterInPublishedDomain dataSet boundary)

publishedToMinimalDistance :
  PublishedCMP116ToMinimalDistanceData →
  CMP116MinimalFixedPointDistanceData
publishedToMinimalDistance dataSet = record
  { decoupled = decoupled dataSet
  ; component = component dataSet
  ; Boundary = Boundary dataSet
  ; boundaryIndex = boundaryIndex dataSet
  ; Parameter = Parameter dataSet
  ; Background = Background dataSet
  ; sensitivity = sensitivity dataSet
  ; fixedPointFamily = R371.fixedPointFamily (published dataSet)
  ; sourceMagnitudeBound = R371.sourceMagnitudeBound (published dataSet)
  ; sourceParameterRadius = R371.sourceParameterRadius (published dataSet)
  ; sourceParameterDistance = sourceParameterDistance dataSet
  ; sourceParameterDistanceNonnegative = sourceParameterDistanceNonnegative dataSet
  ; sourceFamilyAnalytic = R371.sourceFamilyAnalytic (published dataSet)
  ; sourceFamilyUniformlyBounded = R371.sourceFamilyUniformlyBounded (published dataSet)
  ; sourceParameterRadiusPositive = R371.sourceParameterRadiusPositive (published dataSet)
  ; leftParameter = leftParameter dataSet
  ; rightParameter = rightParameter dataSet
  ; selectedParametersShareNeighbourhood =
      publishedSelectedParametersShareNeighbourhood dataSet
  ; selectedParameterDistanceBelowSourceDistance =
      selectedParameterDistanceBelowSourceDistance dataSet
  ; boundarySubstitutionDistance = boundarySubstitutionDistance dataSet
  ; boundarySubstitutionDistanceIsParametricFixedPointDistance =
      boundarySubstitutionDistanceIsPublishedFixedPointDistance dataSet
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

round384MinimalDistanceCompilerLevel : ProofLevel
round384MinimalDistanceCompilerLevel = machineChecked

round370CompatibilityProjectionLevel : ProofLevel
round370CompatibilityProjectionLevel = machineChecked

publishedR371ToMinimalDistanceCompilerLevel : ProofLevel
publishedR371ToMinimalDistanceCompilerLevel = machineChecked

boundaryHessianStableRequiredForFixedPointDistance : Bool
boundaryHessianStableRequiredForFixedPointDistance = false

boundaryHessianStableRequiredForFixedPointDistanceIsFalse :
  boundaryHessianStableRequiredForFixedPointDistance ≡ false
boundaryHessianStableRequiredForFixedPointDistanceIsFalse = refl

leftRightPhysicalDomainsRequiredForFixedPointDistance : Bool
leftRightPhysicalDomainsRequiredForFixedPointDistance = false

leftRightPhysicalDomainsRequiredForFixedPointDistanceIsFalse :
  leftRightPhysicalDomainsRequiredForFixedPointDistance ≡ false
leftRightPhysicalDomainsRequiredForFixedPointDistanceIsFalse = refl

record Round384Boundary : Set where
  constructor round384-boundary
  field
    sourceFixedPointDistanceCanBePaidBeforeHessian : Bool
    sourceFixedPointDistanceCanBePaidBeforeHessianIsTrue :
      sourceFixedPointDistanceCanBePaidBeforeHessian ≡ true

    legacyR370HessianSocketIsCompatibilityOnly : Bool
    legacyR370HessianSocketIsCompatibilityOnlyIsTrue :
      legacyR370HessianSocketIsCompatibilityOnly ≡ true

    selectedSourceFamilyAndParameterCalibrationStillRequired : Bool
    selectedSourceFamilyAndParameterCalibrationStillRequiredIsTrue :
      selectedSourceFamilyAndParameterCalibrationStillRequired ≡ true

canonicalRound384Boundary : Round384Boundary
canonicalRound384Boundary =
  round384-boundary true refl true refl true refl

round384FrontierRefinementLevel : ProofLevel
round384FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
