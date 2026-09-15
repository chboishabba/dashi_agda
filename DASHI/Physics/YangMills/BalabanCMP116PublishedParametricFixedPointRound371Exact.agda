module DASHI.Physics.YangMills.BalabanCMP116PublishedParametricFixedPointRound371Exact where

------------------------------------------------------------------------
-- ROUND371 / CMP116 ALREADY OWNS THE PARAMETRIC FIXED-POINT THEOREM SHAPE
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Commun. Math. Phys. 116 (1988), 1--22.
-- DOI: 10.1007/BF01239022.
--
-- SOURCE LOCATOR
--
-- Sect. 1, around (1.11)--(1.15).  After introducing the complex decoupling
-- variables s(Y0), the source proves H(s(Y0))X analytic and uniformly bounded
-- on the declared parameter domain.  For the fixed-point equation
--
--   D(A') = C(A' - H(s(Y0)) D(A')),
--
-- the source then proves that the transformation preserves one small ball and
-- is contractive there, hence the fixed point is analytic in A' and s(Y0), with
-- the explicit source bound following (1.13), recorded at (1.14).
--
-- R370 already owns the standard Cauchy/mean-value compiler from such a
-- parametric analytic family to H_subScale.  This module therefore does NOT
-- replay R366--R369.  It packages the source theorem separately from the
-- application-specific same-object attachment to the selected R364/R370
-- boundary carrier.
--
-- Defining this ABI does not manufacture an inhabitant of the published source
-- theorem.  Source authority, source theorem payment, selected-family identity,
-- parameter calibration and exact-head kernel validation remain distinct.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; _≤ℝ_)
import DASHI.Foundations.FinitePolydiscCauchyAxioms as Cauchy
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanCMP116DirectParametricSensitivityRound370Exact as R370
import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian as Decoupled
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source

------------------------------------------------------------------------
-- Proof-bearing source theorem surface.
------------------------------------------------------------------------

record PublishedCMP116ParametricFixedPoint
    (Boundary Parameter Background : Set)
    (sensitivity :
      R370.CauchyParametricSensitivityAuthority Parameter Background)
    : Set₁ where
  field
    fixedPointFamily : Boundary → Parameter → Background

    sourceMagnitudeBound sourceParameterRadius : ℝ

    -- Source complex parameter domain for the fixed-point family.
    InSourceParameterDomain : Boundary → Parameter → Set

    sourceFamilyAnalytic :
      ∀ boundary →
      R370.AnalyticFamily sensitivity (fixedPointFamily boundary)

    sourceFamilyUniformlyBounded :
      ∀ boundary →
      R370.UniformMagnitudeBound sensitivity
        (fixedPointFamily boundary) sourceMagnitudeBound

    sourceParameterRadiusPositive :
      R370.PositiveRadiusMargin sensitivity sourceParameterRadius

    -- The source domain is one common complex neighbourhood.  Thus any two
    -- selected parameters attached inside it satisfy the common-neighbourhood
    -- premise consumed by the standard R370 Cauchy sensitivity authority.
    sourceDomainGivesCommonNeighbourhood :
      ∀ boundary left right →
      InSourceParameterDomain boundary left →
      InSourceParameterDomain boundary right →
      R370.CommonNeighbourhood sensitivity left right

open PublishedCMP116ParametricFixedPoint public

------------------------------------------------------------------------
-- Selected same-object attachment into R370.
------------------------------------------------------------------------

record CMP116PublishedParametricToR370Data : Set₁ where
  field
    decoupled : Decoupled.DecoupledActivityHessianData

    leftDomain rightDomain : Decoupled.DomainSequence decoupled
    component : Decoupled.Component decoupled
    leftVariation rightVariation : Decoupled.FieldVariation decoupled

    sourceLipschitz : ℝ
    sourceLipschitzNonnegative : 0ℝ ≤ℝ sourceLipschitz

    Boundary Parameter Background : Set
    sensitivity :
      R370.CauchyParametricSensitivityAuthority Parameter Background
    published :
      PublishedCMP116ParametricFixedPoint
        Boundary Parameter Background sensitivity

    boundaryIndex :
      Cauchy.BoundaryAssignment
        (Decoupled.cauchy decoupled)
        (Decoupled.componentIndices decoupled component) → Boundary

    leftParameter rightParameter : Boundary → Parameter

    leftParameterInPublishedDomain :
      ∀ boundary →
      InSourceParameterDomain published boundary (leftParameter boundary)

    rightParameterInPublishedDomain :
      ∀ boundary →
      InSourceParameterDomain published boundary (rightParameter boundary)

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

    -- Same-object weld: the selected substitution-distance consumer is the
    -- distance between the two values of the published CMP116 fixed-point
    -- family at the selected source parameters.
    boundarySubstitutionDistanceIsPublishedFixedPointDistance :
      ∀ s →
      boundarySubstitutionDistance s ≡
      R370.backgroundDistance sensitivity
        (fixedPointFamily published (boundaryIndex s)
          (leftParameter (boundaryIndex s)))
        (fixedPointFamily published (boundaryIndex s)
          (rightParameter (boundaryIndex s)))

    -- Orthogonal H_local payment.  R371 only removes overpayment on H_subScale.
    boundaryHessianStable :
      ∀ s →
      Cauchy.normValue (Decoupled.cauchy decoupled)
        (Cauchy._-Value_ (Decoupled.cauchy decoupled)
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled leftDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s))
          (Cauchy.evaluate (Decoupled.cauchy decoupled)
            (Decoupled.asFunction decoupled rightDomain component
              leftVariation rightVariation)
            (Cauchy.boundaryAssignment (Decoupled.cauchy decoupled) s)))
        ≤ℝ
      sourceLipschitz * R370._*ℝ_ (boundarySubstitutionDistance s)

open CMP116PublishedParametricToR370Data public

selectedParametersSharePublishedNeighbourhood :
  (dataSet : CMP116PublishedParametricToR370Data) →
  ∀ boundary →
  R370.CommonNeighbourhood (sensitivity dataSet)
    (leftParameter dataSet boundary) (rightParameter dataSet boundary)
selectedParametersSharePublishedNeighbourhood dataSet boundary =
  sourceDomainGivesCommonNeighbourhood (published dataSet)
    boundary
    (leftParameter dataSet boundary)
    (rightParameter dataSet boundary)
    (leftParameterInPublishedDomain dataSet boundary)
    (rightParameterInPublishedDomain dataSet boundary)

round371ToR370 :
  CMP116PublishedParametricToR370Data →
  R370.CMP116DirectParametricSensitivityData
round371ToR370 dataSet = record
  { R370.decoupled = decoupled dataSet
  ; R370.leftDomain = leftDomain dataSet
  ; R370.rightDomain = rightDomain dataSet
  ; R370.component = component dataSet
  ; R370.leftVariation = leftVariation dataSet
  ; R370.rightVariation = rightVariation dataSet
  ; R370.sourceLipschitz = sourceLipschitz dataSet
  ; R370.sourceLipschitzNonnegative = sourceLipschitzNonnegative dataSet
  ; R370.Boundary = Boundary dataSet
  ; R370.boundaryIndex = boundaryIndex dataSet
  ; R370.Parameter = Parameter dataSet
  ; R370.Background = Background dataSet
  ; R370.sensitivity = sensitivity dataSet
  ; R370.fixedPointFamily = fixedPointFamily (published dataSet)
  ; R370.sourceMagnitudeBound = sourceMagnitudeBound (published dataSet)
  ; R370.sourceParameterRadius = sourceParameterRadius (published dataSet)
  ; R370.sourceParameterDistance = sourceParameterDistance dataSet
  ; R370.sourceParameterDistanceNonnegative =
      sourceParameterDistanceNonnegative dataSet
  ; R370.sourceFamilyAnalytic = sourceFamilyAnalytic (published dataSet)
  ; R370.sourceFamilyUniformlyBounded =
      sourceFamilyUniformlyBounded (published dataSet)
  ; R370.sourceParameterRadiusPositive =
      sourceParameterRadiusPositive (published dataSet)
  ; R370.leftParameter = leftParameter dataSet
  ; R370.rightParameter = rightParameter dataSet
  ; R370.selectedParametersShareNeighbourhood =
      selectedParametersSharePublishedNeighbourhood dataSet
  ; R370.selectedParameterDistanceBelowSourceDistance =
      selectedParameterDistanceBelowSourceDistance dataSet
  ; R370.boundarySubstitutionDistance = boundarySubstitutionDistance dataSet
  ; R370.boundarySubstitutionDistanceIsParametricFixedPointDistance =
      boundarySubstitutionDistanceIsPublishedFixedPointDistance dataSet
  ; R370.boundaryHessianStable = boundaryHessianStable dataSet
  }

------------------------------------------------------------------------
-- Pareto / authority boundary.
------------------------------------------------------------------------

cmp116PublishedFixedPointAnalyticityLevel : ProofLevel
cmp116PublishedFixedPointAnalyticityLevel = standardImported

cmp116PublishedUniformFixedPointBoundLevel : ProofLevel
cmp116PublishedUniformFixedPointBoundLevel = standardImported

cmp116DifferentiatedLocalizationSourceLevel : ProofLevel
cmp116DifferentiatedLocalizationSourceLevel =
  Source.cmp116DifferentiatedActivityLocalizationLevel

literalPublishedFixedPointFamilyAttachmentLevel : ProofLevel
literalPublishedFixedPointFamilyAttachmentLevel = conditional

literalSelectedParameterDomainAttachmentLevel : ProofLevel
literalSelectedParameterDomainAttachmentLevel = conditional

literalSelectedParameterDistanceCalibrationLevel : ProofLevel
literalSelectedParameterDistanceCalibrationLevel = conditional

literalBoundarySubstitutionDistanceAttachmentLevel : ProofLevel
literalBoundarySubstitutionDistanceAttachmentLevel = conditional

round371ToR370CompilerLevel : ProofLevel
round371ToR370CompilerLevel = machineChecked

r366R369CrossParameterDefectRouteMandatoryAfterRound371 : Bool
r366R369CrossParameterDefectRouteMandatoryAfterRound371 = false

r366R369CrossParameterDefectRouteMandatoryAfterRound371IsFalse :
  r366R369CrossParameterDefectRouteMandatoryAfterRound371 ≡ false
r366R369CrossParameterDefectRouteMandatoryAfterRound371IsFalse = refl

oneSidedCrossMembershipMandatoryAfterRound371 : Bool
oneSidedCrossMembershipMandatoryAfterRound371 = false

oneSidedCrossMembershipMandatoryAfterRound371IsFalse :
  oneSidedCrossMembershipMandatoryAfterRound371 ≡ false
oneSidedCrossMembershipMandatoryAfterRound371IsFalse = refl

publishedAnalyticityAutomaticallyIdentifiesSelectedFamily : Bool
publishedAnalyticityAutomaticallyIdentifiesSelectedFamily = false

publishedAnalyticityAutomaticallyIdentifiesSelectedFamilyIsFalse :
  publishedAnalyticityAutomaticallyIdentifiesSelectedFamily ≡ false
publishedAnalyticityAutomaticallyIdentifiesSelectedFamilyIsFalse = refl

record Round371Boundary : Set where
  constructor round371-boundary
  field
    sourceParametricTheoremCanFeedDirectR370 : Bool
    sourceParametricTheoremCanFeedDirectR370IsTrue :
      sourceParametricTheoremCanFeedDirectR370 ≡ true

    propagatorDefectRouteIsOptional : Bool
    propagatorDefectRouteIsOptionalIsTrue :
      propagatorDefectRouteIsOptional ≡ true

    selectedSameObjectAttachmentStillRequired : Bool
    selectedSameObjectAttachmentStillRequiredIsTrue :
      selectedSameObjectAttachmentStillRequired ≡ true

    parameterCalibrationStillRequired : Bool
    parameterCalibrationStillRequiredIsTrue :
      parameterCalibrationStillRequired ≡ true

canonicalRound371Boundary : Round371Boundary
canonicalRound371Boundary =
  round371-boundary true refl true refl true refl true refl

round371FrontierRefinementLevel : ProofLevel
round371FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
