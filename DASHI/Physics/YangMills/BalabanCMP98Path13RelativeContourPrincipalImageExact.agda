{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Path13RelativeContourPrincipalImageExact where

------------------------------------------------------------------------
-- PATH13 EQ. (119): LITERAL RELATIVE CONTOUR -> SELECTED PRINCIPAL IMAGE
--
-- The typed RationalUnitQuaternion realization remains the path/group
-- authority.  Paths are erased only after exact multiplication to the raw
-- rational-quaternion carrier consumed by the selected principal chart.
--
-- One global selected-cut/defect weld replaces pointwise principal-image
-- receipts.  The existing finite geometry gives the exact 74-link budget:
--
--   24 + 13 + 24 + 13 = 74,
--   74 / 2048 = 37 / 1024 < 1 / 24.
--
-- The selected cut then turns the resulting defect bound into principal-image
-- admission on the literal erased relative contour.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (_++_)
open import Data.Nat.Base using (_≤_; _+_; s≤s)
import Data.Nat.Properties as ℕP
open import Data.Rational.Base as ℚ using (ℚ; _*_; _+_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier
import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact as Word
import DASHI.Physics.YangMills.BalabanPath13BackgroundGaugeAdjointDefectExact as Background
import DASHI.Physics.YangMills.BalabanPath13SelectedPhysicalBackgroundTargetExact as PathTarget
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanClayGate4PrimaryQkFiniteKernelBudgetExact as Scale
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogPathBoundExact as Path
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanCMP98UnitaryOperatorDefectTelescopeExact as Telescope
import DASHI.Physics.YangMills.BalabanCMP98MinimalContourSourceChartBudgetExact as Budget
import DASHI.Physics.YangMills.BalabanCMP98SelectedSourceChartFromDefectExact as Chart
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralRelativeDefectRound164Exact as R164
import DASHI.Physics.YangMills.BalabanCMP98Equation119RelativeContourYRound155Exact as R155
import DASHI.Physics.YangMills.BalabanCMP98CanonicalContourLength24Round172Exact as R172
import DASHI.Physics.YangMills.BalabanCMP98Path13PhysicalPeriodicRealizationRound192Exact as R192
import DASHI.Physics.YangMills.BalabanCMP98Path13TwoCarrierSourceFamilyExact as Family
import DASHI.Physics.YangMills.BalabanCMP98Path13ReducedFamilyGeometryExact as Reduced
import DASHI.Physics.YangMills.BalabanCMP98Equation119GeometryRelativeContourExact as Geometry
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierErasureBridgeExact as Erasure
import DASHI.Physics.YangMills.BalabanCMP98SelectedPhysicalUnitCarrierRound187Exact as R187
import DASHI.Physics.YangMills.BalabanCMP109QuaternionPathTransportTelescopeExact as RawPath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicPathInverseBianchiExact as InversePath
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicCoordinateClosureExact as Closure
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2ExactGroupLaws as Group
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embed
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanTranslatedCenteredEmbeddingRound163Exact as R163
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanP33CMP109MinimalPathStageBudgetExact as PathBudget
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Quaternion
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as Lie

record Path13SelectedCutDefectWeld
    {CoarseField : Set}
    (selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra) : Set₁ where
  field
    kernel : Telescope.UnitaryOperatorDefectKernel Q.RationalQuaternion

    kernelIdentityIsQuaternionIdentity :
      Telescope.identity kernel ≡ Q.oneQ

    kernelMultiplyIsQuaternionMultiply : ∀ left right →
      Telescope.multiply kernel left right ≡ left Q.*q right

    kernelDefectConjugateInvariant : ∀ value →
      Telescope.defect kernel (Quaternion.quaternionConjugate value)
      ≡ Telescope.defect kernel value

    kernelDefectIsSelectedDefect : ∀ value →
      Telescope.defect kernel value
      ≡ Path.defect
          (Selected.defectAlgebra (PathTarget.bridge13 selected)) value

    chartOrderIsRationalOrder :
      Scale.LessEqual
        (Path.scale (Selected.defectAlgebra (PathTarget.bridge13 selected)))
      ≡ _≤_

    publishedUpperBelowPerLinkMajorant :
      Selected.sourceFineBondUpper
        (Selected.variational (PathTarget.bridge13 selected))
      ≤ Budget.perLinkDefectMajorant

    sourceThresholdBelowSelectedCut :
      Chart.sourceDefectThreshold
      ≤ Path.chartRadius
          (Selected.cutData (PathTarget.bridge13 selected))

open Path13SelectedCutDefectWeld public

selectedBackground :
  ∀ {CoarseField}
    (selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra) →
  Background.RationalSU2Background13
selectedBackground = PathTarget.path13Background

selectedGroupDefectBelowPublishedUpper :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    bond →
  Path.defect (Selected.defectAlgebra (PathTarget.bridge13 selected))
    (Selected.selectedBondGroup
      (PathTarget.bridge13 selected)
      (PathTarget.coarse13 selected)
      (PathTarget.small13 selected)
      bond)
  ≤ Selected.sourceFineBondUpper
      (Selected.variational (PathTarget.bridge13 selected))
selectedGroupDefectBelowPublishedUpper {selected = selected} weld bond =
  let
    bridge = PathTarget.bridge13 selected
    theorem = Selected.variational bridge
    coarse = PathTarget.coarse13 selected
    small = PathTarget.small13 selected
    upper = Selected.sourceFineBondUpper theorem
    deviation =
      Variational.bondDeviation theorem
        (Variational.bondValue theorem
          (Variational.background theorem coarse small) bond)
        (Variational.identityBondValue theorem)

    sourceBound : Variational.LessEqual theorem deviation upper
    sourceBound = Variational.fineBondSmallness theorem coarse small bond

    chartOrderBound :
      Scale.LessEqual (Path.scale (Selected.defectAlgebra bridge))
        deviation upper
    chartOrderBound =
      subst
        (λ relation → relation deviation upper)
        (Selected.variationalOrderIsChartOrder bridge)
        sourceBound

    rationalBound : deviation ≤ upper
    rationalBound =
      subst
        (λ relation → relation deviation upper)
        (chartOrderIsRationalOrder weld)
        chartOrderBound
  in
  subst
    (λ lower → lower ≤ upper)
    (sym (Selected.defectMatchesPublishedBondDeviation
      bridge coarse small bond))
    rationalBound

path13PositiveLinkKernelDefectSmall :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    site axis →
  Telescope.defect (kernel weld)
    (Background.link (selectedBackground selected) axis site)
  ≤ Budget.perLinkDefectMajorant
path13PositiveLinkKernelDefectSmall {selected = selected} weld site axis =
  let
    bridge = PathTarget.bridge13 selected
    selectedValue = Selected.selectedBondGroup bridge
      (PathTarget.coarse13 selected) (PathTarget.small13 selected)
      (Carrier.pair site axis)

    selectedKernelBound :
      Telescope.defect (kernel weld) selectedValue
      ≤ Selected.sourceFineBondUpper (Selected.variational bridge)
    selectedKernelBound =
      subst
        (λ lower → lower
          ≤ Selected.sourceFineBondUpper (Selected.variational bridge))
        (sym (kernelDefectIsSelectedDefect weld selectedValue))
        (selectedGroupDefectBelowPublishedUpper weld (Carrier.pair site axis))

    selectedFinal :
      Telescope.defect (kernel weld) selectedValue
      ≤ Budget.perLinkDefectMajorant
    selectedFinal =
      ℚP.≤-trans selectedKernelBound
        (publishedUpperBelowPerLinkMajorant weld)
  in
  subst
    (λ value → Telescope.defect (kernel weld) value
      ≤ Budget.perLinkDefectMajorant)
    (PathTarget.selectedBondGroupIsPath13Link selected site axis)
    selectedFinal

rawOrientedFactorDefectSmall :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    site direction →
  Telescope.defect (kernel weld)
    (R187.eraseUnitQuaternion
      (Bond.orientedLink
        (R192.path13PhysicalPeriodicRealization (selectedBackground selected))
        site direction))
  ≤ Budget.perLinkDefectMajorant
rawOrientedFactorDefectSmall {selected = selected} weld site
    (Carrier.pair axis true) =
  subst
    (λ value → Telescope.defect (kernel weld) value
      ≤ Budget.perLinkDefectMajorant)
    (sym
      (trans
        (Erasure.eraseOrientedLinkPositive
          (R192.path13PhysicalPeriodicRealization (selectedBackground selected))
          site axis)
        (R192.path13RealizationErasesToPhysicalLink
          (selectedBackground selected) site axis)))
    (path13PositiveLinkKernelDefectSmall weld site axis)
rawOrientedFactorDefectSmall {selected = selected} weld site
    (Carrier.pair axis false) =
  let
    predecessor = Bond.negativeStep site axis
    positive = Background.link (selectedBackground selected) axis predecessor

    erasedNegativeIsConjugate :
      R187.eraseUnitQuaternion
        (Bond.orientedLink
          (R192.path13PhysicalPeriodicRealization (selectedBackground selected))
          site (Carrier.pair axis false))
      ≡ Quaternion.quaternionConjugate positive
    erasedNegativeIsConjugate =
      trans
        (Erasure.eraseOrientedLinkNegative
          (R192.path13PhysicalPeriodicRealization (selectedBackground selected))
          site axis)
        (cong Quaternion.quaternionConjugate
          (R192.path13RealizationErasesToPhysicalLink
            (selectedBackground selected) predecessor axis))

    conjugateBound :
      Telescope.defect (kernel weld) (Quaternion.quaternionConjugate positive)
      ≤ Budget.perLinkDefectMajorant
    conjugateBound =
      subst
        (λ lower → lower ≤ Budget.perLinkDefectMajorant)
        (kernelDefectConjugateInvariant weld positive)
        (path13PositiveLinkKernelDefectSmall weld predecessor axis)
  in
  subst
    (λ value → Telescope.defect (kernel weld) value
      ≤ Budget.perLinkDefectMajorant)
    (sym erasedNegativeIsConjugate)
    conjugateBound

rawPathDefectBelowLengthBudget :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    site word bound →
  R164.listLength word ≤ bound →
  Telescope.defect (kernel weld)
    (RawPath.pathProduct
      (Erasure.rawPathFactors
        (R192.path13PhysicalPeriodicRealization (selectedBackground selected))
        site word))
  ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant
rawPathDefectBelowLengthBudget {selected = selected} weld site [] bound lengthBound =
  subst
    (λ selectedValue →
      Telescope.defect (kernel weld) selectedValue
      ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    (sym (kernelIdentityIsQuaternionIdentity weld))
    (subst
      (λ lower → lower
        ≤ Sums.natAsRational bound * Budget.perLinkDefectMajorant)
      (sym (Telescope.identityDefectZero (kernel weld)))
      (PathBudget.productNonnegative
        (Sums.natAsRational bound)
        Budget.perLinkDefectMajorant
        (PathBudget.natAsRationalNonnegative bound)
        Budget.perLinkDefectMajorantNonnegative))
rawPathDefectBelowLengthBudget weld site (_ ∷ _) zero ()
rawPathDefectBelowLengthBudget {selected = selected} weld site
    (direction ∷ directions) (suc bound) (s≤s tailLength) =
  let
    realization = R192.path13PhysicalPeriodicRealization (selectedBackground selected)
    head = R187.eraseUnitQuaternion (Bond.orientedLink realization site direction)
    tail = RawPath.pathProduct
      (Erasure.rawPathFactors realization (Bond.walkStep site direction) directions)

    productBound :
      Telescope.defect (kernel weld)
        (Telescope.multiply (kernel weld) head tail)
      ≤ Telescope.defect (kernel weld) head
        + Telescope.defect (kernel weld) tail
    productBound = Telescope.productDefectTriangle (kernel weld) head tail

    headTailBound :
      Telescope.defect (kernel weld) head
        + Telescope.defect (kernel weld) tail
      ≤ Budget.perLinkDefectMajorant
        + (Sums.natAsRational bound * Budget.perLinkDefectMajorant)
    headTailBound = ℚP.+-mono-≤
      (rawOrientedFactorDefectSmall weld site direction)
      (rawPathDefectBelowLengthBudget
        weld (Bond.walkStep site direction)
        directions bound tailLength)

    successorBound :
      Telescope.defect (kernel weld)
        (Telescope.multiply (kernel weld) head tail)
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant
    successorBound =
      subst
        (λ upper →
          Telescope.defect (kernel weld)
            (Telescope.multiply (kernel weld) head tail)
          ≤ upper)
        (PathBudget.successorBudgetExact bound Budget.perLinkDefectMajorant)
        (ℚP.≤-trans productBound headTailBound)
  in
  subst
    (λ selectedValue →
      Telescope.defect (kernel weld) selectedValue
      ≤ Sums.natAsRational (suc bound) * Budget.perLinkDefectMajorant)
    (kernelMultiplyIsQuaternionMultiply weld head tail)
    successorBound

path13CoarseWordLengthIs13 :
  ∀ bond →
  R164.listLength (Periodic.segmentWord (Family.coarseSegmentFor bond)) ≡ 13
path13CoarseWordLengthIs13 bond =
  trans
    (Periodic.segmentWordLength (Family.coarseSegmentFor bond))
    refl

path13LiteralGammaLengthAtMost61 :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    bond step point →
  R164.listLength
    (Geometry.literalGammaWord
      (Family.geometrySourceAt
        (Reduced.asPath13FamilyGeometry reduced) bond)
      step point)
  ≤ 61
path13LiteralGammaLengthAtMost61 reduced bond step point =
  let
    contour = Embed.canonicalCenteredContourWord point
    coarse = Periodic.segmentWord (Family.coarseSegmentFor bond)
    contourBound = R172.canonicalContourLengthAtMost24 point

    reverseBound : R164.listLength (R155.reverseWord contour) ≤ 24
    reverseBound = subst
      (λ selectedLength → selectedLength ≤ 24)
      (sym (R164.reverseWordLength contour))
      contourBound

    coarseBound : R164.listLength coarse ≤ 13
    coarseBound = subst
      (λ selectedLength → selectedLength ≤ 13)
      (sym (path13CoarseWordLengthIs13 bond))
      ℕP.≤-refl

    sumBound :
      R164.listLength contour
      + (R164.listLength coarse + R164.listLength (R155.reverseWord contour))
      ≤ 24 + (13 + 24)
    sumBound = ℕP.+-mono-≤ contourBound
      (ℕP.+-mono-≤ coarseBound reverseBound)
  in
  subst
    (λ selectedLength → selectedLength ≤ 61)
    (sym
      (trans
        (R164.appendLength contour (coarse ++ R155.reverseWord contour))
        (cong (λ n → R164.listLength contour + n)
          (R164.appendLength coarse (R155.reverseWord contour)))))
    sumBound

path13RelativeClosedWord :
  ∀ {CoarseField} →
  Reduced.ReducedPath13FamilyGeometry CoarseField →
  Family.Path13PositiveBond → Nat → Centered.CenteredBlockPoint4 6 →
  List Word.SignedAxis4
path13RelativeClosedWord reduced bond step point =
  Geometry.literalGammaWord
    (Family.geometrySourceAt (Reduced.asPath13FamilyGeometry reduced) bond)
    step point
  ++ R155.reverseWord (Periodic.segmentWord (Family.coarseSegmentFor bond))

path13RelativeClosedWordLengthAtMost74 :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    bond step point →
  R164.listLength (path13RelativeClosedWord reduced bond step point) ≤ 74
path13RelativeClosedWordLengthAtMost74 reduced bond step point =
  let
    gamma = Geometry.literalGammaWord
      (Family.geometrySourceAt (Reduced.asPath13FamilyGeometry reduced) bond)
      step point
    coarse = Periodic.segmentWord (Family.coarseSegmentFor bond)
    gammaBound = path13LiteralGammaLengthAtMost61 reduced bond step point

    reverseCoarseBound : R164.listLength (R155.reverseWord coarse) ≤ 13
    reverseCoarseBound = subst
      (λ selectedLength → selectedLength ≤ 13)
      (sym (R164.reverseWordLength coarse))
      (subst
        (λ selectedLength → selectedLength ≤ 13)
        (sym (path13CoarseWordLengthIs13 bond))
        ℕP.≤-refl)

    sumBound :
      R164.listLength gamma + R164.listLength (R155.reverseWord coarse)
      ≤ 61 + 13
    sumBound = ℕP.+-mono-≤ gammaBound reverseCoarseBound
  in
  subst
    (λ selectedLength → selectedLength ≤ 74)
    (sym (R164.appendLength gamma (R155.reverseWord coarse)))
    sumBound

path13LiteralGammaEndpointIsPlusCentre :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    bond step (point : Centered.CenteredBlockPoint4 6) →
  let geometry = Reduced.asPath13FamilyGeometry reduced
      source = Family.geometrySourceAt geometry bond
      minus = Geometry.minusEmbedding source step
      plus = R163.translatedEmbedding minus (Family.coarseSegmentFor bond)
  in
  Bond.walk (Embed.embeddingCentre minus)
    (Geometry.literalGammaWord source step point)
  ≡ Embed.embeddingCentre plus
path13LiteralGammaEndpointIsPlusCentre reduced bond step point =
  let
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    minus = Geometry.minusEmbedding source step
    plus = R163.translatedEmbedding minus (Family.coarseSegmentFor bond)
    contour = Embed.canonicalCenteredContourWord point
    coarse = Periodic.segmentWord (Family.coarseSegmentFor bond)

    afterMinusContour :
      Bond.walk (Embed.embeddingCentre minus) contour ≡ Embed.embed minus point
    afterMinusContour = sym (Embed.embedMeaning minus point)

    afterCoarse :
      Bond.walk (Embed.embed minus point) coarse ≡ Embed.embed plus point
    afterCoarse = sym
      (R163.translatedPointExact minus (Family.coarseSegmentFor bond) point)

    plusPointIsWalk :
      Embed.embed plus point
      ≡ Bond.walk (Embed.embeddingCentre plus) contour
    plusPointIsWalk = Embed.embedMeaning plus point

    returnToPlusCentre :
      Bond.walk (Embed.embed plus point) (R155.reverseWord contour)
      ≡ Embed.embeddingCentre plus
    returnToPlusCentre =
      trans
        (cong
          (λ start → Bond.walk start (R155.reverseWord contour))
          plusPointIsWalk)
        (InversePath.walkReverseOpposite
          (Closure.periodicStepInverseLaws R192.path13PeriodicIndex)
          (Embed.embeddingCentre plus)
          contour)
  in
  trans
    (Embed.walkAppend
      (Embed.embeddingCentre minus)
      contour
      (coarse ++ R155.reverseWord contour))
    (trans
      (cong
        (λ start → Bond.walk start (coarse ++ R155.reverseWord contour))
        afterMinusContour)
      (trans
        (Embed.walkAppend
          (Embed.embed minus point) coarse (R155.reverseWord contour))
        (trans
          (cong
            (λ start → Bond.walk start (R155.reverseWord contour))
            afterCoarse)
          returnToPlusCentre)))

path13ClosedPathHolonomyIsRelativeContour :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    bond step (point : Centered.CenteredBlockPoint4 6) →
  let geometry = Reduced.asPath13FamilyGeometry reduced
      source = Family.geometrySourceAt geometry bond
      minus = Geometry.minusEmbedding source step
  in
  Bond.pathHolonomy
    (Geometry.realization source step)
    (Embed.embeddingCentre minus)
    (path13RelativeClosedWord reduced bond step point)
  ≡ Geometry.relativeContourElement source step point
path13ClosedPathHolonomyIsRelativeContour reduced bond step point =
  let
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    realization = Geometry.realization source step
    minus = Geometry.minusEmbedding source step
    plus = R163.translatedEmbedding minus (Family.coarseSegmentFor bond)
    minusCentre = Embed.embeddingCentre minus
    plusCentre = Embed.embeddingCentre plus
    gamma = Geometry.literalGammaWord source step point
    coarse = Periodic.segmentWord (Family.coarseSegmentFor bond)

    appendHolonomy =
      InversePath.holonomyAppend realization minusCentre
        gamma (R155.reverseWord coarse)

    gammaEndpoint =
      path13LiteralGammaEndpointIsPlusCentre reduced bond step point

    reverseCoarseAtPlus :
      Bond.pathHolonomy realization plusCentre (R155.reverseWord coarse)
      ≡ Bond.inverse Group.rationalSU2ExactLinkGroup
          (Bond.pathHolonomy realization minusCentre coarse)
    reverseCoarseAtPlus =
      trans
        (cong
          (λ start → Bond.pathHolonomy realization start (R155.reverseWord coarse))
          (R163.translatedCentreExact minus (Family.coarseSegmentFor bond)))
        (InversePath.pathHolonomyReverseOpposite
          (Closure.periodicStepInverseLaws R192.path13PeriodicIndex)
          realization minusCentre coarse)

    transportedReverse :
      Bond.pathHolonomy realization
        (Bond.walk minusCentre gamma)
        (R155.reverseWord coarse)
      ≡ Bond.inverse Group.rationalSU2ExactLinkGroup
          (Bond.pathHolonomy realization minusCentre coarse)
    transportedReverse =
      trans
        (cong
          (λ start → Bond.pathHolonomy realization start (R155.reverseWord coarse))
          gammaEndpoint)
        reverseCoarseAtPlus
  in
  trans
    appendHolonomy
    (trans
      (cong
        (Bond.multiply Group.rationalSU2ExactLinkGroup
          (Bond.pathHolonomy realization minusCentre gamma))
        transportedReverse)
      refl)

rawClosedProductIsErasedRelativeContour :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    bond step point →
  let geometry = Reduced.asPath13FamilyGeometry reduced
      source = Family.geometrySourceAt geometry bond
      minus = Geometry.minusEmbedding source step
      background = Family.familyBackground geometry
  in
  RawPath.pathProduct
    (Erasure.rawPathFactors
      (R192.path13PhysicalPeriodicRealization background)
      (Embed.embeddingCentre minus)
      (path13RelativeClosedWord reduced bond step point))
  ≡ Family.erasedRelativeContour geometry bond step point
rawClosedProductIsErasedRelativeContour reduced bond step point =
  let
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    minus = Geometry.minusEmbedding source step
    background = Family.familyBackground geometry
    closed = path13RelativeClosedWord reduced bond step point
  in
  trans
    (sym
      (R192.path13PeriodicPathErasure
        background (Embed.embeddingCentre minus) closed))
    (cong R187.eraseUnitQuaternion
      (path13ClosedPathHolonomyIsRelativeContour reduced bond step point))

relativeContourDefectBelowSourceThreshold :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    (weld : Path13SelectedCutDefectWeld (Reduced.selectedPhysical reduced))
    bond step point →
  Telescope.defect (kernel weld)
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
  ≤ Chart.sourceDefectThreshold
relativeContourDefectBelowSourceThreshold reduced weld bond step point =
  let
    geometry = Reduced.asPath13FamilyGeometry reduced
    source = Family.geometrySourceAt geometry bond
    minus = Geometry.minusEmbedding source step
    background = Family.familyBackground geometry
    closed = path13RelativeClosedWord reduced bond step point

    bound74 = rawPathDefectBelowLengthBudget
      weld (Embed.embeddingCentre minus) closed 74
      (path13RelativeClosedWordLengthAtMost74 reduced bond step point)

    boundRelativeBudget :
      Telescope.defect (kernel weld)
        (RawPath.pathProduct
          (Erasure.rawPathFactors
            (R192.path13PhysicalPeriodicRealization background)
            (Embed.embeddingCentre minus) closed))
      ≤ R164.relativeLinkBudget
    boundRelativeBudget =
      subst
        (λ upper →
          Telescope.defect (kernel weld)
            (RawPath.pathProduct
              (Erasure.rawPathFactors
                (R192.path13PhysicalPeriodicRealization background)
                (Embed.embeddingCentre minus) closed))
          ≤ upper)
        R164.nat74BudgetIsRelativeLinkBudget
        bound74

    targetBound :
      Telescope.defect (kernel weld)
        (Family.erasedRelativeContour geometry bond step point)
      ≤ R164.relativeLinkBudget
    targetBound =
      subst
        (λ value → Telescope.defect (kernel weld) value
          ≤ R164.relativeLinkBudget)
        (rawClosedProductIsErasedRelativeContour reduced bond step point)
        boundRelativeBudget
  in
  ℚP.≤-trans targetBound R164.relativeLinkBudgetInsideSourceThreshold

selectedCutOrderIsRationalOrder :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra} →
  Path13SelectedCutDefectWeld selected →
  Scale.LessEqual
    (Path.scale (Path.defectAlgebra (Selected.cutData (PathTarget.bridge13 selected))))
  ≡ _≤_
selectedCutOrderIsRationalOrder {selected = selected} weld =
  trans
    (cong (λ algebra → Scale.LessEqual (Path.scale algebra))
      (Selected.sameDefectAlgebra (PathTarget.bridge13 selected)))
    (chartOrderIsRationalOrder weld)

selectedCutDefectIsKernelDefect :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    value →
  Path.defect
    (Path.defectAlgebra (Selected.cutData (PathTarget.bridge13 selected))) value
  ≡ Telescope.defect (kernel weld) value
selectedCutDefectIsKernelDefect {selected = selected} weld value =
  trans
    (cong (λ algebra → Path.defect algebra value)
      (Selected.sameDefectAlgebra (PathTarget.bridge13 selected)))
    (sym (kernelDefectIsSelectedDefect weld value))

selectedCutRecognizesSourceThreshold :
  ∀ {CoarseField}
    {selected : PathTarget.SelectedPhysicalBackground13Instantiation
      CoarseField Lie.SU2LieAlgebra}
    (weld : Path13SelectedCutDefectWeld selected)
    value →
  Telescope.defect (kernel weld) value ≤ Chart.sourceDefectThreshold →
  Log.InPrincipalImage
    (Selected.principalChart (PathTarget.bridge13 selected)) value
selectedCutRecognizesSourceThreshold {selected = selected} weld value operatorBound =
  let
    bridge = PathTarget.bridge13 selected
    cut = Selected.cutData bridge

    operatorBelowCut :
      Telescope.defect (kernel weld) value ≤ Path.chartRadius cut
    operatorBelowCut =
      ℚP.≤-trans operatorBound (sourceThresholdBelowSelectedCut weld)

    cutDefectBoundRational :
      Path.defect (Path.defectAlgebra cut) value ≤ Path.chartRadius cut
    cutDefectBoundRational =
      subst
        (λ lower → lower ≤ Path.chartRadius cut)
        (sym (selectedCutDefectIsKernelDefect weld value))
        operatorBelowCut

    cutDefectBound :
      Scale.LessEqual (Path.scale (Path.defectAlgebra cut))
        (Path.defect (Path.defectAlgebra cut) value)
        (Path.chartRadius cut)
    cutDefectBound =
      subst
        (λ relation → relation
          (Path.defect (Path.defectAlgebra cut) value)
          (Path.chartRadius cut))
        (sym (selectedCutOrderIsRationalOrder weld))
        cutDefectBoundRational

    admitted : Path.PrincipalLogAdmissible cut value
    admitted = Path.defectBelowRadiusImpliesAdmissible cut value cutDefectBound
  in
  subst
    (λ predicate → predicate value)
    (Selected.admissibleIsPrincipalImage bridge)
    admitted

path13RelativeContourInPrincipalImage :
  ∀ {CoarseField}
    (reduced : Reduced.ReducedPath13FamilyGeometry CoarseField)
    (weld : Path13SelectedCutDefectWeld (Reduced.selectedPhysical reduced))
    bond step point →
  Log.InPrincipalImage
    (Family.path13PrincipalChart (Reduced.asPath13FamilyGeometry reduced))
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
path13RelativeContourInPrincipalImage reduced weld bond step point =
  selectedCutRecognizesSourceThreshold weld
    (Family.erasedRelativeContour
      (Reduced.asPath13FamilyGeometry reduced) bond step point)
    (relativeContourDefectBelowSourceThreshold reduced weld bond step point)

cmp98Path13RawRelative74TelescopeLevel : ProofLevel
cmp98Path13RawRelative74TelescopeLevel = machineChecked

cmp98Path13ClosedPathSameObjectLevel : ProofLevel
cmp98Path13ClosedPathSameObjectLevel = machineChecked

cmp98Path13RelativeContourPrincipalImageCompilerLevel : ProofLevel
cmp98Path13RelativeContourPrincipalImageCompilerLevel = machineChecked

cmp98Path13PointwisePrincipalImageReceiptPrunedLevel : ProofLevel
cmp98Path13PointwisePrincipalImageReceiptPrunedLevel = machineChecked

-- One global representation/cut weld remains.  Pointwise contour admission is
-- downstream construction from it.
literalCMP98Path13SelectedCutDefectWeldLevel : ProofLevel
literalCMP98Path13SelectedCutDefectWeldLevel = conditional
