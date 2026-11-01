module DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAveragedContourExact where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredPeriodicEmbeddingExact as Embedding
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredExecutableGeometryExact as Executable
import DASHI.Physics.YangMills.BalabanClayGate4CMP109PeriodicContourFamilyInstantiationExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalAdmissibleRepositoryScaleExact as Minimal
import DASHI.Physics.YangMills.BalabanClayGate4CMP109MinimalContourFamilyExact as Contour
import DASHI.Physics.YangMills.BalabanClayGate4CMP109GroupAverageAxiomsExact as Average

------------------------------------------------------------------------
-- Equation-(0.11) group average on the literal minimal contour family.
--
-- The path carrier is no longer selected independently: it is exactly the
-- executable L=13 family of every ordering of the nonzero coordinate segments.
-- Gauge covariance of the averaged contour follows from covariance of each
-- path holonomy and Bałaban's bi-translation law.
------------------------------------------------------------------------

record MinimalContourGaugeData
    (Field Group Lie Scalar : Set)
    (geometry : Executable.CenteredExecutableGeometry Minimal.radius)
    (point : Centered.CenteredBlockPoint4 Minimal.radius)
    (averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar)
    : Set₁ where
  field
    holonomy transformedHolonomy :
      Field →
      Periodic.ExecutablePeriodicContour
        (Embedding.centeredTorusParameter Minimal.radius)
        (Contour.minimalContourStart geometry) →
      Group

    leftGauge rightGauge : Field → Group

    pathHolonomyGaugeCovariant : ∀ fld path →
      transformedHolonomy fld path
      ≡ Average.multiply averageAxioms (leftGauge fld)
          (Average.multiply averageAxioms
            (holonomy fld path) (rightGauge fld))

    contourHolonomiesSmallDiameter : ∀ fld →
      Average.SmallDiameter averageAxioms
        (Average.mapList (holonomy fld)
          (Contour.minimalContourFamily geometry point))

open MinimalContourGaugeData public

asGaugeCovariantPathFamily :
  ∀ {Field Group Lie Scalar : Set}
    {geometry : Executable.CenteredExecutableGeometry Minimal.radius}
    {point : Centered.CenteredBlockPoint4 Minimal.radius}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  MinimalContourGaugeData
    Field Group Lie Scalar geometry point averageAxioms →
  Average.GaugeCovariantPathFamily
    Field
    (Periodic.ExecutablePeriodicContour
      (Embedding.centeredTorusParameter Minimal.radius)
      (Contour.minimalContourStart geometry))
    Group Lie Scalar averageAxioms
asGaugeCovariantPathFamily {geometry = geometry} {point = point} dataSet = record
  { paths =
      Contour.minimalContourFamily geometry point
  ; holonomy = holonomy dataSet
  ; transformedHolonomy =
      transformedHolonomy dataSet
  ; leftGauge = leftGauge dataSet
  ; rightGauge = rightGauge dataSet
  ; transformedHolonomyGaugeCovariant =
      pathHolonomyGaugeCovariant dataSet
  ; pathFamilySmallDiameter =
      contourHolonomiesSmallDiameter dataSet
  }

minimalAveragedContour :
  ∀ {Field Group Lie Scalar : Set}
    {geometry : Executable.CenteredExecutableGeometry Minimal.radius}
    {point : Centered.CenteredBlockPoint4 Minimal.radius}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  MinimalContourGaugeData
    Field Group Lie Scalar geometry point averageAxioms →
  Field → Group
minimalAveragedContour dataSet =
  Average.averagedContour (asGaugeCovariantPathFamily dataSet)

minimalTransformedAveragedContour :
  ∀ {Field Group Lie Scalar : Set}
    {geometry : Executable.CenteredExecutableGeometry Minimal.radius}
    {point : Centered.CenteredBlockPoint4 Minimal.radius}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar} →
  MinimalContourGaugeData
    Field Group Lie Scalar geometry point averageAxioms →
  Field → Group
minimalTransformedAveragedContour dataSet =
  Average.transformedAveragedContour
    (asGaugeCovariantPathFamily dataSet)

minimalAveragedContourGaugeCovariant :
  ∀ {Field Group Lie Scalar : Set}
    {geometry : Executable.CenteredExecutableGeometry Minimal.radius}
    {point : Centered.CenteredBlockPoint4 Minimal.radius}
    {averageAxioms : Average.CMP109GroupAverageAxioms Group Lie Scalar}
    (dataSet : MinimalContourGaugeData
      Field Group Lie Scalar geometry point averageAxioms)
    field →
  minimalTransformedAveragedContour dataSet field
  ≡ Average.multiply averageAxioms (leftGauge dataSet field)
      (Average.multiply averageAxioms
        (minimalAveragedContour dataSet field)
        (rightGauge dataSet field))
minimalAveragedContourGaugeCovariant dataSet =
  Average.averagedContourGaugeCovariant
    (asGaugeCovariantPathFamily dataSet)

cmp109MinimalEquation011PathIdentificationLevel : ProofLevel
cmp109MinimalEquation011PathIdentificationLevel = machineChecked

cmp109MinimalEquation011GaugeCovarianceLevel : ProofLevel
cmp109MinimalEquation011GaugeCovarianceLevel = machineChecked

physicalCMP109MinimalContourHolonomyInputsLevel : ProofLevel
physicalCMP109MinimalContourHolonomyInputsLevel = conditional

physicalCMP109MinimalContourSmallDiameterInputsLevel : ProofLevel
physicalCMP109MinimalContourSmallDiameterInputsLevel = conditional
