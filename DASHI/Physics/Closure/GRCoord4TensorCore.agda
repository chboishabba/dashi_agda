module DASHI.Physics.Closure.GRCoord4TensorCore where

------------------------------------------------------------------------
-- Minimal four-coordinate tensor API for GR closure work.
--
-- This module supplies only the component carrier shapes that the current
-- continuum/GR obstruction receipts identify as absent: a concrete Coord4
-- index, metric/inverse metric component families, partial-derivative shape,
-- Christoffel components, and Ricci components.  It intentionally contains no
-- Christoffel formula law, inverse law, Ricci contraction theorem, convergence
-- estimate, Einstein equation, Schwarzschild authority, or GR promotion.
--
-- The diagonal helpers below stay carrier-only and are meant for future
-- Schwarzschild-friendly bookkeeping on the four independent slots only.

data Coord4 : Set where
  coord0 : Coord4
  coord1 : Coord4
  coord2 : Coord4
  coord3 : Coord4

Tensor0 :
  Set →
  Set
Tensor0 Scalar =
  Scalar

Tensor1 :
  Set →
  Set
Tensor1 Scalar =
  Coord4 →
  Scalar

Tensor2 :
  Set →
  Set
Tensor2 Scalar =
  Coord4 →
  Coord4 →
  Scalar

Tensor3 :
  Set →
  Set
Tensor3 Scalar =
  Coord4 →
  Coord4 →
  Coord4 →
  Scalar

Tensor4 :
  Set →
  Set
Tensor4 Scalar =
  Coord4 →
  Coord4 →
  Coord4 →
  Coord4 →
  Scalar

record DiagonalTensor2 (Scalar : Set) : Set where
  constructor diagTensor2
  field
    component00 :
      Scalar
    component11 :
      Scalar
    component22 :
      Scalar
    component33 :
      Scalar

Metric :
  Set →
  Set
Metric =
  Tensor2

MetricT :
  Set →
  Set
MetricT = Metric

InverseMetric :
  Set →
  Set
InverseMetric =
  Tensor2

InvMetric :
  Set →
  Set
InvMetric = InverseMetric

Partial :
  Set →
  Set
Partial Tensor =
  Coord4 →
  Tensor →
  Tensor

MetricPartial :
  Set →
  Set
MetricPartial Scalar =
  Partial (Metric Scalar)

PartialG :
  Set →
  Set
PartialG = MetricPartial

Christoffel :
  Set →
  Set
Christoffel =
  Tensor3

ChristoffelT :
  Set →
  Set
ChristoffelT = Christoffel

Riemann :
  Set →
  Set
Riemann =
  Tensor4

Ricci :
  Set →
  Set
Ricci =
  Tensor2

RicciT :
  Set →
  Set
RicciT = Ricci

DiagonalMetric :
  Set →
  Set
DiagonalMetric = DiagonalTensor2

DiagonalInvMetric :
  Set →
  Set
DiagonalInvMetric = DiagonalTensor2

DiagonalRicciT :
  Set →
  Set
DiagonalRicciT = DiagonalTensor2

record GRCoord4TensorPackage (Scalar : Set) : Set₁ where
  field
    metric :
      Metric Scalar

    inverseMetric :
      InverseMetric Scalar

    partial :
      MetricPartial Scalar

    christoffel :
      Christoffel Scalar

    ricci :
      Ricci Scalar

record GRCoord4TensorFormulaSurface (Scalar : Set) : Set₁ where
  field
    metric :
      Metric Scalar

    inverseMetric :
      InverseMetric Scalar

    metricPartial :
      MetricPartial Scalar

    christoffel :
      Christoffel Scalar

    ricci :
      Ricci Scalar

    ChristoffelFormula :
      Set

    RicciContraction :
      Set

    InverseMetricLaw :
      Set

    MetricCompatibilityLaw :
      Set

record DiagonalGRCoord4TensorPackage (Scalar : Set) : Set₁ where
  field
    metric :
      DiagonalMetric Scalar

    inverseMetric :
      DiagonalInvMetric Scalar

    partialG :
      PartialG Scalar

    christoffelT :
      ChristoffelT Scalar

    ricciT :
      RicciT Scalar
