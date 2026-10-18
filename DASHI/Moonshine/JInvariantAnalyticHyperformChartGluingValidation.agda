module DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingValidation where

import DASHI.Foundations.HyperformChartGluingExact as Glue
import DASHI.Moonshine.JInvariantAnalyticHyperformChartGluingExact as Atlas
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinSameObjectCompilerExact as Lattice
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex

e4AtlasHasExplicitOverlap :
  (M : Lattice.BishopLatticeEisensteinModel) →
  (qE4 qE6 : Lattice.Parameter M → Complex.BishopComplex) →
  ∀ {system} →
  (atlas : Atlas.JInvariantAnalyticHyperformAtlas M qE4 qE6 system) →
  (tau : Lattice.Parameter M) →
  Complex._≈C_
    (Glue.chartA (Atlas.e4PresentationGluing atlas) tau)
    (Glue.chartB (Atlas.e4PresentationGluing atlas) tau)
e4AtlasHasExplicitOverlap M qE4 qE6 atlas tau =
  Glue.glueOnOverlap (Atlas.e4PresentationGluing atlas) tau
