module DASHI.Core.ComparisonLawCore where

------------------------------------------------------------------------
-- Generic comparison law for two structured carriers projected into a
-- common surface.
--
-- The core abstraction is governed comparison under projection:
-- two carriers project into the same public surface, a comparison law
-- governs admissible agreement on that surface, and a residual records
-- the typed obstruction when the projections fail to commute or glue.
------------------------------------------------------------------------

record ComparisonLawCore : Set₁ where
  constructor comparisonLawCore
  field
    LeftCarrier    : Set
    RightCarrier   : Set
    Surface        : Set
    leftProject    : LeftCarrier → Surface
    rightProject   : RightCarrier → Surface
    Residual       : Surface → Surface → Set
    ComparisonLaw  : Surface → Surface → Set

open ComparisonLawCore public

ProjectedLeft :
  (core : ComparisonLawCore) →
  LeftCarrier core → Surface core
ProjectedLeft core =
  leftProject core

ProjectedRight :
  (core : ComparisonLawCore) →
  RightCarrier core → Surface core
ProjectedRight core =
  rightProject core

ComparisonResidual :
  (core : ComparisonLawCore) →
  Surface core → Surface core → Set
ComparisonResidual core =
  Residual core
