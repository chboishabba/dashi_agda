{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223DiagonalCauchyMajorantExact where

------------------------------------------------------------------------
-- THREE UNIFORM DIAGONAL CAUCHY BOUNDS -> POINTWISE E/R/B TRACE MAJORANTS.
--
-- CMP116 Sect.1 supplies the analytic/Cauchy principle: differentiation on a
-- smaller common polydisc costs inverse radius while preserving the external
-- localization majorant.  CMP119 imports that analytic class for E, supplies the
-- stronger R bound (2.31), and the B bound (2.42).
--
-- The remaining model-specific calibration is therefore not four derivatives
-- per sector.  It is one uniform diagonal metric-derivative upper constant for
-- each source sector on the selected common metric chart.  This file compiles
-- those THREE source/Cauchy constants into the exact four-diagonal pointwise
-- bounds consumed by the preferred cosmology sign route.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.KernelGeometryEmergenceObligations as K
import DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseToNumeratorMajorantExact as Pointwise
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119RationalFiniteMeasureOrderExact as Order
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.BalabanCMP119SourceNativeRawStateActiveBoundsExact as Raw

module _
    {Density Background Fluctuation
     Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm
     Configuration : Set}
    {source :
      Raw.CMP119SourceNativeRawState
        Density Background Fluctuation
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm VacuumTerm}
    {scale : Nat}
    (realization :
      Eq223.Eq223SourceMetricVariationRealization
        source Configuration scale)
    (measure : Physical.PhysicalFiniteYMMeasure Configuration ℚ)
    (orderLaws : Order.RationalPositiveFiniteMeasureOrderLaws measure)
  where

  module P = Pointwise realization measure orderLaws

  data DiagonalComponent : Set where
    d00 d11 d22 d33 : DiagonalComponent

  asComponent : DiagonalComponent → K.SymmetricTensorComponent4
  asComponent d00 = K.component00
  asComponent d11 = K.component11
  asComponent d22 = K.component22
  asComponent d33 = K.component33

  record UniformDiagonalCauchyUpperBounds : Set₁ where
    field
      regularPerDiagonalUpper : ℚ
      rOperationPerDiagonalUpper : ℚ
      boundaryPerDiagonalUpper : ℚ

      regularDiagonalBelow : ∀ diagonal configuration →
        Eq223.regularMetricVariation realization
          (Raw.regularSmallFieldTerm source scale)
          (asComponent diagonal) configuration
        ≤ regularPerDiagonalUpper

      rOperationDiagonalBelow : ∀ diagonal configuration →
        Eq223.rOperationMetricVariation realization
          (Raw.rOperationTerm source scale)
          (asComponent diagonal) configuration
        ≤ rOperationPerDiagonalUpper

      boundaryDiagonalBelow : ∀ diagonal configuration →
        Eq223.boundaryMetricVariation realization
          (Raw.boundaryTerm source scale)
          (asComponent diagonal) configuration
        ≤ boundaryPerDiagonalUpper

  open UniformDiagonalCauchyUpperBounds public

  fourTimes : ℚ → ℚ
  fourTimes value = (value + value) + (value + value)

  regularTraceBelowFourTimes :
    (bounds : UniformDiagonalCauchyUpperBounds) →
    ∀ configuration →
    DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact.regularDiagonalTrace
      (Eq223.sourceCompleteFiniteMetricVariation realization) configuration
    ≤ fourTimes (regularPerDiagonalUpper bounds)
  regularTraceBelowFourTimes bounds configuration =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (regularDiagonalBelow bounds d00 configuration)
        (regularDiagonalBelow bounds d11 configuration))
      (ℚP.+-mono-≤
        (regularDiagonalBelow bounds d22 configuration)
        (regularDiagonalBelow bounds d33 configuration))

  rOperationTraceBelowFourTimes :
    (bounds : UniformDiagonalCauchyUpperBounds) →
    ∀ configuration →
    DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact.rOperationDiagonalTrace
      (Eq223.sourceCompleteFiniteMetricVariation realization) configuration
    ≤ fourTimes (rOperationPerDiagonalUpper bounds)
  rOperationTraceBelowFourTimes bounds configuration =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (rOperationDiagonalBelow bounds d00 configuration)
        (rOperationDiagonalBelow bounds d11 configuration))
      (ℚP.+-mono-≤
        (rOperationDiagonalBelow bounds d22 configuration)
        (rOperationDiagonalBelow bounds d33 configuration))

  boundaryTraceBelowFourTimes :
    (bounds : UniformDiagonalCauchyUpperBounds) →
    ∀ configuration →
    DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact.boundaryDiagonalTrace
      (Eq223.sourceCompleteFiniteMetricVariation realization) configuration
    ≤ fourTimes (boundaryPerDiagonalUpper bounds)
  boundaryTraceBelowFourTimes bounds configuration =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (boundaryDiagonalBelow bounds d00 configuration)
        (boundaryDiagonalBelow bounds d11 configuration))
      (ℚP.+-mono-≤
        (boundaryDiagonalBelow bounds d22 configuration)
        (boundaryDiagonalBelow bounds d33 configuration))

  asPointwiseERBTraceUpperBounds :
    UniformDiagonalCauchyUpperBounds →
    P.PointwiseERBDiagonalTraceUpperBounds
  asPointwiseERBTraceUpperBounds bounds = record
    { P.PointwiseERBDiagonalTraceUpperBounds.regularPointwiseUpper =
        fourTimes (regularPerDiagonalUpper bounds)
    ; P.PointwiseERBDiagonalTraceUpperBounds.rOperationPointwiseUpper =
        fourTimes (rOperationPerDiagonalUpper bounds)
    ; P.PointwiseERBDiagonalTraceUpperBounds.boundaryPointwiseUpper =
        fourTimes (boundaryPerDiagonalUpper bounds)
    ; P.PointwiseERBDiagonalTraceUpperBounds.regularTraceBelow =
        regularTraceBelowFourTimes bounds
    ; P.PointwiseERBDiagonalTraceUpperBounds.rOperationTraceBelow =
        rOperationTraceBelowFourTimes bounds
    ; P.PointwiseERBDiagonalTraceUpperBounds.boundaryTraceBelow =
        boundaryTraceBelowFourTimes bounds
    }

threeUniformDiagonalCauchyBoundsReplaceTwelveComponentBounds : Bool
threeUniformDiagonalCauchyBoundsReplaceTwelveComponentBounds = true

cmp116CauchyPrincipleIsStandardImportedNotNewCosmologyMath : Bool
cmp116CauchyPrincipleIsStandardImportedNotNewCosmologyMath = true
