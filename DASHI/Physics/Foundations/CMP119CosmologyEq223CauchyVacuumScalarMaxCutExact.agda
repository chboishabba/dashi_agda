{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223CauchyVacuumScalarMaxCutExact where

------------------------------------------------------------------------
-- PREFERRED EQ.(2.23) SIGN MAX-CUT.
--
-- All finite-measure and four-diagonal bookkeeping has now compiled away.
-- It is sufficient to prove THREE uniform source/Cauchy derivative bounds
--
--   E_diag <= M_E,   R_diag <= M_R,   B_diag <= M_B
--
-- and the ONE scalar source inequality
--
--   4(M_E + M_R + M_B) < - c_V,
--
-- where c_V is literally the four-diagonal metric derivative of the selected
-- Eq.(2.23) vacuum-energy term.  The existing compilers then yield the literal
-- weighted finite-measure dominance N_E+N_R+N_B < -N_V.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; -_; _<_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Foundations.CMP119CosmologyEq223DiagonalCauchyMajorantExact as Cauchy
import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyEq223PointwiseVacuumMarginExact as Margin
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
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
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
  where

  module C = Cauchy realization measure orderLaws
  module M = Margin realization measure orderLaws partition scaleLaw

  sourceCauchyTotal : C.UniformDiagonalCauchyUpperBounds → ℚ
  sourceCauchyTotal bounds =
    (C.regularPerDiagonalUpper bounds
      + C.rOperationPerDiagonalUpper bounds)
      + C.boundaryPerDiagonalUpper bounds

  fourSourceCauchyTotal : C.UniformDiagonalCauchyUpperBounds → ℚ
  fourSourceCauchyTotal bounds = C.fourTimes (sourceCauchyTotal bounds)

  pointwiseSourceUpperTotalIsFourSourceCauchyTotal :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    M.sourceUpperTotal (C.asPointwiseERBTraceUpperBounds bounds)
    ≡ fourSourceCauchyTotal bounds
  pointwiseSourceUpperTotalIsFourSourceCauchyTotal bounds =
    Ring.solve-∀
      (C.regularPerDiagonalUpper bounds)
      (C.rOperationPerDiagonalUpper bounds)
      (C.boundaryPerDiagonalUpper bounds)

  cauchyVacuumScalarMarginForcesLiteralDominance :
    (bounds : C.UniformDiagonalCauchyUpperBounds) →
    fourSourceCauchyTotal bounds
      < - Eq223.eq223VacuumTraceCoefficient realization →
    Dominance.LiteralNegativeSectorDominance realization measure
  cauchyVacuumScalarMarginForcesLiteralDominance bounds scalarMargin =
    M.sourceScalarMarginForcesLiteralDominance
      (C.asPointwiseERBTraceUpperBounds bounds)
      (subst
        (λ left → left < - Eq223.eq223VacuumTraceCoefficient realization)
        (sym (pointwiseSourceUpperTotalIsFourSourceCauchyTotal bounds))
        scalarMargin)

preferredEq223SignHasOneScalarMarginAfterThreeCauchyCalibrations : Bool
preferredEq223SignHasOneScalarMarginAfterThreeCauchyCalibrations = true

finiteMeasureAndFourDiagonalArithmeticCompilerOwned : Bool
finiteMeasureAndFourDiagonalArithmeticCompilerOwned = true
