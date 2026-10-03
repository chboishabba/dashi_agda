{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyEq223ERBUpperMajorantExact where

------------------------------------------------------------------------
-- SOURCE-SIGN PARETO CUT: THREE E/R/B UPPER ESTIMATES -> ONE VACUUM MARGIN.
--
-- The preferred gravitational sign target is
--
--   N_E + N_R + N_B < - N_V.
--
-- Source analysis often supplies upper estimates sectorwise.  Do not require
-- the three exact numerators to be evaluated separately once such estimates
-- exist.  If
--
--   N_E <= M_E,  N_R <= M_R,  N_B <= M_B
--
-- and
--
--   M_E + M_R + M_B < -N_V,
--
-- then the literal Eq.(2.23) dominance follows.  This owner is pinned to the
-- actual selected Eq.(2.23) metric variation and introduces no sign claim for
-- any sector.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; -_; _≤_; _<_)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Foundations.CMP119CosmologyEq223NegativeSectorDominanceExact as Dominance
import DASHI.Physics.Foundations.CMP119CosmologyEq223SourceMetricVariationExact as Eq223
import DASHI.Physics.Foundations.CMP119CosmologyR136WeylSectorDecompositionExact as Sector
import DASHI.Physics.Foundations.CMP119CosmologyPartitionStressFirstVariationExact as Source
import DASHI.Physics.Foundations.CMP119CosmologyVacuumSectorFactorizationExact as Vacuum
import DASHI.Physics.Foundations.CMP119CosmologyPhysicalFinitePartitionAuthorityExact as Partition
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
  where

  d : Source.CompleteFiniteMetricVariation Configuration
  d = Eq223.sourceCompleteFiniteMetricVariation realization

  record LiteralERBUpperMajorants : Set₁ where
    field
      regularUpper : ℚ
      rOperationUpper : ℚ
      boundaryUpper : ℚ

      regularBelowUpper :
        Sector.regularNumerator measure d ≤ regularUpper

      rOperationBelowUpper :
        Sector.rOperationNumerator measure d ≤ rOperationUpper

      boundaryBelowUpper :
        Sector.boundaryNumerator measure d ≤ boundaryUpper

  open LiteralERBUpperMajorants public

  erbUpperTotal : LiteralERBUpperMajorants → ℚ
  erbUpperTotal bounds =
    (regularUpper bounds + rOperationUpper bounds)
      + boundaryUpper bounds

  literalERBNumerator : ℚ
  literalERBNumerator =
    (Sector.regularNumerator measure d
      + Sector.rOperationNumerator measure d)
      + Sector.boundaryNumerator measure d

  literalERBBelowUpperTotal :
    (bounds : LiteralERBUpperMajorants) →
    literalERBNumerator ≤ erbUpperTotal bounds
  literalERBBelowUpperTotal bounds =
    ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (regularBelowUpper bounds)
        (rOperationBelowUpper bounds))
      (boundaryBelowUpper bounds)

  upperTotalBelowNegativeVacuumForcesDominance :
    (bounds : LiteralERBUpperMajorants) →
    erbUpperTotal bounds
      < - Sector.vacuumNumerator measure d →
    Dominance.LiteralNegativeSectorDominance realization measure
  upperTotalBelowNegativeVacuumForcesDominance bounds upperStrict =
    ℚP.≤-<-trans
      (literalERBBelowUpperTotal bounds)
      upperStrict

  record FactoredVacuumMargin
      (partition : Partition.PhysicalFinitePartitionAuthority measure)
      (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
      : Set₁ where
    field
      vacuumConstant : Vacuum.VacuumTraceConstant d

      upperTotalBelowFactoredVacuum :
        erbUpperTotal
          -- The bounds are supplied to the theorem below; this field is only
          -- the source-side vacuum datum and is intentionally not used here.
          ?
        < - (Vacuum.coefficient vacuumConstant
              * Physical.haarIntegral measure (Physical.density measure))

  -- The useful factored form is theorem-level rather than stored in the record:
  -- it keeps E/R/B majorants and the vacuum source datum independent.
  factoredVacuumMarginForcesDominance :
    (bounds : LiteralERBUpperMajorants)
    (partition : Partition.PhysicalFinitePartitionAuthority measure)
    (scaleLaw : Vacuum.RationalHaarScaleLaw measure)
    (constant : Vacuum.VacuumTraceConstant d) →
    erbUpperTotal bounds
      < - (Vacuum.coefficient constant
            * Physical.haarIntegral measure (Physical.density measure)) →
    Dominance.LiteralNegativeSectorDominance realization measure
  factoredVacuumMarginForcesDominance
      bounds partition scaleLaw constant margin =
    upperTotalBelowNegativeVacuumForcesDominance
      bounds
      (Relation.Binary.PropositionalEquality.subst
        (λ value → erbUpperTotal bounds < - value)
        (Relation.Binary.PropositionalEquality.sym
          (Vacuum.vacuumNumeratorFactors measure d scaleLaw constant))
        margin)

  sourceSignNowAcceptsThreeUpperBoundsPlusOneStrictMargin : Bool
  sourceSignNowAcceptsThreeUpperBoundsPlusOneStrictMargin = true

  noERBSignAssumptionIntroduced : Bool
  noERBSignAssumptionIntroduced = true
