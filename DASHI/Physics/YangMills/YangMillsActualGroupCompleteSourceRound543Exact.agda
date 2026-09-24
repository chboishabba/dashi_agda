{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact where

------------------------------------------------------------------------
-- GOAL-1 / ALL-G / ROUND543:
-- ONE ACTUAL-GROUP SOURCE OBJECT OWNS STRUCTURE + QUANTITATIVE DATA + G1
--
-- Do not let downstream code independently choose:
--
--   * the proof-bearing compact-simple group,
--   * a classification-tag quantitative package,
--   * and the five-block Yang--Mills source map.
--
-- R543 packages the R517/R541 objects into one source.  This does not prove
-- their remaining analytic fields; it removes cross-object mixing as a
-- separate failure mode.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import Data.Rational.Base as ℚ
import DASHI.Physics.YangMills.CompactLieGroupCore as Core
import DASHI.Physics.YangMills.CompactSimpleQuantitativeCoverage as Quant
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeAlignmentRound541Exact as Alignment
import DASHI.Physics.YangMills.BalabanGroupParametricFiveBlockSignedG2Exact as G1

record ActualGroupCompleteSource
    (GaugeIndex X : Set) : Set₂ where
  field
    structural :
      Structural.StructuralSourceBundle GaugeIndex X

    alignment :
      Alignment.ActualGroupQuantitativeAlignment
        GaugeIndex X structural

    fiveBlockSource :
      Alignment.ActualGroupFiveBlockSource
        GaugeIndex X structural alignment

open ActualGroupCompleteSource public

actualCompactSimple :
  ∀ {GaugeIndex X}
    (source : ActualGroupCompleteSource GaugeIndex X)
    group →
  Core.CompactSimpleLieGroup
    (Structural.GroupCarrier (structural source) group)
    (Structural.LieCarrier (structural source) group)
actualCompactSimple source =
  Structural.compactSimple (structural source)

alignedQuantitative :
  ∀ {GaugeIndex X}
    (source : ActualGroupCompleteSource GaugeIndex X)
    group →
  Quant.QuantitativeCompactLiePackage
    ℚ.ℚ
    (Structural.LieCarrier (structural source) group)
    (Structural.GroupCarrier (structural source) group)
    (Alignment.classification (alignment source) group)
alignedQuantitative source =
  Alignment.quantitative (alignment source)

alignedFiveBlock :
  ∀ {GaugeIndex X}
    (source : ActualGroupCompleteSource GaugeIndex X)
    group →
  G1.GroupParametricFiveBlockG2Data
    (Structural.LieCarrier (structural source) group)
    (Structural.GroupCarrier (structural source) group)
    (Alignment.classification (alignment source) group)
alignedFiveBlock source =
  Alignment.fiveBlock (fiveBlockSource source)

fiveBlockUsesActualAlignedQuantitative :
  ∀ {GaugeIndex X}
    (source : ActualGroupCompleteSource GaugeIndex X)
    group →
  G1.quantitativeLiePackage (alignedFiveBlock source group)
  ≡
  alignedQuantitative source group
fiveBlockUsesActualAlignedQuantitative source =
  Alignment.fiveBlockQuantitativeIsAligned (fiveBlockSource source)

round543ActualGroupCompleteSourceCompilerLevel : ProofLevel
round543ActualGroupCompleteSourceCompilerLevel = machineChecked

round543StructuralWitnessLevel : ProofLevel
round543StructuralWitnessLevel =
  Structural.literalRound517AllGroupCompactSimpleSourceLevel

round543ActualGroupAlignmentLevel : ProofLevel
round543ActualGroupAlignmentLevel =
  Alignment.literalRound541ActualGroupQuantitativeAlignmentLevel

round543FiveBlockSourceMapLevel : ProofLevel
round543FiveBlockSourceMapLevel =
  Alignment.literalRound541AlignedFiveBlockSourceLevel

round543IndependentStructuralAndQuantitativeSelectionsAllowed : Bool
round543IndependentStructuralAndQuantitativeSelectionsAllowed = false

round543SU2PromotionAllowed : Bool
round543SU2PromotionAllowed = false

-- The package is complete architecturally, not analytically.
literalRound543ActualGroupCompleteSourceLevel : ProofLevel
literalRound543ActualGroupCompleteSourceLevel = conditional
