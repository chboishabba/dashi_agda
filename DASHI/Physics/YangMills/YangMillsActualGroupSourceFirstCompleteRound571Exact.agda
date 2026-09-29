{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsActualGroupSourceFirstCompleteRound571Exact where

------------------------------------------------------------------------
-- GOAL-1 G1 / ROUND571:
-- SOURCE-FIRST ACTUAL-GROUP COMPLETE BUNDLE
--
-- Preferred all-G construction:
--
--   actual CompactSimpleLieGroup witness
--       ↓
--   quantitative estimates whose bracket/exp/log/Ad ARE those actual ops
--       ↓
--   five-block physical scalar source built on that exact quantitative package
--
-- All historical alignment equations are compiler-owned.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as Structural
import DASHI.Physics.YangMills.YangMillsActualGroupQuantitativeConstructorRound569Exact as R569
import DASHI.Physics.YangMills.YangMillsActualGroupFiveBlockConstructorRound570Exact as R570
import DASHI.Physics.YangMills.YangMillsActualGroupCompleteSourceRound543Exact as R543

record ActualGroupSourceFirstComplete
    (GaugeIndex X : Set) : Set₂ where
  field
    structural :
      Structural.StructuralSourceBundle GaugeIndex X

    quantitative :
      R569.ActualGroupQuantitativeSource
        GaugeIndex X structural

    fiveBlock :
      R570.ActualGroupFiveBlockCompleteSource
        GaugeIndex X structural quantitative

open ActualGroupSourceFirstComplete public

asLegacyActualGroupCompleteSource :
  ∀ {GaugeIndex X} →
  ActualGroupSourceFirstComplete GaugeIndex X →
  R543.ActualGroupCompleteSource GaugeIndex X
asLegacyActualGroupCompleteSource source = record
  { R543.ActualGroupCompleteSource.structural =
      structural source
  ; R543.ActualGroupCompleteSource.alignment =
      R569.asActualGroupQuantitativeAlignment
        (quantitative source)
  ; R543.ActualGroupCompleteSource.fiveBlockSource =
      R570.asR541FiveBlockSource
        (quantitative source)
        (fiveBlock source)
  }

round571SourceFirstAllGroupCompilerLevel : ProofLevel
round571SourceFirstAllGroupCompilerLevel = machineChecked

round571OperationAlignmentFieldsRequired : Bool
round571OperationAlignmentFieldsRequired = false

round571FiveBlockPackageAlignmentRequired : Bool
round571FiveBlockPackageAlignmentRequired = false

round571SU2PromotionRequired : Bool
round571SU2PromotionRequired = false

------------------------------------------------------------------------
-- Genuine remaining G1 source work.
------------------------------------------------------------------------

literalRound571ActualCompactSimpleWitnessLevel : ProofLevel
literalRound571ActualCompactSimpleWitnessLevel =
  Structural.literalRound517AllGroupCompactSimpleSourceLevel

literalRound571ActualQuantitativeBoundsLevel : ProofLevel
literalRound571ActualQuantitativeBoundsLevel =
  R569.literalRound569ActualGroupQuantitativeBoundsLevel

literalRound571FiveBlockPhysicalDataLevel : ProofLevel
literalRound571FiveBlockPhysicalDataLevel =
  R570.literalRound570ActualGroupFiveBlockPhysicalDataLevel

literalRound571SourceFirstActualGroupCompleteLevel : ProofLevel
literalRound571SourceFirstActualGroupCompleteLevel = conditional
