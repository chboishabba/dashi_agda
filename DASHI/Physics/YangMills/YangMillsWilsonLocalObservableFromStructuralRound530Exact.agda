{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFromStructuralRound530Exact where

------------------------------------------------------------------------
-- GOAL-1 C0 / ROUND530:
-- WILSON LOCAL OBSERVABLES USE THE SAME ACTUAL COMPACT-SIMPLE GROUP WITNESS
--
-- R517 carries an actual CompactSimpleLieGroup for every literal group index.
-- R529 needs only its underlying Group structure.  Do not select another group
-- model for the local observable lane.
------------------------------------------------------------------------

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.CompactLieGroupCore as Core

import DASHI.Physics.YangMills.CompactLieLatticeGauge as Lattice
import DASHI.Physics.YangMills.YangMillsConcreteStructuralSemanticsRound517Exact as R517
import DASHI.Physics.YangMills.YangMillsWilsonLocalObservableFamilyRound529Exact as R529

record StructuralWilsonLocalData
    (G X Configuration Position : Set)
    (structural : R517.StructuralSourceBundle G X)
    : Set₂ where
  field
    Vertex : G → Set

    Edge :
      ∀ group →
      Vertex group → Vertex group → Set

    decode :
      ∀ group →
      Configuration →
      Lattice.GaugeField
        {G = R517.GroupCarrier structural group}
        (Edge group)

    baseAt :
      ∀ group →
      Position → Vertex group

    boundaryAt :
      ∀ group position →
      Lattice.Path (Edge group)
        (baseAt group position)
        (baseAt group position)

    classValue :
      ∀ group →
      R517.GroupCarrier structural group → ℝ

    classFunction :
      ∀ groupIndex →
      Lattice.ClassFunction
        (Core.group (R517.compactSimple structural groupIndex))
        (classValue groupIndex)

open StructuralWilsonLocalData public

asWilsonLocalObservableFamily :
  ∀ {G X Configuration Position}
    {structural : R517.StructuralSourceBundle G X} →
  StructuralWilsonLocalData
    G X Configuration Position structural →
  R529.WilsonLocalObservableFamily G Configuration Position
asWilsonLocalObservableFamily {structural = structural} dataSet = record
  { R529.WilsonLocalObservableFamily.Vertex =
      Vertex dataSet
  ; R529.WilsonLocalObservableFamily.GroupElement =
      R517.GroupCarrier structural
  ; R529.WilsonLocalObservableFamily.Edge =
      Edge dataSet
  ; R529.WilsonLocalObservableFamily.groupStructure =
      λ groupIndex →
        Core.group (R517.compactSimple structural groupIndex)
  ; R529.WilsonLocalObservableFamily.source =
      λ groupIndex → record
        { R529.WilsonLocalObservableAt.decode =
            decode dataSet groupIndex
        ; R529.WilsonLocalObservableAt.baseAt =
            baseAt dataSet groupIndex
        ; R529.WilsonLocalObservableAt.boundaryAt =
            boundaryAt dataSet groupIndex
        ; R529.WilsonLocalObservableAt.classValue =
            classValue dataSet groupIndex
        ; R529.WilsonLocalObservableAt.classFunction =
            classFunction dataSet groupIndex
        }
  }

round530StructuralWilsonFamilyCompilerLevel : ProofLevel
round530StructuralWilsonFamilyCompilerLevel = machineChecked

-- The group structure itself is no longer a C0 payment.  Remaining realization
-- is exactly lattice/configuration decoding + local loop/class-function choice.
literalRound530StructuralWilsonLocalDataLevel : ProofLevel
literalRound530StructuralWilsonLocalDataLevel = conditional
