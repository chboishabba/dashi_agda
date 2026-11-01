{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsSourceFirstStressChoiceRound522Exact where

------------------------------------------------------------------------
-- GOAL-1 C4 / ROUND522:
-- CHOOSE THE LITERAL STRESS TENSOR FROM THE COMPLETED MARKED SOURCE
--
-- The generic same-completed-state source package constructs a continuum stress
-- field before the Clay construction is chosen.  Therefore the equality
--
--   completed marked stress = literal Clay stress
--
-- is a model-choice equality on the preferred route.  Choose the literal
-- stressTensor projection from that source field and it becomes refl.
--
-- This does NOT pay:
--   * the marked-source Hilbert modulus;
--   * finite stress insertion = CMP119 local insertion;
--   * Cauchy completion = completed marked stress;
--   * literal density/metric derivative.
--
-- Those remain genuine source facts.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact as Nuclear
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact as Marked
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact as StressMarked

record SourceFirstStressChoice
    (C : Top.LiteralYangMillsCarriers) : Set₂ where
  field
    continuityScale :
      Top.CompactSimpleGroup C → Nuclear.ContinuityScale

    CompletedState :
      Top.CompactSimpleGroup C → Set

    completedSources :
      ∀ group →
      StressMarked.SameCompletedCompositeStressMarkedSource
        (continuityScale group)
        (CompletedState group)
        (Top.LocalOperator C)
        (Top.StressTensor C)

open SourceFirstStressChoice public

selectedStress :
  ∀ {C} →
  SourceFirstStressChoice C →
  Top.CompactSimpleGroup C →
  Top.StressTensor C
selectedStress choice group =
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (completedSources choice group)))

withSourceFirstStress :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S) →
  SourceFirstStressChoice C →
  Top.LiteralYangMillsConstruction C S
withSourceFirstStress Y choice = record
  { Top.LiteralYangMillsConstruction.spacetime =
      Top.spacetime Y
  ; Top.LiteralYangMillsConstruction.finiteMeasure =
      Top.finiteMeasure Y
  ; Top.LiteralYangMillsConstruction.continuumMeasure =
      Top.continuumMeasure Y
  ; Top.LiteralYangMillsConstruction.schwinger =
      Top.schwinger Y
  ; Top.LiteralYangMillsConstruction.localObservable =
      Top.localObservable Y
  ; Top.LiteralYangMillsConstruction.curvatureOperator =
      Top.curvatureOperator Y
  ; Top.LiteralYangMillsConstruction.opeCoefficient =
      Top.opeCoefficient Y
  ; Top.LiteralYangMillsConstruction.opeRemainder =
      Top.opeRemainder Y
  ; Top.LiteralYangMillsConstruction.stressTensor =
      selectedStress choice
  ; Top.LiteralYangMillsConstruction.hilbertSpace =
      Top.hilbertSpace Y
  ; Top.LiteralYangMillsConstruction.hamiltonian =
      Top.hamiltonian Y
  ; Top.LiteralYangMillsConstruction.vacuum =
      Top.vacuum Y
  ; Top.LiteralYangMillsConstruction.massGap =
      Top.massGap Y
  }

completedMarkedStressIsChosenLiteralStress :
  ∀ {C S}
    (Y : Top.LiteralYangMillsConstruction C S)
    (choice : SourceFirstStressChoice C)
    group →
  Marked.continuumComposite
    (StressMarked.stressField
      (StressMarked.sameCompletedMarkedSourcesGiveCompositeAndStressFields
        (completedSources choice group)))
  ≡
  Top.stressTensor (withSourceFirstStress Y choice) group
completedMarkedStressIsChosenLiteralStress Y choice group = refl

round522SourceFirstStressCompilerLevel : ProofLevel
round522SourceFirstStressCompilerLevel = machineChecked

round522CompletedStressLiteralEqualityLevel : ProofLevel
round522CompletedStressLiteralEqualityLevel = machineChecked

-- Physical production of the same-completed composite/stress marked source
-- remains a real theorem input.
literalRound522CompletedMarkedSourceLevel : ProofLevel
literalRound522CompletedMarkedSourceLevel =
  StressMarked.physicalStressMarkedSourceHilbertModulusLevel
