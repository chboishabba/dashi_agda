{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentCompactnessRound434Exact where

------------------------------------------------------------------------
-- ROUND434 / GLOBAL SELECTED CONTAINMENT -> FULL COMPACTNESS INPUT PACKAGE
--
-- Round211 identified the least-privilege H2a theorem:
--
--   on the literal selected diagonal measure sequence, the already-owned
--   moment bound controls escape from one admissible compact witness uniformly
--   in cutoff.
--
-- That theorem is exactly SelectedMomentCompactContainmentInputs.
--
-- R432 turns it into selected diagonal tightness.
-- R431 gives every-subsequence tightness.
-- R430 derives unique cluster points from P2 determining expectations.
-- R427 then gives full sequence convergence.
--
-- R434 packages that chain so the preferred continuum route cannot replace
-- global compact containment by an arbitrary tightness assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5MomentToSelectedDiagonalTightnessRound432Exact as R432
import DASHI.Physics.YangMills.BalabanClayT5SelectedDiagonalTightnessRound431Exact as R431
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5ClusterPointUniquenessRound430Exact as R430

record GlobalContainmentCompactnessInputs
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (Epsilon Witness : Set) : Set₂ where
  field
    convergence : Limit.SequentialLimit Measure

    -- Exact global H2a theorem on the literal selected family.
    globalContainment :
      Moment.SelectedMomentCompactContainmentInputs
        Measure Observable Scalar Epsilon Witness expectationData

    prokhorovAuthority :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure

    determiningUniqueness :
      R430.DeterminingExpectationUniquenessAuthority
        expectationData
        (R431.asPhysicalSubsequenceTightnessData
          (R432.momentContainmentToSelectedDiagonalTightness
            convergence globalContainment))
        prokhorovAuthority

    compactUniqueFullConvergenceAuthority :
      Compact.CompactUniqueFullConvergenceAuthority Measure

  selectedTightness :
    R431.SelectedDiagonalTightnessInputs expectationData
  selectedTightness =
    R432.momentContainmentToSelectedDiagonalTightness
      convergence globalContainment

open GlobalContainmentCompactnessInputs public

asR430CompactnessUniqueness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  GlobalContainmentCompactnessInputs expectationData Epsilon Witness →
  R430.LiteralT5CompactnessUniquenessInputs expectationData
asR430CompactnessUniqueness inputs = record
  { R430.LiteralT5CompactnessUniquenessInputs.selectedTightness =
      selectedTightness inputs
  ; R430.LiteralT5CompactnessUniquenessInputs.prokhorovAuthority =
      prokhorovAuthority inputs
  ; R430.LiteralT5CompactnessUniquenessInputs.determiningUniqueness =
      determiningUniqueness inputs
  ; R430.LiteralT5CompactnessUniquenessInputs.compactUniqueFullConvergenceAuthority =
      compactUniqueFullConvergenceAuthority inputs
  }

round434GlobalContainmentCompactnessCompilerLevel : ProofLevel
round434GlobalContainmentCompactnessCompilerLevel = machineChecked

round434GlobalMomentCompactContainmentLevel : ProofLevel
round434GlobalMomentCompactContainmentLevel = conditional

round434SelectedDiagonalTightnessLevel : ProofLevel
round434SelectedDiagonalTightnessLevel = machineChecked

round434EverySubsequenceTightLevel : ProofLevel
round434EverySubsequenceTightLevel = machineChecked

round434EveryClusterPointIsSelectedTargetLevel : ProofLevel
round434EveryClusterPointIsSelectedTargetLevel = machineChecked

round434IndependentTightnessTheoremRequired : Bool
round434IndependentTightnessTheoremRequired = false
