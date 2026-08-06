module DASHI.Physics.YangMills.BalabanP33WreathBlockSpinCrossPollinationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John D. Dixon and Brian Mortimer,
-- "Permutation Groups".
-- DOI: 10.1007/978-1-4612-0731-3.
--
-- Volodymyr Nekrashevych,
-- "Self-Similar Groups".
-- DOI: 10.1090/surv/117.
--
-- Tadeusz Balaban,
-- "Propagators and Renormalization Transformations for Lattice Gauge
-- Theories. II".
-- DOI: 10.1007/BF01240221.
--
-- DASHI CONTRIBUTION
-- Interpret a block-spin assignment as local fine data indexed by coarse
-- sites, with local transformations and coarse-index permutations acting
-- together.  The executable two-site tri-state witness is imported from the
-- common wreath-style module.  No identification with the actual SU(2) gauge
-- action or Balaban block map is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Common.FiniteWreathRefinementExact as Wreath
import DASHI.Physics.Common.SeparatingProbeFamilyExact as Probe

BlockSpinAssignment : Set
BlockSpinAssignment = Wreath.Assignment

prototypeBlockSpinAction : BlockSpinAssignment → BlockSpinAssignment
prototypeBlockSpinAction = Wreath.localPermutationStep

prototypeBlockSpinActionTwiceAt :
  ∀ assignment site →
  prototypeBlockSpinAction (prototypeBlockSpinAction assignment) site
  ≡ assignment site
prototypeBlockSpinActionTwiceAt = Wreath.localPermutationStepTwiceAt

data BlockSpinProbe : Set where
  leftBlockProbe : BlockSpinProbe
  rightBlockProbe : BlockSpinProbe

probeBlockSpin : BlockSpinProbe → BlockSpinAssignment → Wreath.TriState
probeBlockSpin leftBlockProbe assignment = assignment Wreath.leftSite
probeBlockSpin rightBlockProbe assignment = assignment Wreath.rightSite

record WreathBlockSpinBoundary : Set where
  constructor wreathBlockSpinBoundary
  field
    prototypeIsActualGaugeTransformation : Set
    prototypeIsNotActualGaugeTransformation :
      prototypeIsActualGaugeTransformation → Set

    prototypeIsActualRGBlockingMap : Set
    prototypeIsNotActualRGBlockingMap :
      prototypeIsActualRGBlockingMap → Set

    physicalStencilAndIncidenceStillRequired : Set
    physicalStencilAndIncidenceStillRequiredWitness :
      physicalStencilAndIncidenceStillRequired

canonicalWreathBlockSpinBoundary : WreathBlockSpinBoundary
canonicalWreathBlockSpinBoundary =
  wreathBlockSpinBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
    ⊤ tt
  where
  open import Data.Empty using (⊥)
  open import Data.Unit using (⊤; tt)
