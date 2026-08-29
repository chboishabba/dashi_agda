module DASHI.Physics.YangMills.BalabanReducedGhostPhysicalMatrixLogFifthTailExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Nicholas J. Higham,
-- "Functions of Matrices: Theory and Computation", SIAM, 2008.
-- DOI: 10.1137/1.9780898717778.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Instantiate the exact fifth-order matrix-log tail theorem on the literal
-- anchored reduced Faddeev--Popov relative kernel.  The preceding same-object
-- theorem gives
--
--   rowMass(R_A) <= 104601/524288 < 1/5.
--
-- Hence every finite degree-five-and-higher log majorant with coefficients in
-- [0,1] has row mass <= 1/2500 on the selected background ball.  This is the
-- physical kernel used by the reduced ghost normalization; no abstract matrix
-- contraction is inserted at this step.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (_≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33PhysicalBackgroundGaugeParameterizedYoungExact as Relaxed
import DASHI.Physics.YangMills.BalabanReducedGhostNeumannRowContractionExact as Neumann
import DASHI.Physics.YangMills.BalabanReducedGhostAnchoredRelativeContractionExact as Physical
import DASHI.Physics.YangMills.BalabanReducedGhostMatrixLogFifthTailExact as Tail

physicalAnchoredRelativeRowsBelowOneFifth :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ anchor →
  Neumann.UniformRowBound
    Physical.gaugeRows
    (Physical.anchoredRelativeKernel background anchor)
    Tail.oneFifth
physicalAnchoredRelativeRowsBelowOneFifth background radius anchor row =
  ℚP.≤-trans
    (Physical.anchoredRelativeAbsoluteRowMassBound
      background radius anchor row)
    (ℚP.<⇒≤ Physical.anchoredRelativeContractionBelowOneFifth)

physicalReducedGhostFifthTailUniformCap :
  ∀ background → Relaxed.RelaxedInverseLinkRadius background →
  ∀ anchor (coefficients : Tail.LogTailCoefficients) exponent →
  Neumann.UniformRowBound
    Physical.gaugeRows
    (Tail.finiteFifthTail
      Physical.gaugeRows
      (Physical.anchoredRelativeKernel background anchor)
      coefficients exponent)
    Tail.fifthTailCap
physicalReducedGhostFifthTailUniformCap
    background radius anchor coefficients exponent =
  Tail.finiteFifthTailUniformCap
    Physical.gaugeRows
    (Physical.anchoredRelativeKernel background anchor)
    coefficients exponent
    (physicalAnchoredRelativeRowsBelowOneFifth background radius anchor)

physicalReducedGhostMatrixLogFifthTailLevel : ProofLevel
physicalReducedGhostMatrixLogFifthTailLevel = machineChecked
