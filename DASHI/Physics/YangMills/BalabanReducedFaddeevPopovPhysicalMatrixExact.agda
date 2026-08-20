module DASHI.Physics.YangMills.BalabanReducedFaddeevPopovPhysicalMatrixExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- L. D. Faddeev and V. N. Popov,
-- "Feynman Diagrams for the Yang-Mills Field", Physics Letters B 25 (1967),
-- 29--30. DOI: 10.1016/0370-2693(67)90067-6.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- DASHI CONTRIBUTION
--
-- Put the literal reduced relative ghost perturbation
--
--       R_A = M_A M_0^{-1} - I
--
-- into the explicit finite coordinate matrix used by the fourth-order
-- trace-log jet.  This is the same physical operator constructed in Round61/62,
-- not an abstract matrix variable.  Every basis source is colourwise mean-zero,
-- so the exact identity-background theorem immediately gives
--
--       R_1 = 0
--
-- entry by entry on the complete 765-dimensional reduced carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier using (pair)
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreCarrier as Block
import DASHI.Physics.YangMills.BalabanPath4AxisAverageExact as Path4
import DASHI.Physics.YangMills.BalabanP33PhysicalFlatGaugeDivergenceIdentificationExact as Gauge
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanFiniteRationalMatrixTraceCyclicExact as Matrix
import DASHI.Physics.YangMills.BalabanReducedGhostExplicitTraceCarrierExact as Basis
import DASHI.Physics.YangMills.BalabanReducedGhostOperatorMatrixExact as OperatorMatrix
import DASHI.Physics.YangMills.BalabanReducedFaddeevPopovRelativePerturbationExact as Relative

relativeGhostOperator :
  Physical.RationalSU2Background4 → Block.PhysicalBlockL Path4.side4 →
  Basis.GhostLinearMap
relativeGhostOperator background anchor source coordinate =
  Relative.relativeFaddeevPopovPerturbation
    background anchor source coordinate

relativeGhostMatrix :
  Physical.RationalSU2Background4 → Block.PhysicalBlockL Path4.side4 →
  Matrix.Matrix Gauge.GaugeCoordinate4
relativeGhostMatrix background anchor =
  OperatorMatrix.reducedGhostOperatorMatrix anchor
    (relativeGhostOperator background anchor)

identityRelativeGhostMatrixZero :
  ∀ anchor row column →
  relativeGhostMatrix Physical.identityBackground anchor row column ≡ 0ℚ
identityRelativeGhostMatrixZero
    anchor (pair rowColour rowSite) (pair colour site) =
  Relative.relativeFaddeevPopovIdentityZero
    (Basis.reducedGhostBasisSource anchor colour site)
    anchor
    (Basis.reducedGhostBasisMeanZero anchor colour site)
    rowColour rowSite

relativeGhostPhysicalMatrixLevel : ProofLevel
relativeGhostPhysicalMatrixLevel = machineChecked

identityRelativeGhostPhysicalMatrixZeroLevel : ProofLevel
identityRelativeGhostPhysicalMatrixZeroLevel = machineChecked
