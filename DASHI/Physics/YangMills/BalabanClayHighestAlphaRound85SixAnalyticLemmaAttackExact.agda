module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound85SixAnalyticLemmaAttackExact where

------------------------------------------------------------------------
-- ROUND85/86: ATTACK THREE OF ROUND84'S SIX LIVE ANALYTIC FAMILIES
--
-- This root deliberately does NOT decrement the strict fail-closed count merely
-- because downstream compilers have improved.  It records the exact stronger
-- physical premises whose proof would justify the research-level reductions.
--
-- L1 / compact-simple beta:
--   classified C_A(G) >= 2, hence C_A(G)*11/24 >= 11/12.
--   `BalabanCompactSimpleFourOrbitHalfRemainderExact` now further compiles FOUR
--   literal joint-orbit interval enclosures with total in [-1/2,1/2] directly
--   into an all-group `UniformBetaEnclosure`.
--
-- L4 / continuum composite field:
--   once the SAME completed composite projection supplies a linear literal
--   source derivative with one Hilbertian test-function modulus and the nuclear
--   topology refines that Hilbert topology, nuclear-continuous distributional
--   field existence is theorem output.  A separate completion receipt is gone.
--
-- L6 / stress charge -- Round86 sharpening:
--
--      local T_{0 nu} + microcausality
--        -> outer-shell commutator vanishes beyond supp(A)
--        -> [Q_R,A] eventually constant
--      + Q_R(A Omega) = [Q_R,A] Omega
--        -> Q_R(A Omega) eventually constant
--        -> exact additive local-core charge.
--
--   There is a second reduction after this.  We no longer require the physical
--   theorem to prove exp(i t Q)=U_OS(t) as an independent global statement.
--   It is enough to prove that the stress charge and OS generator agree on one
--   common core and that both global operators are the self-adjoint closures of
--   those core actions.  `YangMillsStressWardCommonCoreGeneratorExact` then gives
--   Q=H_OS/P and Stone supplies equality of the exponentials downstream.
--
-- PRIMARY LOCAL-CHARGE CALIBRATION
--
-- Manfred Requardt,
-- "Symmetry Conservation and Integrals over Local Charge Densities in Quantum
-- Field Theory", Communications in Mathematical Physics 50 (1976), 259--263.
-- DOI: 10.1007/BF01609406.
--
-- Giovanni Morchio and Franco Strocchi,
-- "Charge density and electric charge in quantum electrodynamics",
-- Journal of Mathematical Physics 44 (2003), 5569--5587.
-- DOI: 10.1063/1.1623928. arXiv: hep-th/0301111.
--
-- IMPORTANT ATTRIBUTION CORRECTION
-- The 1976 paper is by Requardt, not Buchholz--Fredenhagen.  Neither source is
-- promoted into a proof of the literal nonperturbative Yang--Mills stress field.
--
-- STRICT SCOREBOARD REMAINS
--
--   5 endpoint packages
--   6 fail-closed physical analytic lemma families
--
-- Research planning can treat L4 as downstream of a strengthened L2, yielding
-- the five-theorem cutset, but this source root remains conservative until that
-- stronger physical L2 inhabitant actually exists.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound84SixAnalyticLemmaExact
import DASHI.Physics.YangMills.BalabanCompactSimpleUniversalBetaFloorExact
import DASHI.Physics.YangMills.BalabanCompactSimpleFourOrbitHalfRemainderExact
import DASHI.Physics.YangMills.BalabanMarkedSourceNuclearCompositeFieldExact
import DASHI.Physics.YangMills.YangMillsStressChargeLocalCoreCutoffStabilizationExact
import DASHI.Physics.YangMills.YangMillsLocalChargeCommutatorToCoreStabilizationExact
import DASHI.Physics.YangMills.YangMillsLocalCurrentMicrocausalShellExact
import DASHI.Physics.YangMills.YangMillsLocalCoreChargeLinearityExact
import DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact
import DASHI.Physics.YangMills.YangMillsStressWardStoneGeneratorBridgeExact

round85IndependentPackageCount : Nat
round85IndependentPackageCount = 5

round85HardAnalyticLemmaUpperCount : Nat
round85HardAnalyticLemmaUpperCount = 6

------------------------------------------------------------------------
-- REFINED LIVE PHYSICAL LEAVES
------------------------------------------------------------------------

-- L1: the post-evaluation arithmetic is now finished.  Physical work is the
-- SAME literal Wilson/reduced-FP/Haar Ward scalar + C_A factorization + four
-- joint regular orbit interval evaluations inside the common half-radius budget.
literalWilsonFPHaarFourJointOrbitHalfEnclosuresLevel : ProofLevel
literalWilsonFPHaarFourJointOrbitHalfEnclosuresLevel = conditional

-- L2 remains the common physical marked-coordinate theorem.  For the L2->L4
-- fusion it must additionally expose the completed composite projection, linear
-- source derivative and one cutoff-independent Hilbertian test modulus.
physicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel : ProofLevel
physicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel = conditional

-- L3 unchanged: same-density continuous heat shell debt <= marked RG shell debt.
physicalPerShellHeatHessianDebtLevel : ProofLevel
physicalPerShellHeatHessianDebtLevel = conditional

-- L4 is conditional only because the preceding physical marked theorem has not
-- yet been shown to instantiate the new same-family nuclear-field compiler.
sameFamilyCompositeFieldInputDataLevel : ProofLevel
sameFamilyCompositeFieldInputDataLevel = conditional

-- L5 unchanged: physical product/OPE identification and AF coefficient matching.
sameFamilyOPEAndAsymptoticFreedomMatchingLevel : ProofLevel
sameFamilyOPEAndAsymptoticFreedomMatchingLevel = conditional

-- L6 after Round86: construct the local renormalized stress/Ward action on the
-- SAME reconstructed local core, prove agreement there with the OS generator,
-- and prove the required essential-self-adjoint/common-core closure facts.
-- Shell cutoff removal, additivity, global generator equality and exponentials
-- are downstream.
physicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel : ProofLevel
physicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel = conditional

------------------------------------------------------------------------
-- THEOREM-BEARING DOWNSTREAM REDUCTIONS
------------------------------------------------------------------------

compactSimpleUniversalCasimirFloorLevel : ProofLevel
compactSimpleUniversalCasimirFloorLevel = machineChecked

compactSimpleUniversalBetaFloorLevel : ProofLevel
compactSimpleUniversalBetaFloorLevel = machineChecked

fourOrbitHalfToAllGroupPositiveBetaLevel : ProofLevel
fourOrbitHalfToAllGroupPositiveBetaLevel = machineChecked

markedSourceToNuclearCompositeFieldCompilerLevel : ProofLevel
markedSourceToNuclearCompositeFieldCompilerLevel = machineChecked

microcausalOuterShellCompilerLevel : ProofLevel
microcausalOuterShellCompilerLevel = machineChecked

localCommutatorToCoreStabilizationLevel : ProofLevel
localCommutatorToCoreStabilizationLevel = machineChecked

stressChargeLocalCoreCutoffRemovalLevel : ProofLevel
stressChargeLocalCoreCutoffRemovalLevel = machineChecked

stabilizedChargeAdditivityCompilerLevel : ProofLevel
stabilizedChargeAdditivityCompilerLevel = machineChecked

commonCoreClosureEqualityCompilerLevel : ProofLevel
commonCoreClosureEqualityCompilerLevel = machineChecked

stoneExponentialsAfterGeneratorEqualityLevel : ProofLevel
stoneExponentialsAfterGeneratorEqualityLevel = standardImported

-- No Clay solution inhabitant is asserted by this root.
------------------------------------------------------------------------
