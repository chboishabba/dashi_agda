module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound85SixAnalyticLemmaAttackExact where

------------------------------------------------------------------------
-- ROUND85/86: ATTACK THE SHORTEST CLAY ANALYTIC FRONTIER
--
-- This root deliberately does NOT decrement the strict fail-closed count merely
-- because downstream compilers have improved.  It records the exact stronger
-- physical premises whose proof would justify the research-level reductions.
--
-- L1 / compact-simple beta:
--   classified C_A(G) >= 2, hence C_A(G)*11/24 >= 11/12.
--   `BalabanCompactSimpleFourOrbitHalfRemainderExact` compiles FOUR literal
--   joint-orbit interval enclosures with total in [-1/2,1/2] directly into an
--   all-group `UniformBetaEnclosure`.
--
-- L2/L4 / composite field:
--   once the SAME completed composite projection supplies a linear literal
--   source derivative with one Hilbertian test-function modulus and the nuclear
--   topology refines that Hilbert topology, nuclear-continuous distributional
--   field existence is theorem output.  A separate completion receipt is gone.
--
-- L5 / OPE coefficient matching -- Round86 sharpening:
--   the physical coefficient does not need to be compared independently with
--   the AF coefficient at every RG depth.  If both satisfy the SAME deterministic
--   one-step operator-mixing recursion and have the SAME UV normalization,
--   `BalabanOPECoefficientRGRecurrenceUniquenessExact` proves equality at every
--   depth by induction.  The remaining OPE physics is same-family product/tail
--   identification + one-step coefficient-law identification + UV normalization.
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
--   We also no longer require exp(i t Q)=U_OS(t) as an independent physical
--   statement.  Common-core equality of the stress charge and OS generator,
--   plus the self-adjoint closure/core facts, gives global generator equality;
--   Stone then gives equality of exponentials downstream.
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
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact
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

-- L1: post-evaluation arithmetic is finished.  Physical work is the SAME literal
-- Wilson/reduced-FP/Haar Ward scalar + C_A factorization + four joint regular
-- orbit interval evaluations inside the common half-radius budget.
literalWilsonFPHaarFourJointOrbitHalfEnclosuresLevel : ProofLevel
literalWilsonFPHaarFourJointOrbitHalfEnclosuresLevel = conditional

-- L2: common physical marked-coordinate theorem.  For L2->L4 fusion it must
-- additionally expose the completed composite projection, linear source
-- derivative and one cutoff-independent Hilbertian test modulus.
physicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel : ProofLevel
physicalMarkedCoordinateRadiusProjectionAndCompositeHilbertModulusLevel = conditional

-- L3: same-density continuous heat shell debt <= marked RG shell debt.
physicalPerShellHeatHessianDebtLevel : ProofLevel
physicalPerShellHeatHessianDebtLevel = conditional

-- L4: conditional only because L2 has not yet instantiated the same-family
-- nuclear-field compiler.
sameFamilyCompositeFieldInputDataLevel : ProofLevel
sameFamilyCompositeFieldInputDataLevel = conditional

-- L5 after Round86: prove the physical product remainder is the same composite
-- marked tail, and prove the literal coefficient coordinate obeys the SAME
-- one-step mixing recurrence/UV normalization as the AF coefficient.  All-depth
-- coefficient equality and geometric remainder decay are downstream.
physicalSameFamilyOPEProductAndOneStepAFIdentificationLevel : ProofLevel
physicalSameFamilyOPEProductAndOneStepAFIdentificationLevel = conditional

-- L6 after Round86: construct local renormalized stress/Ward action on the SAME
-- reconstructed local core, prove agreement there with the OS generator, and
-- prove the essential-self-adjoint/common-core closure facts.
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

coefficientRGRecurrenceUniquenessLevel : ProofLevel
coefficientRGRecurrenceUniquenessLevel = machineChecked

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
