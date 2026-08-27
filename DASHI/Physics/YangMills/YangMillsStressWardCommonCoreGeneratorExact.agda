module DASHI.Physics.YangMills.YangMillsStressWardCommonCoreGeneratorExact where

------------------------------------------------------------------------
-- ROUND86: COMMON-CORE WARD ACTION -> SAME SELF-ADJOINT OS GENERATOR
--
-- STANDARD FUNCTIONAL-ANALYSIS CALIBRATION
--
-- Michael Reed and Barry Simon,
-- "Methods of Modern Mathematical Physics I: Functional Analysis",
-- Academic Press, revised edition.
-- DOI: 10.1016/B978-0-12-585001-8.X5001-6.
--
-- Marshall H. Stone,
-- "On One-Parameter Unitary Groups in Hilbert Space",
-- Annals of Mathematics 33 (1932), 643--648.
-- DOI: 10.2307/1968538.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- MATHEMATICAL REDUCTION
--
-- Round84/85 asked the physical stress theorem to prove
--
--       exp(i t Q_nu) = U_OS(t e_nu)
--
-- on the reconstructed Hilbert space and then invoked Stone uniqueness.  That
-- is stronger than necessary if Ward theory already works on a common operator
-- core.  The shorter route is:
--
--   * construct the local-core charge action q;
--   * identify the OS generator's restriction h on the SAME core;
--   * prove q psi = h psi for every core vector psi;
--   * prove both global operators are the self-adjoint closures of these core
--     actions (essential self-adjointness/core property).
--
-- Equality of the core actions then gives equality of their closures.  Equality
-- of the exponentiated groups is a consequence, not a separate physical input.
--
-- We formalize the closure operation abstractly.  This does not pretend to prove
-- essential self-adjointness: identifying the physical Q and H_OS with these
-- closures remains exactly the operator-theoretic part of the YM stress theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl; cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record CommonCoreClosureCalculus : Set₁ where
  field
    Core Vector Operator : Set
    close : (Core → Vector) → Operator

open CommonCoreClosureCalculus public

record StressOSCommonCoreData
    (C : CommonCoreClosureCalculus) : Set₁ where
  field
    stressCoreAction : Core C → Vector C
    osCoreAction : Core C → Vector C

    stressOperator osHamiltonian : Operator C

    -- Function equality is the extensional common-core Ward identity.  A
    -- pointwise Ward theorem may be promoted to this equality by ordinary
    -- function extensionality in the ambient formalization.
    commonCoreActionEquality : stressCoreAction ≡ osCoreAction

    stressIsClosureOfCoreAction :
      stressOperator ≡ close C stressCoreAction

    osHamiltonianIsClosureOfCoreAction :
      osHamiltonian ≡ close C osCoreAction

open StressOSCommonCoreData public

commonCoreWardImpliesSameGenerator :
  (C : CommonCoreClosureCalculus) →
  (dataSet : StressOSCommonCoreData C) →
  stressOperator dataSet ≡ osHamiltonian dataSet
commonCoreWardImpliesSameGenerator C dataSet =
  trans
    (stressIsClosureOfCoreAction dataSet)
    (trans
      (cong (close C) (commonCoreActionEquality dataSet))
      (sym (osHamiltonianIsClosureOfCoreAction dataSet)))

record SameGeneratorConclusion
    (C : CommonCoreClosureCalculus)
    (dataSet : StressOSCommonCoreData C) : Set where
  field
    stressChargeEqualsOSHamiltonian :
      stressOperator dataSet ≡ osHamiltonian dataSet

open SameGeneratorConclusion public

sameGeneratorConclusion :
  (C : CommonCoreClosureCalculus) →
  (dataSet : StressOSCommonCoreData C) →
  SameGeneratorConclusion C dataSet
sameGeneratorConclusion C dataSet = record
  { stressChargeEqualsOSHamiltonian =
      commonCoreWardImpliesSameGenerator C dataSet
  }

commonCoreClosureEqualityCompilerLevel : ProofLevel
commonCoreClosureEqualityCompilerLevel = machineChecked

functionExtensionalityFromPointwiseWardLevel : ProofLevel
functionExtensionalityFromPointwiseWardLevel = standardImported

selfAdjointClosureCoreUniquenessLevel : ProofLevel
selfAdjointClosureCoreUniquenessLevel = standardImported

stoneExponentialsAfterGeneratorEqualityLevel : ProofLevel
stoneExponentialsAfterGeneratorEqualityLevel = standardImported

-- Sharpened physical L6 boundary:
--
--   renormalized local T_{mu nu}
--   + translation Ward identity on the SAME reconstructed local core
--   + local-current/microcausal shell construction (Round86 downstream)
--   + essential self-adjointness / common-core closure identification
--   ---------------------------------------------------------------
--   Q_nu = H_OS/P_nu by this compiler;
--   equality of unitary translations follows downstream.
--
-- Thus `exp(i t Q)=U_OS(t)` is no longer a required independent physical lemma.
physicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel : ProofLevel
physicalStressWardCommonCoreAndEssentialSelfAdjointnessLevel = conditional
