module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact where

------------------------------------------------------------------------
-- ROUND78: TOP-DOWN CLAY FRONTIER
--
-- This is deliberately NOT another historical leaf-count decrement.
-- Starting from the literal Clay endpoint, the remaining genuinely independent
-- analytic theorem roles are three:
--
--   A. UV_TO_CONTINUUM_YM
--      Construct the same source-native finite-cutoff Yang--Mills family through
--      all scales and its OS-compatible continuum limit, with the required
--      asymptotically-free short-distance normalization.
--
--   B. SAME_H_PHYSICAL_MASS_GAP
--      On the Hamiltonian reconstructed from THAT continuum family, prove a
--      strictly positive finite physical gap, uniformly inherited from the
--      same-density finite-cutoff construction (equivalently via sufficiently
--      strong uniform exponential clustering plus OS reconstruction).
--
--   C. SAME_FAMILY_LOCAL_FIELDS
--      On THAT continuum family construct gauge-invariant curvature local
--      fields, a quantitative OPE, and a conserved stress tensor whose T_00
--      generates the SAME reconstructed Hamiltonian, with the exact Ward/locality
--      structure needed by the Gaussian reductio.
--
-- Round77 showed that nontriviality is downstream of B+C plus standard
-- Gaussian OS/Fock and spectral theory on the SAME physical Hamiltonian.  It is
-- therefore not a fourth independent nonperturbative estimate.
--
-- IMPORTANT: the five Round77 jobs remain useful INTERNAL sufficient lemmas.
-- They are not five independent Clay-facing endpoints:
--
--   selected-background five-block estimate  --\
--   literal Wilson+FP+Haar one-loop scalar    ---+--> A
--   strong physical one-step RG estimate      --/
--   same-density heat/Langevin clustering     -------> B
--   composite OPE/stress/Ward closure         -------> C
--
-- This top-down recut also prevents over-fitting the proof to convenience
-- constants.  The literal endpoint needs a genuine contraction q<1, a genuine
-- positive physical clustering/gap rate m>0, and a vanishing OPE remainder
-- modulus.  Particular current targets such as 17/32, 55/18874368, or one
-- chosen clustering exponent are SUFFICIENT quantitative certificates, not
-- themselves Clay requirements.  They should be retained only where they make
-- the source-native proof easiest.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five

------------------------------------------------------------------------
-- A. One theorem from literal finite-cutoff YM through the accepted continuum
-- theory.  The old weak-RG and continuum roles are components of ONE theorem on
-- the same construction Y, not independent endpoint analyses.
------------------------------------------------------------------------

record UVToContinuumYM
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    weakCouplingRG : Five.LiteralWeakCouplingRGConstruction Y
    continuumYM : Five.UnifiedContinuumYMConstruction Y
open UVToContinuumYM public

------------------------------------------------------------------------
-- B. Physical positive gap on the SAME reconstructed Hamiltonian.
------------------------------------------------------------------------

record SameHamiltonianPhysicalMassGap
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    physicalGap : Five.CutoffUniformPhysicalMassGap Y
open SameHamiltonianPhysicalMassGap public

------------------------------------------------------------------------
-- C. Local curvature fields / OPE / stress / Ward on the SAME continuum.
------------------------------------------------------------------------

record SameFamilyLocalFieldsOPEStressWard
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    localFields : Five.ContinuumLocalFieldOPEStressWard Y
open SameFamilyLocalFieldsOPEStressWard public

------------------------------------------------------------------------
-- Standard consequence, not a fourth new YM estimate.
--
-- Round77 opens the concrete route:
--   hypothetical Gaussian + local O(4) two-derivative Ward kernel
--   -> m^2=0, Z+Y=0, Z=1
--   -> Maxwell quadratic kernel
--   -> gauge-invariant Gaussian Maxwell sector with spectrum accumulating at 0
--   -> contradiction with B on the SAME H.
--
-- This abstract weld only records the endpoint dependency at the literal-Y
-- layer.  Its concrete realization must be the Round77 same-H bridge, not an
-- unrelated nontriviality assumption.
------------------------------------------------------------------------

record StandardSameHGaussianNontrivialityConsequence
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    deriveInteracting :
      Five.CutoffUniformPhysicalMassGap Y →
      Five.ContinuumLocalFieldOPEStressWard Y →
      Five.InteractingContinuumNontriviality Y
open StandardSameHGaussianNontrivialityConsequence public

------------------------------------------------------------------------
-- Literal Clay compiler from the THREE analytic endpoint theorems plus
-- structural endpoint data and the standard same-H Gaussian consequence.
------------------------------------------------------------------------

literalClaySolutionFromTopDownThree :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  Five.LiteralClayStructuralBase Y →
  UVToContinuumYM Y →
  SameHamiltonianPhysicalMassGap Y →
  SameFamilyLocalFieldsOPEStressWard Y →
  StandardSameHGaussianNontrivialityConsequence Y →
  Clay.ClayYangMillsSolution (Top.literalClayVocabulary Y)
literalClaySolutionFromTopDownThree Y structural uv gap local standard =
  Five.literalClaySolutionFromFiveTheorems
    Y
    structural
    (weakCouplingRG uv)
    (physicalGap gap)
    (continuumYM uv)
    (localFields local)
    (deriveInteracting standard (physicalGap gap) (localFields local))

round78IndependentClayAnalyticEndpointCount : Nat
round78IndependentClayAnalyticEndpointCount = 3

round78TopDownCompilerLevel : ProofLevel
round78TopDownCompilerLevel = machineChecked

-- Concrete physical inhabitants of A/B/C remain the actual research frontier.
round78PhysicalThreeTheoremInstantiationLevel : ProofLevel
round78PhysicalThreeTheoremInstantiationLevel = conditional

-- The same-H Gaussian consequence is standard spectral/free-field mathematics
-- only after its hypotheses are instantiated on the literal continuum Y; the
-- Round77 concrete bridge is the intended implementation.
round78StandardSameHNontrivialityConsequenceLevel : ProofLevel
round78StandardSameHNontrivialityConsequenceLevel = standardImported
