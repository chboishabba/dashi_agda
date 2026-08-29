module DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact where

------------------------------------------------------------------------
-- ROUND87: THE LITERAL CLAY STRESS/OPE REQUIREMENT DOES NOT REQUIRE
--          A SEPARATE STRESS-CHARGE = HAMILTONIAN THEOREM
--
-- PRIMARY SOURCE
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- The problem description requires local gauge-invariant curvature-polynomial
-- quantum fields whose short-distance correlation functions agree with
-- asymptotic freedom / perturbative renormalization; the listed predictions
-- include a stress tensor and operator product expansion.  It separately asks
-- for a positive-energy reconstructed quantum theory and a positive mass gap.
--
-- MATHEMATICAL ROLE
--
-- Earlier DASHI endgame roots strengthened the stress requirement to
--
--        integral T_00 = the SAME reconstructed Hamiltonian
--
-- via a local-core charge, essential self-adjointness and Stone uniqueness.
-- That is a valuable theorem, but it is stronger than the literal
-- `stressTensorAndOperatorProductExpansion` postcondition in the repository's
-- Jaffe--Witten contract.
--
-- This module makes the exact contract boundary theorem-bearing.  To inhabit
-- the stress/OPE Clay postcondition one needs exactly:
--
--   * a stress tensor on the same Schwinger family;
--   * physical OPE coefficients;
--   * physical OPE remainders.
--
-- No stress-charge cutoff limit, common-core generator equality, essential
-- self-adjointness or equality of exponentials is consumed by this constructor.
-- Those remain optional stronger local-QFT results.
------------------------------------------------------------------------

open import Data.Product using (_×_; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayProblemContractExact as Clay
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record LiteralClayStressOPEEvidence
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    stressAndOPE : ∀ G →
      Top.HasStressTensorAndOPE S G
        (Top.schwinger Y G) (Top.stressTensor Y G)

    physicalOPECoefficient : ∀ G left right output position →
      Top.IsPhysicalOPECoefficient S G left right output position
        (Top.opeCoefficient Y G left right output position)

    physicalOPERemainder : ∀ G left right position depth →
      Top.IsPhysicalOPERemainder S G left right position depth
        (Top.opeRemainder Y G left right position depth)

open LiteralClayStressOPEEvidence public

literalStressOPEEvidenceIsClayPostcondition :
  ∀ {C S} (Y : Top.LiteralYangMillsConstruction C S) →
  LiteralClayStressOPEEvidence Y →
  Top.postconditionRequirement Y Clay.stressTensorAndOperatorProductExpansion
literalStressOPEEvidenceIsClayPostcondition Y evidence G =
  stressAndOPE evidence G ,
  (physicalOPECoefficient evidence G , physicalOPERemainder evidence G)

literalClayStressOPEBoundaryLevel : ProofLevel
literalClayStressOPEBoundaryLevel = machineChecked

-- The stronger charge/generator theorem remains useful, but is not an input to
-- `literalStressOPEEvidenceIsClayPostcondition`.
stressChargeGeneratorIdentificationIsOptionalStrengtheningLevel : ProofLevel
stressChargeGeneratorIdentificationIsOptionalStrengtheningLevel = standardImported
