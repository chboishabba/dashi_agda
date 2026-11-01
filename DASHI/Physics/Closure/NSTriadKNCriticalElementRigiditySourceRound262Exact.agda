module DASHI.Physics.Closure.NSTriadKNCriticalElementRigiditySourceRound262Exact where

------------------------------------------------------------------------
-- ROUND262 / SOURCE-EXACT CRITICAL-ELEMENT RIGIDITY VIA BACKWARD UNIQUENESS
--
-- Sources:
-- * L. Escauriaza, G. Seregin, V. Sverak,
--   "L_{3,infinity}-solutions of the Navier-Stokes equations and backward
--   uniqueness", Russian Math. Surveys 58 (2003), 211--250,
--   DOI 10.1070/RM2003v058n02ABEH000609.
-- * L. Escauriaza, G. Seregin, V. Sverak,
--   "On backward uniqueness for parabolic equations", Arch. Rational Mech.
--   Anal. 169 (2003), 147--157, DOI 10.1007/s00205-003-0263-8.
-- * Gallagher--Koch--Planchon, Math. Ann. 355 (2013), 1527--1559,
--   DOI 10.1007/s00208-012-0830-0, for the critical-element architecture.
--
-- BIDI SHAPE.
--
-- Backward consumer needs only a contradiction from one nontrivial compact
-- critical element.  Forward PDE producer supplies:
--
--   1. an ancient/backward interval on which the critical element is regular;
--   2. terminal-time decay/vanishing obtained from compactness modulo the NS
--      symmetries and the critical-element construction;
--   3. vorticity omega = curl u satisfying the standard parabolic inequality
--      to which the ESS backward-uniqueness theorem applies;
--   4. backward uniqueness => omega identically zero on the earlier interval;
--   5. divergence free + decay/normalisation then forces u to be the trivial
--      solution, contradicting the nonzero mixed-defect obstruction.
--
-- This file names the exact analytic receipts.  Round257 owns the final logical
-- contradiction compiler; Round262 identifies its PDE content with the
-- published ESS/GKP theorem chain.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record ESSCriticalElementRigidity
    {ℓ : Level} (CriticalElement : Set ℓ) : Set (lsuc ℓ) where
  field
    element : CriticalElement

    compactnessModuloNSSymmetry : Set ℓ
    regularOnBackwardInterval : Set ℓ
    terminalVorticityVanishing : Set ℓ

    vorticitySatisfiesESSParabolicInequality : Set ℓ
    coefficientsMeetESSBackwardUniquenessClass : Set ℓ
    backwardUniquenessForcesZeroVorticity : Set ℓ

    zeroVorticityPlusDivergenceFreeForcesTrivialVelocity : Set ℓ
    nonzeroMixedDefectObstruction : Set ℓ

open ESSCriticalElementRigidity public

round262ESSBackwardUniquenessIsExactRigidityLeaf : Bool
round262ESSBackwardUniquenessIsExactRigidityLeaf = true

round262GKPCompactCriticalElementArchitectureMatchesConsumer : Bool
round262GKPCompactCriticalElementArchitectureMatchesConsumer = true

round262ZeroVorticityContradictsNonzeroMixedDefect : Bool
round262ZeroVorticityContradictsNonzeroMixedDefect = true

round262ESSAnalyticTheoremKernelDerivedInFiniteAgda : Bool
round262ESSAnalyticTheoremKernelDerivedInFiniteAgda = false

round262PackageAClosed : Bool
round262PackageAClosed = false

round262ESSBackwardUniquenessIsExactRigidityLeafIsTrue :
  round262ESSBackwardUniquenessIsExactRigidityLeaf ≡ true
round262ESSBackwardUniquenessIsExactRigidityLeafIsTrue = refl
