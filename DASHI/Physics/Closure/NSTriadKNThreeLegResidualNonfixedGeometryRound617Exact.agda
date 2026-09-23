{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNThreeLegResidualNonfixedGeometryRound617Exact where

------------------------------------------------------------------------
-- ROUND617 / R112 NONFIXEDNESS = THREE EXPLICIT MODE DIAGONALS
--
-- R616 reduces the nine-field R112 witness to three swap-nonfixedness proofs.
-- This owner removes the remaining opacity from those proofs.
--
-- For any physical incidence tau:
--
--   swapTriad tau = tau    <->    p_tau = q_tau.
--
-- Applying the same statement to the cyclic energy legs and using their
-- definitional inputs gives:
--
--   swap(pEnergyLeg tau) = pEnergyLeg tau
--     <-> k_tau = -q_tau,
--
--   swap(qEnergyLeg tau) = qEnergyLeg tau
--     <-> k_tau = -p_tau.
--
-- Hence a canonical R112 residual witness can be built from exactly the three
-- explicit nondegeneracy conditions
--
--   p != q,  k != -q,  k != -p.
--
-- The exceptional loci are NOT declared impossible; they remain explicit.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≢_; cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNF4PairNormalizationRound39Exact as R39
import DASHI.Physics.Closure.NSTriadKNExternalWaleffeResidualCarrierRound112Exact as R112
import DASHI.Physics.Closure.NSTriadKNThreeLegResidualMembershipCompilerRound616Exact as R616

------------------------------------------------------------------------
-- Generic swap fixed-point equivalence.
------------------------------------------------------------------------

swapFixedImpliesInputsEqual :
  (tau : Physical.PhysicalTriadIncidence) →
  Symmetry.swapTriad tau ≡ tau →
  Physical.p tau ≡ Physical.q tau
swapFixedImpliesInputsEqual tau fixed =
  trans
    (sym (cong Physical.p fixed))
    (Symmetry.swapTriadP tau)

inputsEqualImpliesSwapFixed :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.p tau ≡ Physical.q tau →
  Symmetry.swapTriad tau ≡ tau
inputsEqualImpliesSwapFixed = R39.swapFixedWhenInputsEqual

swapNonfixedFromInputsDifferent :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.p tau ≢ Physical.q tau →
  Symmetry.swapTriad tau ≢ tau
swapNonfixedFromInputsDifferent tau inputsDifferent fixed =
  inputsDifferent (swapFixedImpliesInputsEqual tau fixed)

inputsDifferentFromSwapNonfixed :
  (tau : Physical.PhysicalTriadIncidence) →
  Symmetry.swapTriad tau ≢ tau →
  Physical.p tau ≢ Physical.q tau
inputsDifferentFromSwapNonfixed tau swapNonfixed inputsEqual =
  swapNonfixed (inputsEqualImpliesSwapFixed tau inputsEqual)

------------------------------------------------------------------------
-- Energy-leg specializations.
------------------------------------------------------------------------

pEnergyLegNonfixedFromModeInequality :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≢ Z3.negateMode (Physical.q tau) →
  Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau
pEnergyLegNonfixedFromModeInequality tau modeDifferent =
  swapNonfixedFromInputsDifferent
    (Orbit.pEnergyLeg tau)
    (λ legInputsEqual →
      modeDifferent
        (trans
          (sym (Orbit.pEnergyLegFirstInput tau))
          (trans legInputsEqual (Orbit.pEnergyLegSecondInput tau))))

qEnergyLegNonfixedFromModeInequality :
  (tau : Physical.PhysicalTriadIncidence) →
  Physical.k tau ≢ Z3.negateMode (Physical.p tau) →
  Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau
qEnergyLegNonfixedFromModeInequality tau modeDifferent =
  swapNonfixedFromInputsDifferent
    (Orbit.qEnergyLeg tau)
    (λ legInputsEqual →
      modeDifferent
        (trans
          (sym (Orbit.qEnergyLegFirstInput tau))
          (trans legInputsEqual (Orbit.qEnergyLegSecondInput tau))))

pEnergyLegModeInequalityFromNonfixed :
  (tau : Physical.PhysicalTriadIncidence) →
  Symmetry.swapTriad (Orbit.pEnergyLeg tau) ≢ Orbit.pEnergyLeg tau →
  Physical.k tau ≢ Z3.negateMode (Physical.q tau)
pEnergyLegModeInequalityFromNonfixed tau nonfixed modeEqual =
  nonfixed
    (inputsEqualImpliesSwapFixed
      (Orbit.pEnergyLeg tau)
      (trans
        (Orbit.pEnergyLegFirstInput tau)
        (trans modeEqual (sym (Orbit.pEnergyLegSecondInput tau)))))

qEnergyLegModeInequalityFromNonfixed :
  (tau : Physical.PhysicalTriadIncidence) →
  Symmetry.swapTriad (Orbit.qEnergyLeg tau) ≢ Orbit.qEnergyLeg tau →
  Physical.k tau ≢ Z3.negateMode (Physical.p tau)
qEnergyLegModeInequalityFromNonfixed tau nonfixed modeEqual =
  nonfixed
    (inputsEqualImpliesSwapFixed
      (Orbit.qEnergyLeg tau)
      (trans
        (Orbit.qEnergyLegFirstInput tau)
        (trans modeEqual (sym (Orbit.qEnergyLegSecondInput tau)))))

------------------------------------------------------------------------
-- R112 constructor with only explicit mode inequalities.
------------------------------------------------------------------------

threeLegResidualMembershipFromModeNondegeneracy :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Audit.FiniteComplex3GalerkinSystem F E I)
    (tau : Physical.PhysicalTriadIncidence) →
  (tauMember : tau ∈ Audit.concreteTriadsAt system (Physical.k tau)) →
  (kDifferent : Physical.p tau ≢ Physical.q tau) →
  (pLegDifferent :
    Physical.k tau ≢ Z3.negateMode (Physical.q tau)) →
  (qLegDifferent :
    Physical.k tau ≢ Z3.negateMode (Physical.p tau)) →
  R112.ThreeLegResidualMembership system tau
threeLegResidualMembershipFromModeNondegeneracy
    system tau tauMember kDifferent pLegDifferent qLegDifferent =
  R616.threeLegResidualMembershipFromOwnFibre
    system tau tauMember
    (swapNonfixedFromInputsDifferent tau kDifferent)
    (pEnergyLegNonfixedFromModeInequality tau pLegDifferent)
    (qEnergyLegNonfixedFromModeInequality tau qLegDifferent)

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round617SwapFixedIffInputDiagonalClosed : Bool
round617SwapFixedIffInputDiagonalClosed = true

round617PEnergyLegFixedIffExplicitModeDiagonalClosed : Bool
round617PEnergyLegFixedIffExplicitModeDiagonalClosed = true

round617QEnergyLegFixedIffExplicitModeDiagonalClosed : Bool
round617QEnergyLegFixedIffExplicitModeDiagonalClosed = true

round617R112WitnessReducedToThreeModeInequalities : Bool
round617R112WitnessReducedToThreeModeInequalities = true

round617ExceptionalLociProvedAbsent : Bool
round617ExceptionalLociProvedAbsent = false

round617IntroducesEstimate : Bool
round617IntroducesEstimate = false

round617SwapFixedIffInputDiagonalClosedIsTrue :
  round617SwapFixedIffInputDiagonalClosed ≡ true
round617SwapFixedIffInputDiagonalClosedIsTrue = refl

round617PEnergyLegFixedIffExplicitModeDiagonalClosedIsTrue :
  round617PEnergyLegFixedIffExplicitModeDiagonalClosed ≡ true
round617PEnergyLegFixedIffExplicitModeDiagonalClosedIsTrue = refl

round617QEnergyLegFixedIffExplicitModeDiagonalClosedIsTrue :
  round617QEnergyLegFixedIffExplicitModeDiagonalClosed ≡ true
round617QEnergyLegFixedIffExplicitModeDiagonalClosedIsTrue = refl

round617R112WitnessReducedToThreeModeInequalitiesIsTrue :
  round617R112WitnessReducedToThreeModeInequalities ≡ true
round617R112WitnessReducedToThreeModeInequalitiesIsTrue = refl

round617ExceptionalLociProvedAbsentIsFalse :
  round617ExceptionalLociProvedAbsent ≡ false
round617ExceptionalLociProvedAbsentIsFalse = refl

round617IntroducesEstimateIsFalse :
  round617IntroducesEstimate ≡ false
round617IntroducesEstimateIsFalse = refl
