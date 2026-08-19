module DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Gregory L. Eyink.
-- Title: "Locality of turbulent cascades".
-- Physica D 207 (2005), 91--116.
-- DOI: 10.1016/j.physd.2005.05.018.
--
-- Authors: Gregory L. Eyink; Hussein Aluie.
-- Title: "Localness of energy cascade in hydrodynamic turbulence. I.
-- Smooth coarse graining".
-- Physics of Fluids 21 (2009), 115107.
-- DOI: 10.1063/1.3266883.
--
-- ROUND96 / EXACT PHYSICAL PACKET-BOUNDARY REDUCTION
--
-- Eyink/Aluie calibrate the scale-local flux viewpoint, but no statistical or
-- regularity-dependent locality theorem is imported here.  The theorem below
-- is a finite exact consequence of the repository's literal physical triad
-- energy cancellation.
--
-- Let chi(k) be ANY Boolean packet selector.  For one physical triad tau, sum
-- the three literal ordered-pair energy transfers only on selected legs:
--
--   chi(k) T_k + chi(p) T_p + chi(q) T_q.
--
-- If all three legs are selected, exact three-leg energy conservation makes
-- this zero.  If none are selected, it is definitionally zero.  Consequently
-- the packet transfer from a complete finite physical triad enumeration equals
-- exactly the sum over boundary-crossing triads (those with mixed selector
-- values).  Internal and fully external triads disappear BEFORE any absolute
-- value, positive-part, Bony, or cubic majorization is taken.
--
-- This is the correct source-facing simplification for Round96 external
-- replenishment: only packet-boundary incidences need coefficient-to-charge
-- estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNRationalPhysicalTriadEnergyRound37Exact as TriadEnergy
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as Round38

F : C3.RealField _
F = Rational.rationalRealField

selectTransfer : Bool → ℚ → ℚ
selectTransfer true value = value
selectTransfer false value = 0ℚ

packetTriadTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
packetTriadTransfer E I selected velocity tau =
    selectTransfer (selected (Physical.k tau))
      (Round38.orderedPairPower E I tau velocity)
  + selectTransfer (selected (Physical.p tau))
      (Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity)
  + selectTransfer (selected (Physical.q tau))
      (Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity)

-- Retain exactly the mixed-side interactions.  The all-in and all-out cases
-- are erased before any later majorization.
boundaryTriadTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  Physical.PhysicalTriadIncidence → ℚ
boundaryTriadTransfer E I selected velocity tau
  with selected (Physical.k tau)
     | selected (Physical.p tau)
     | selected (Physical.q tau)
... | true  | true  | true  = 0ℚ
... | false | false | false = 0ℚ
... | sk    | sp    | sq    = packetTriadTransfer E I selected velocity tau

allSelectedTriadPacketTransferZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  selected (Physical.k tau) ≡ true →
  selected (Physical.p tau) ≡ true →
  selected (Physical.q tau) ≡ true →
  packetTriadTransfer E I selected velocity tau ≡ 0ℚ
allSelectedTriadPacketTransferZero E I selected velocity
    reality divergenceFree tau kIn pIn qIn
  rewrite kIn | pIn | qIn =
  trans
    (symThreeLeg E I tau velocity)
    (TriadEnergy.literalPhysicalTriadPowerZero
      E I tau velocity reality divergenceFree)
  where
  symThreeLeg :
    (E : C3.IntegerEmbedding F) →
    (I : C3.ModeInverseSquare F E) →
    (tau : Physical.PhysicalTriadIncidence) →
    (velocity : Z3.FourierMode → C3.Complex3 F) →
    Round38.orderedPairPower E I tau velocity
      + Round38.orderedPairPower E I (Orbit.pEnergyLeg tau) velocity
      + Round38.orderedPairPower E I (Orbit.qEnergyLeg tau) velocity
    ≡ TriadEnergy.literalThreeLegPower E I tau velocity
  symThreeLeg E I tau velocity =
    let
      forward = Round38.threeLegPowerIsPairOrbitSum E I tau velocity
    in
    symEq forward

  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

packetTriadTransferEqualsBoundaryTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (tau : Physical.PhysicalTriadIncidence) →
  packetTriadTransfer E I selected velocity tau
    ≡ boundaryTriadTransfer E I selected velocity tau
packetTriadTransferEqualsBoundaryTransfer
    E I selected velocity reality divergenceFree tau
  with selected (Physical.k tau)
     | selected (Physical.p tau)
     | selected (Physical.q tau)
... | true | true | true =
  allSelectedTriadPacketTransferZero
    E I selected velocity reality divergenceFree tau refl refl refl
... | false | false | false = solve []
... | true | true | false = refl
... | true | false | true = refl
... | false | true | true = refl
... | true | false | false = refl
... | false | true | false = refl
... | false | false | true = refl

sumPacketTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
sumPacketTransfer E I selected velocity [] = 0ℚ
sumPacketTransfer E I selected velocity (tau ∷ rest) =
  packetTriadTransfer E I selected velocity tau
    + sumPacketTransfer E I selected velocity rest

sumBoundaryTransfer :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Physical.PhysicalTriadIncidence → ℚ
sumBoundaryTransfer E I selected velocity [] = 0ℚ
sumBoundaryTransfer E I selected velocity (tau ∷ rest) =
  boundaryTriadTransfer E I selected velocity tau
    + sumBoundaryTransfer E I selected velocity rest

finitePacketTransferIsBoundaryFlux :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (triads : List Physical.PhysicalTriadIncidence) →
  sumPacketTransfer E I selected velocity triads
  ≡ sumBoundaryTransfer E I selected velocity triads
finitePacketTransferIsBoundaryFlux E I selected velocity
    reality divergenceFree [] = refl
finitePacketTransferIsBoundaryFlux E I selected velocity
    reality divergenceFree (tau ∷ rest) =
  cong₂Q _+_
    (packetTriadTransferEqualsBoundaryTransfer
      E I selected velocity reality divergenceFree tau)
    (finitePacketTransferIsBoundaryFlux
      E I selected velocity reality divergenceFree rest)
  where
  cong₂Q :
    (ℚ → ℚ → ℚ) → ∀ {a b c d : ℚ} →
    a ≡ b → c ≡ d → a + c ≡ b + d
  cong₂Q f refl refl = refl

literalCutoffPacketTransferIsBoundaryFlux :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (selected : Z3.FourierMode → Bool) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  Audit.RealityCondition velocity →
  Audit.DivergenceFreeCondition E velocity →
  (cutoff : Agda.Builtin.Nat.Nat) →
  sumPacketTransfer E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
  ≡ sumBoundaryTransfer E I selected velocity
    (Physical.physicalTriadEnumeration cutoff)
literalCutoffPacketTransferIsBoundaryFlux E I selected velocity
    reality divergenceFree cutoff =
  finitePacketTransferIsBoundaryFlux
    E I selected velocity reality divergenceFree
    (Physical.physicalTriadEnumeration cutoff)

round96PhysicalPacketInternalTriadsCancelExactly : Bool
round96PhysicalPacketInternalTriadsCancelExactly = true

round96PhysicalPacketTransferReducedToBoundaryTriads : Bool
round96PhysicalPacketTransferReducedToBoundaryTriads = true

round96BoundaryReductionUsesNoStatisticalLocalityHypothesis : Bool
round96BoundaryReductionUsesNoStatisticalLocalityHypothesis = true

round96PhysicalPacketTransferReducedToBoundaryTriadsIsTrue :
  round96PhysicalPacketTransferReducedToBoundaryTriads ≡ true
round96PhysicalPacketTransferReducedToBoundaryTriadsIsTrue = refl
