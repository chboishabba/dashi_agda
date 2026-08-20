module DASHI.Physics.Closure.NSTriadKNOffPacketRatioBoundaryFluxCoerciveRound98Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- AMS Chelsea Publishing, 2001 reprint.
-- DOI: 10.1090/chel/343.
--
-- ROUND98 / OFF-PACKET RATIO RECUT AFTER THE PACKET-FLUX WELD
--
-- With
--
--   E = E_P + E_off,       D = D_P + D_off,
--   E'_P + D_P = F,        E' + D = 0,
--
-- the cross-multiplied derivative numerator of R_off = E_off/E is exactly
--
--   E'_off E - E_off E'
--     = -F E + E_off D_P - D_off E_P.
--
-- The total-energy identity is not assumed independently: it is the
-- all-selected instance of the same literal projected Galerkin packet theorem,
-- and its boundary transfer is zero because every incidence is all-in.
--
-- Therefore positive packet influx is favorable for both the packet -log
-- reserve and the off-packet ratio. The surviving ratio physics is packet
-- OUTFLOW plus the spectral cross-dissipation term
--
--   E_off D_P - D_off E_P.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact as Round96
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact as Packet

F : C3.RealField _
F = Rational.rationalRealField

allSelected : Z3.FourierMode → Bool
allSelected _ = true

literalSelectedEnergy :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (selected : Z3.FourierMode → Bool) → ℚ
literalSelectedEnergy system selected =
  Packet.sumSelectedPairing selected
    (Equation.velocity system)
    (Equation.velocity system)
    (Cube.cutoffModes (Equation.cutoff system))

literalTotalEnergy :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I → ℚ
literalTotalEnergy system = literalSelectedEnergy system allSelected

literalOffPacketEnergy :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  Equation.FiniteComplex3GalerkinSystem F E I →
  (Z3.FourierMode → Bool) → ℚ
literalOffPacketEnergy system selected =
  literalTotalEnergy system - literalSelectedEnergy system selected

literalTotalEnergyDerivative :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system → ℚ
literalTotalEnergyDerivative system ode =
  Packet.literalPacketEnergyDerivative system ode allSelected

literalTotalDissipation :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system → ℚ
literalTotalDissipation system ode =
  Packet.literalPacketDissipation system ode allSelected

literalOffPacketEnergyDerivative :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system →
  (Z3.FourierMode → Bool) → ℚ
literalOffPacketEnergyDerivative system ode selected =
  literalTotalEnergyDerivative system ode
  - Packet.literalPacketEnergyDerivative system ode selected

literalOffPacketDissipation :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system →
  (Z3.FourierMode → Bool) → ℚ
literalOffPacketDissipation system ode selected =
  literalTotalDissipation system ode
  - Packet.literalPacketDissipation system ode selected

allSelectedBoundaryTransferZeroOnList :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (items : List Physical.PhysicalTriadIncidence) →
  Round96.sumBoundaryTransfer E I allSelected velocity items ≡ 0ℚ
allSelectedBoundaryTransferZeroOnList E I velocity [] = refl
allSelectedBoundaryTransferZeroOnList E I velocity (tau ∷ rest) =
  allSelectedBoundaryTransferZeroOnList E I velocity rest

allSelectedNormalizedBoundaryFluxZero :
  (E : C3.IntegerEmbedding F) →
  (I : C3.ModeInverseSquare F E) →
  (velocity : Z3.FourierMode → C3.Complex3 F) →
  (cutoff : Nat) →
  Norm.normalizedBoundaryTransfer E I allSelected velocity cutoff ≡ 0ℚ
allSelectedNormalizedBoundaryFluxZero E I velocity cutoff =
  trans
    (cong (Norm.oneSixth *_)
      (allSelectedBoundaryTransferZeroOnList E I velocity
        (Physical.physicalTriadEnumeration cutoff)))
    (solve [])

literalTotalEnergyBalance :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : Packet.LiteralSelectedProjectedODE system) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  literalTotalEnergyDerivative system (Packet.equation L)
    + literalTotalDissipation system (Packet.equation L)
  ≡ 0ℚ
literalTotalEnergyBalance {E} {I} system L reality divergenceFree =
  trans
    (Packet.PhysicalPacketBoundaryFluxIdentification
      system L allSelected reality divergenceFree)
    (allSelectedNormalizedBoundaryFluxZero
      E I (Equation.velocity system) (Equation.cutoff system))

balanceToNegative : ∀ x d → x + d ≡ 0ℚ → x ≡ - d
balanceToNegative x d balance =
  let
    shifted = cong (λ value → value - d) balance
    leftNormalize : (x + d) - d ≡ x
    leftNormalize = solve (x ∷ d ∷ [])
    rightNormalize : 0ℚ - d ≡ - d
    rightNormalize = solve (d ∷ [])
  in
  trans (sym leftNormalize) (trans shifted rightNormalize)

balanceToFluxMinusDissipation : ∀ x d f → x + d ≡ f → x ≡ f - d
balanceToFluxMinusDissipation x d f balance =
  let
    shifted = cong (λ value → value - d) balance
    leftNormalize : (x + d) - d ≡ x
    leftNormalize = solve (x ∷ d ∷ [])
  in
  trans (sym leftNormalize) shifted

literalOffPacketEnergyBalance :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : Packet.LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  literalOffPacketEnergyDerivative system (Packet.equation L) selected
  ≡ - literalOffPacketDissipation system (Packet.equation L) selected
    - Norm.normalizedBoundaryTransfer E I selected
        (Equation.velocity system) (Equation.cutoff system)
literalOffPacketEnergyBalance {E} {I}
    system L selected reality divergenceFree =
  let
    etDot = literalTotalEnergyDerivative system (Packet.equation L)
    dt = literalTotalDissipation system (Packet.equation L)
    epDot = Packet.literalPacketEnergyDerivative system (Packet.equation L) selected
    dp = Packet.literalPacketDissipation system (Packet.equation L) selected
    flux = Norm.normalizedBoundaryTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
    totalMeaning = balanceToNegative etDot dt
      (literalTotalEnergyBalance system L reality divergenceFree)
    packetMeaning = balanceToFluxMinusDissipation epDot dp flux
      (Packet.PhysicalPacketBoundaryFluxIdentification
        system L selected reality divergenceFree)
  in
  trans
    (cong (λ value → value - epDot) totalMeaning)
    (trans
      (cong (λ value → (- dt) - value) packetMeaning)
      (solve (dt ∷ dp ∷ flux ∷ [])))

-- Pure equality-transport proof of the cross-multiplied ratio numerator.
offPacketRatioCrossNumeratorIdentity :
  (totalEnergy packetEnergy offEnergy : ℚ) →
  (totalDerivative packetDerivative : ℚ) →
  (totalDissipation packetDissipation offDissipation flux : ℚ) →
  totalEnergy ≡ packetEnergy + offEnergy →
  totalDissipation ≡ packetDissipation + offDissipation →
  totalDerivative + totalDissipation ≡ 0ℚ →
  packetDerivative + packetDissipation ≡ flux →
  (totalDerivative - packetDerivative) * totalEnergy
    - offEnergy * totalDerivative
  ≡ (- flux) * totalEnergy
    + offEnergy * packetDissipation
    - offDissipation * packetEnergy
offPacketRatioCrossNumeratorIdentity
    totalEnergy packetEnergy offEnergy
    totalDerivative packetDerivative
    totalDissipation packetDissipation offDissipation flux
    energySplit dissipationSplit totalBalance packetBalance
  rewrite balanceToNegative totalDerivative totalDissipation totalBalance
        | balanceToFluxMinusDissipation
            packetDerivative packetDissipation flux packetBalance
        | energySplit
        | dissipationSplit =
  solve (packetEnergy ∷ offEnergy ∷ packetDissipation ∷ offDissipation ∷ flux ∷ [])

PhysicalOffPacketRatioBoundaryFluxCoerciveIdentity :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : Packet.LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  let
    et = literalTotalEnergy system
    ep = literalSelectedEnergy system selected
    eo = literalOffPacketEnergy system selected
    etd = literalTotalEnergyDerivative system (Packet.equation L)
    epd = Packet.literalPacketEnergyDerivative system (Packet.equation L) selected
    dt = literalTotalDissipation system (Packet.equation L)
    dp = Packet.literalPacketDissipation system (Packet.equation L) selected
    doff = literalOffPacketDissipation system (Packet.equation L) selected
    flux = Norm.normalizedBoundaryTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
  in
  (etd - epd) * et - eo * etd
  ≡ (- flux) * et + eo * dp - doff * ep
PhysicalOffPacketRatioBoundaryFluxCoerciveIdentity {E} {I}
    system L selected reality divergenceFree =
  let
    et = literalTotalEnergy system
    ep = literalSelectedEnergy system selected
    eo = literalOffPacketEnergy system selected
    etd = literalTotalEnergyDerivative system (Packet.equation L)
    epd = Packet.literalPacketEnergyDerivative system (Packet.equation L) selected
    dt = literalTotalDissipation system (Packet.equation L)
    dp = Packet.literalPacketDissipation system (Packet.equation L) selected
    doff = literalOffPacketDissipation system (Packet.equation L) selected
    flux = Norm.normalizedBoundaryTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
    energySplit : et ≡ ep + eo
    energySplit = solve (et ∷ ep ∷ [])
    dissipationSplit : dt ≡ dp + doff
    dissipationSplit = solve (dt ∷ dp ∷ [])
  in
  offPacketRatioCrossNumeratorIdentity
    et ep eo etd epd dt dp doff flux
    energySplit dissipationSplit
    (literalTotalEnergyBalance system L reality divergenceFree)
    (Packet.PhysicalPacketBoundaryFluxIdentification
      system L selected reality divergenceFree)

round98OffPacketRatioBoundaryFluxRecutClosed : Bool
round98OffPacketRatioBoundaryFluxRecutClosed = true

round98PositivePacketInfluxIsAdverseOffPacketCost : Bool
round98PositivePacketInfluxIsAdverseOffPacketCost = false

round98OffPacketSurvivingLeavesAreOutflowAndCrossDissipation : Bool
round98OffPacketSurvivingLeavesAreOutflowAndCrossDissipation = true

round98OffPacketRatioBoundaryFluxRecutClosedIsTrue :
  round98OffPacketRatioBoundaryFluxRecutClosed ≡ true
round98OffPacketRatioBoundaryFluxRecutClosedIsTrue = refl
