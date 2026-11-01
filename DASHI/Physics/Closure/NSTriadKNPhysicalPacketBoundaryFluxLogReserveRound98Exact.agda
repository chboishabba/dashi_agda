module DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxLogReserveRound98Exact where

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
-- ROUND98 / PHYSICAL PACKET BOUNDARY-FLUX LOG-RESERVE WELD
--
-- On the literal projected finite Galerkin equation, pair every selected
-- retained mode with u_k and sum over the literal cutoff. Round98's selected
-- F4 theorem identifies the nonlinear side with the correctly normalized
-- Round96 boundary flux:
--
--   E'_P + D_P = (1/6) sumBoundaryTransfer.
--
-- The factor 1/6 is forced by Round38/Round39: Round96 sums all three energy
-- legs using ordered-pair power, while the actual projected PDE pairing is the
-- raw ordered-incidence fold. There is no hidden convention left to choose.
--
-- Round97's exact denominator-free logarithmic algebra then gives
--
--   r(-E'_P) + r F_boundary = r D_P.
--
-- Hence packet-boundary influx is already owned by the -log(E_P) reserve and
-- requires no positive-part occupation/Bony/amplitude tax at this component.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNF4ProjectedOutputPairingRound39Exact as Pairing
import DASHI.Physics.Closure.NSTriadKNPhysicalPacketBoundaryFluxRound96Exact as Round96
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as Selected
import DASHI.Physics.Closure.NSTriadKNPacketLogReserveBoundaryFluxCancellationRound97Exact as LogReserve

F : C3.RealField _
F = Rational.rationalRealField

selectedPairing :
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  Z3.FourierMode → ℚ
selectedPairing selected test value output =
  Round96.selectTransfer (selected output)
    (Pairing.realHermitianPower (test output) (value output))

sumSelectedPairing :
  (Z3.FourierMode → Bool) →
  (Z3.FourierMode → C3.Complex3 F) →
  (Z3.FourierMode → C3.Complex3 F) →
  List Z3.FourierMode → ℚ
sumSelectedPairing selected test value [] = 0ℚ
sumSelectedPairing selected test value (output ∷ rest) =
  selectedPairing selected test value output
  + sumSelectedPairing selected test value rest

record LiteralSelectedProjectedODE
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    (system : Equation.FiniteComplex3GalerkinSystem F E I) : Set where
  field
    equation : Equation.ExactProjectedGalerkinEquation system
    cutoffModeListed : ∀ output →
      Cube._∈_ output (Cube.cutoffModes (Equation.cutoff system)) →
      Equation.modeListed system output

open LiteralSelectedProjectedODE public

literalPacketEnergyDerivative :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system →
  (Z3.FourierMode → Bool) → ℚ
literalPacketEnergyDerivative system ode selected =
  sumSelectedPairing selected
    (Equation.velocity system)
    (Equation.timeDerivative ode)
    (Cube.cutoffModes (Equation.cutoff system))

literalPacketDissipation :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  Equation.ExactProjectedGalerkinEquation system →
  (Z3.FourierMode → Bool) → ℚ
literalPacketDissipation system ode selected =
  sumSelectedPairing selected
    (Equation.velocity system)
    (Equation.viscousTerm ode)
    (Cube.cutoffModes (Equation.cutoff system))

selectedModeProjectedODEPairing :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  (output : Z3.FourierMode) →
  Cube._∈_ output (Cube.cutoffModes (Equation.cutoff system)) →
  selectedPairing selected (Equation.velocity system)
      (Equation.timeDerivative (equation L)) output
    + selectedPairing selected (Equation.velocity system)
      (Equation.viscousTerm (equation L)) output
  ≡ Selected.selectedProjectedOutputPower system selected output
selectedModeProjectedODEPairing system L selected output listed
  with selected output
... | false = solve []
... | true =
  trans
    (sym
      (Pairing.realHermitianPowerAddRight
        (Equation.velocity system output)
        (Equation.timeDerivative (equation L) output)
        (Equation.viscousTerm (equation L) output)))
    (cong
      (Pairing.realHermitianPower (Equation.velocity system output))
      (Equation.projectedODE (equation L) output
        (cutoffModeListed L output listed)))

sumSelectedProjectedODEPairing :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  (outputs : List Z3.FourierMode) →
  (∀ output → Cube._∈_ output outputs →
    Cube._∈_ output (Cube.cutoffModes (Equation.cutoff system))) →
  sumSelectedPairing selected (Equation.velocity system)
      (Equation.timeDerivative (equation L)) outputs
    + sumSelectedPairing selected (Equation.velocity system)
      (Equation.viscousTerm (equation L)) outputs
  ≡ Selected.sumSelectedProjectedPairings system selected outputs
sumSelectedProjectedODEPairing system L selected [] listed = solve []
sumSelectedProjectedODEPairing system L selected (output ∷ rest) listed =
  let
    ht = selectedPairing selected (Equation.velocity system)
      (Equation.timeDerivative (equation L)) output
    hv = selectedPairing selected (Equation.velocity system)
      (Equation.viscousTerm (equation L)) output
    tt = sumSelectedPairing selected (Equation.velocity system)
      (Equation.timeDerivative (equation L)) rest
    tv = sumSelectedPairing selected (Equation.velocity system)
      (Equation.viscousTerm (equation L)) rest
    headBalance = selectedModeProjectedODEPairing
      system L selected output (listed output (Cube.here refl))
    tailBalance = sumSelectedProjectedODEPairing
      system L selected rest
      (λ chosen member → listed chosen (Cube.there member))
  in
  trans
    (solve (ht ∷ hv ∷ tt ∷ tv ∷ []))
    (cong₂ _+_ headBalance tailBalance)

literalSelectedProjectedODEEnergyBalance :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  literalPacketEnergyDerivative system (equation L) selected
    + literalPacketDissipation system (equation L) selected
  ≡ Selected.literalSelectedProjectedPairing system selected
literalSelectedProjectedODEEnergyBalance system L selected =
  sumSelectedProjectedODEPairing
    system L selected
    (Cube.cutoffModes (Equation.cutoff system))
    (λ output member → member)

PhysicalPacketBoundaryFluxIdentification :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  literalPacketEnergyDerivative system (equation L) selected
    + literalPacketDissipation system (equation L) selected
  ≡ Norm.normalizedBoundaryTransfer E I selected
      (Equation.velocity system) (Equation.cutoff system)
PhysicalPacketBoundaryFluxIdentification {E} {I}
    system L selected reality divergenceFree =
  trans
    (literalSelectedProjectedODEEnergyBalance system L selected)
    (Selected.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
      system selected reality divergenceFree)

PhysicalPacketBoundaryFluxLogReserveIdentification :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (L : LiteralSelectedProjectedODE system) →
  (selected : Z3.FourierMode → Bool) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  (packetReciprocal : ℚ) →
  packetReciprocal *
      (- literalPacketEnergyDerivative system (equation L) selected)
    + packetReciprocal *
      Norm.normalizedBoundaryTransfer E I selected
        (Equation.velocity system) (Equation.cutoff system)
  ≡ packetReciprocal *
      literalPacketDissipation system (equation L) selected
PhysicalPacketBoundaryFluxLogReserveIdentification {E} {I}
    system L selected reality divergenceFree packetReciprocal =
  LogReserve.logReserveBoundaryFluxCancellation
    (LogReserve.packet-reciprocal-balance
      (LogReserve.signed-packet-energy-balance
        (literalPacketEnergyDerivative system (equation L) selected)
        (literalPacketDissipation system (equation L) selected)
        (Norm.normalizedBoundaryTransfer E I selected
          (Equation.velocity system) (Equation.cutoff system))
        (PhysicalPacketBoundaryFluxIdentification
          system L selected reality divergenceFree))
      packetReciprocal)

round98PhysicalPacketBoundaryFluxLogReserveIdentificationClosed : Bool
round98PhysicalPacketBoundaryFluxLogReserveIdentificationClosed = true

round98PacketPositiveFluxOccupationTaxDeleted : Bool
round98PacketPositiveFluxOccupationTaxDeleted = true

round98PhysicalPacketBoundaryFluxLogReserveIdentificationClosedIsTrue :
  round98PhysicalPacketBoundaryFluxLogReserveIdentificationClosed ≡ true
round98PhysicalPacketBoundaryFluxLogReserveIdentificationClosedIsTrue = refl
