module DASHI.Physics.Closure.NSTriadKNConcreteUpperSquaredPacketRound104Exact where

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
-- ROUND104 / CONCRETE UPPER-FREQUENCY PACKETS
--
-- Round98 proves the literal selected projected Galerkin pairing equals the
-- correctly normalized physical boundary flux for ANY Boolean mode selector.
-- This file removes one remaining selector abstraction: upper-frequency
-- packets are executable predicates on the literal integer lattice using the
-- already-proved exact natural squared norm
--
--   |k|_Nat^2 = kx^2 + ky^2 + kz^2.
--
-- For threshold R2,
--
--   upperSquaredPacket R2 k = true  iff the executable comparison accepts
--                                  R2 <= |k|_Nat^2.
--
-- No square root or dyadic proxy is introduced at this selector stage.  The
-- critical H^(1/2) radial weight may later be represented by an exact real
-- radius or by a quantitatively equivalent dyadic shell norm; that standard
-- norm-identification step remains separate from the packet boundary theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Audit
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Equation
import DASHI.Physics.Closure.NSTriadKNPacketBoundaryFluxNormalizationRound98Exact as Norm
import DASHI.Physics.Closure.NSTriadKNSelectedPacketProjectedPairingRound98Exact as Selected

infix 4 _≤ᵇ_

_≤ᵇ_ : Nat → Nat → Bool
zero ≤ᵇ n = true
suc m ≤ᵇ zero = false
suc m ≤ᵇ suc n = m ≤ᵇ n

upperSquaredPacket : Nat → Z3.FourierMode → Bool
upperSquaredPacket thresholdSquared k =
  thresholdSquared ≤ᵇ ModeNorm.modeNatNormSquared k

zeroThresholdSelectsEveryMode :
  (k : Z3.FourierMode) → upperSquaredPacket zero k ≡ true
zeroThresholdSelectsEveryMode k = refl

F : C3.RealField _
F = Rational.rationalRealField

literalUpperSquaredPacketPairingIsBoundaryFlux :
  {E : C3.IntegerEmbedding F} →
  {I : C3.ModeInverseSquare F E} →
  (system : Equation.FiniteComplex3GalerkinSystem F E I) →
  (thresholdSquared : Nat) →
  Audit.RealityCondition (Equation.velocity system) →
  Audit.DivergenceFreeCondition E (Equation.velocity system) →
  Selected.literalSelectedProjectedPairing
      system (upperSquaredPacket thresholdSquared)
  ≡ Norm.normalizedBoundaryTransfer
      E I (upperSquaredPacket thresholdSquared)
      (Equation.velocity system) (Equation.cutoff system)
literalUpperSquaredPacketPairingIsBoundaryFlux
    system thresholdSquared reality divergenceFree =
  Selected.literalSelectedProjectedPairingIsNormalizedBoundaryFlux
    system (upperSquaredPacket thresholdSquared) reality divergenceFree

round104ConcreteUpperSquaredPacketSelectorClosed : Bool
round104ConcreteUpperSquaredPacketSelectorClosed = true

round104ConcreteUpperSquaredPacketBoundaryFluxClosed : Bool
round104ConcreteUpperSquaredPacketBoundaryFluxClosed = true

round104ConcreteUpperSquaredPacketBoundaryFluxClosedIsTrue :
  round104ConcreteUpperSquaredPacketBoundaryFluxClosed ≡ true
round104ConcreteUpperSquaredPacketBoundaryFluxClosedIsTrue = refl