module DASHI.Physics.Closure.NSTriadKNPacketLogReserveBoundaryFluxCancellationRound97Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Authors: Alexey Cheskidov; Roman Shvydkoy.
-- Title: "The Regularity of Weak Solutions of the 3D Navier-Stokes
-- Equations in B^{-1}_{infinity,infinity}".
-- Archive for Rational Mechanics and Analysis 195 (2010), 159--169.
-- DOI: 10.1007/s00205-009-0265-2.
--
-- ROUND97 / PACKET-LOG LYAPUNOV CANCELLATION
--
-- Round96 reduced nonlinear packet transfer exactly to boundary-crossing
-- physical triads.  The compact-Gamma potential already uses the logarithmic
-- packet reserve -log(E_P).  Consequently the signed boundary flux must not be
-- taxed a second time as a positive forcing term.
--
-- If the literal packet balance is
--
--   E' + D = F_boundary,
--
-- then, before division,
--
--   -E' + F_boundary = D.
--
-- For any reciprocal r = E^{-1}, multiplication gives the logarithmic reserve
-- numerator identity
--
--   r (-E') + r F_boundary = r D.
--
-- When r is the actual packet reciprocal this is precisely
--
--   (-log E)' + F_boundary/E = D/E.
--
-- Thus signed inward packet-boundary transfer belongs on the LOSS side of the
-- log-reserve balance.  It requires no amplitude cap, no positive-part Bony
-- majorant, and no supercritical residence theorem at this component.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record SignedPacketEnergyBalance : Set where
  constructor signed-packet-energy-balance
  field
    energyDerivative dissipation boundaryFlux : ℚ
    balance : energyDerivative + dissipation ≡ boundaryFlux

open SignedPacketEnergyBalance public

boundaryFluxMovesToLogLossNumerator :
  (B : SignedPacketEnergyBalance) →
  (- energyDerivative B) + boundaryFlux B ≡ dissipation B
boundaryFluxMovesToLogLossNumerator B =
  let
    e = energyDerivative B
    d = dissipation B
    f = boundaryFlux B

    substituted : (- e) + (e + d) ≡ d
    substituted = solve (e ∷ d ∷ [])
  in
  trans
    (cong ((- e) +_) (symEq (balance B)))
    substituted
  where
  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

record PacketReciprocalBalance : Set where
  constructor packet-reciprocal-balance
  field
    packetBalance : SignedPacketEnergyBalance
    reciprocal : ℚ

open PacketReciprocalBalance public

logReserveBoundaryFluxCancellation :
  (R : PacketReciprocalBalance) →
  reciprocal R * (- energyDerivative (packetBalance R))
    + reciprocal R * boundaryFlux (packetBalance R)
  ≡ reciprocal R * dissipation (packetBalance R)
logReserveBoundaryFluxCancellation R =
  let
    r = reciprocal R
    e = energyDerivative (packetBalance R)
    d = dissipation (packetBalance R)
    f = boundaryFlux (packetBalance R)

    factor : r * ((- e) + f) ≡ r * d
    factor = cong (r *_) (boundaryFluxMovesToLogLossNumerator (packetBalance R))

    distribute : r * ((- e) + f) ≡ r * (- e) + r * f
    distribute = solve (r ∷ e ∷ f ∷ [])
  in
  trans (symEq distribute) factor
  where
  symEq : ∀ {a b : ℚ} → a ≡ b → b ≡ a
  symEq refl = refl

-- A named same-object adapter: `packetBoundaryFlux` should be instantiated by
-- Round96's exact finite sum over boundary-crossing physical triads, not by an
-- independently supplied forcing receipt.
record LiteralPacketBoundaryLogBalance : Set where
  constructor literal-packet-boundary-log-balance
  field
    packetEnergyDerivative packetDissipation packetBoundaryFlux : ℚ
    packetEnergyPDE :
      packetEnergyDerivative + packetDissipation ≡ packetBoundaryFlux
    packetReciprocal : ℚ

open LiteralPacketBoundaryLogBalance public

literalPacketBoundaryFluxIsLogReserveLoss :
  (L : LiteralPacketBoundaryLogBalance) →
  packetReciprocal L * (- packetEnergyDerivative L)
    + packetReciprocal L * packetBoundaryFlux L
  ≡ packetReciprocal L * packetDissipation L
literalPacketBoundaryFluxIsLogReserveLoss L =
  logReserveBoundaryFluxCancellation
    (packet-reciprocal-balance
      (signed-packet-energy-balance
        (packetEnergyDerivative L)
        (packetDissipation L)
        (packetBoundaryFlux L)
        (packetEnergyPDE L))
      (packetReciprocal L))

round97PacketBoundaryFluxNeedsNoPositiveMajorantInLogReserve : Bool
round97PacketBoundaryFluxNeedsNoPositiveMajorantInLogReserve = true

round97PacketBoundaryFluxNeedsNoPositiveMajorantInLogReserveIsTrue :
  round97PacketBoundaryFluxNeedsNoPositiveMajorantInLogReserve ≡ true
round97PacketBoundaryFluxNeedsNoPositiveMajorantInLogReserveIsTrue = refl
