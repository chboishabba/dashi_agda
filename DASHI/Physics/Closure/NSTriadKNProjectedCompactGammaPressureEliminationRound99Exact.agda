module DASHI.Physics.Closure.NSTriadKNProjectedCompactGammaPressureEliminationRound99Exact where

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
-- ROUND99 / PROJECTED COMPACT-GAMMA PRESSURE ELIMINATION
--
-- The shortest compact-Gamma route must differentiate the SAME vector field
-- used by the literal finite Galerkin ODE.  That vector field is already the
-- Leray-projected equation
--
--   F_N(u)(k) = -nu |k|^2 u(k) + P_k N_k(u).
--
-- Consequently the selected tangent used in the Round82 packet-transfer first
-- variation contains no independent pressure-gradient direction.  Pressure is
-- already encoded in the Leray projection defining `projectedNonlinearity`.
--
-- This matters for the Round85 three-way pressure decomposition: that
-- decomposition is useful when one deliberately reopens an unprojected
-- pressure representation, but it is NOT an additional analytic producer for
-- the source-native compact-Gamma drift.  The equalities below are literal
-- same-object equalities, not estimates and not a replacement assumption.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Literal
import DASHI.Physics.Closure.NSTriadKNLiteralPacketTransferFirstVariationRound82Exact as Packet
import DASHI.Physics.Closure.NSTriadKNLiteralPhysicalCompactTransferDriftRound82Exact as Drift

literalCompactGammaTangentIsProjectedGalerkinRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.literalRHS datum
  ≡ Literal.literalViscousQuadraticCoefficient (Drift.physicalSystem datum)
literalCompactGammaTangentIsProjectedGalerkinRHS datum = refl

literalCompactGammaPacketTangentIsSelectedProjectedGalerkinRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.packetRHS datum
  ≡ Packet.packetField model (Drift.shell datum)
      (Literal.literalViscousQuadraticCoefficient (Drift.physicalSystem datum))
literalCompactGammaPacketTangentIsSelectedProjectedGalerkinRHS datum = refl

literalCompactGammaTransferFirstVariationUsesProjectedRHS :
  ∀ {r} {model : LP.PeriodicHardShellFourierPDE {r}}
    (datum : Drift.LiteralPhysicalCompactTransferDatum model) →
  Drift.rawTransferTangent datum
  ≡ C3.real
    (Packet.packetTransferPairingFirstVariation
      model (Drift.finiteSystem datum) (Drift.shell datum)
      (Drift.packetModes datum)
      (Literal.literalViscousQuadraticCoefficient (Drift.physicalSystem datum)))
literalCompactGammaTransferFirstVariationUsesProjectedRHS datum = refl

round99CompactGammaUsesProjectedGalerkinTangent : Bool
round99CompactGammaUsesProjectedGalerkinTangent = true

round99SeparatePressureTangentRequiredByCompactGamma : Bool
round99SeparatePressureTangentRequiredByCompactGamma = false

round99PressureThreeWayEstimateIsShortestPathProducer : Bool
round99PressureThreeWayEstimateIsShortestPathProducer = false

round99CompactGammaUsesProjectedGalerkinTangentIsTrue :
  round99CompactGammaUsesProjectedGalerkinTangent ≡ true
round99CompactGammaUsesProjectedGalerkinTangentIsTrue = refl

round99SeparatePressureTangentRequiredByCompactGammaIsFalse :
  round99SeparatePressureTangentRequiredByCompactGamma ≡ false
round99SeparatePressureTangentRequiredByCompactGammaIsFalse = refl

round99PressureThreeWayEstimateIsShortestPathProducerIsFalse :
  round99PressureThreeWayEstimateIsShortestPathProducer ≡ false
round99PressureThreeWayEstimateIsShortestPathProducerIsFalse = refl
