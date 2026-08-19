module DASHI.Physics.Closure.NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: J. M. Manley; H. E. Rowe.
-- Title: "Some General Properties of Nonlinear Elements-Part I. General
-- Energy Relations".
-- Proceedings of the IRE 44(7) (1956), 904--913.
-- DOI: 10.1109/JRPROC.1956.275145.
--
-- ROUND95 / NORMALIZED PHASE DERIVATIVE
--
-- Let
--
--   Psi = A^2 / (E_k E_p E_q)
--
-- on a nonzero three-leg cell.  Rather than introduce division, this module
-- works with the numerator obtained after multiplying the quotient-rule
-- identity by (E_k E_p E_q)^2.  The exact algebraic object is
--
--   Q = 2 A A' E_k E_p E_q
--       - A^2 (E_k' E_p E_q + E_k E_p' E_q + E_k E_p E_q').
--
-- If
--
--   A'   = -(rho_k+rho_p+rho_q) A + F_A,
--   E_j' = -2 rho_j E_j + T_j,
--
-- then every viscous term cancels IDENTICALLY in Q.  This is the exact
-- denominator-free statement behind the logarithmic cancellation
--
--   Psi'/Psi = 2 A'/A - E_k'/E_k - E_p'/E_p - E_q'/E_q.
--
-- The nonlinear forcing is split into self-triad and external-network pieces.
-- Importantly, the self-triad amplitude forcing F_A^self is retained.  The
-- Waleffe energy-transfer identities alone do NOT imply F_A^self = 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst)

neg : ℚ → ℚ
neg x = - x

square : ℚ → ℚ
square x = x * x

cube : ℚ → ℚ
cube x = (x * x) * x

record NormalizedPhaseTangentData : Set where
  constructor normalized-phase-tangent-data
  field
    amplitude amplitudeTangent : ℚ
    energyK energyP energyQ : ℚ
    energyKTangent energyPTangent energyQTangent : ℚ

    rhoK rhoP rhoQ : ℚ

    selfAmplitudeForcing externalAmplitudeForcing : ℚ
    selfTransferK selfTransferP selfTransferQ : ℚ
    externalTransferK externalTransferP externalTransferQ : ℚ

    amplitudeTangentMeaning :
      amplitudeTangent
      ≡ neg ((rhoK + rhoP + rhoQ) * amplitude)
        + selfAmplitudeForcing + externalAmplitudeForcing

    energyKTangentMeaning :
      energyKTangent
      ≡ neg ((2 * rhoK) * energyK)
        + selfTransferK + externalTransferK

    energyPTangentMeaning :
      energyPTangent
      ≡ neg ((2 * rhoP) * energyP)
        + selfTransferP + externalTransferP

    energyQTangentMeaning :
      energyQTangent
      ≡ neg ((2 * rhoQ) * energyQ)
        + selfTransferQ + externalTransferQ

open NormalizedPhaseTangentData public

energyProduct : NormalizedPhaseTangentData → ℚ
energyProduct d = energyK d * energyP d * energyQ d

normalizedPhaseDerivativeNumerator : NormalizedPhaseTangentData → ℚ
normalizedPhaseDerivativeNumerator d =
  2 * amplitude d * amplitudeTangent d * energyProduct d
  + neg
      (square (amplitude d)
        * ( energyKTangent d * energyP d * energyQ d
          + energyK d * energyPTangent d * energyQ d
          + energyK d * energyP d * energyQTangent d))

selfNormalizedDrift : NormalizedPhaseTangentData → ℚ
selfNormalizedDrift d =
  2 * amplitude d * selfAmplitudeForcing d * energyProduct d
  + neg
      (square (amplitude d)
        * ( selfTransferK d * energyP d * energyQ d
          + energyK d * selfTransferP d * energyQ d
          + energyK d * energyP d * selfTransferQ d))

externalNormalizedDrift : NormalizedPhaseTangentData → ℚ
externalNormalizedDrift d =
  2 * amplitude d * externalAmplitudeForcing d * energyProduct d
  + neg
      (square (amplitude d)
        * ( externalTransferK d * energyP d * energyQ d
          + energyK d * externalTransferP d * energyQ d
          + energyK d * energyP d * externalTransferQ d))

normalizedPhaseViscosityCancelsExactly :
  (d : NormalizedPhaseTangentData) →
  normalizedPhaseDerivativeNumerator d
  ≡ selfNormalizedDrift d + externalNormalizedDrift d
normalizedPhaseViscosityCancelsExactly d
  rewrite amplitudeTangentMeaning d
        | energyKTangentMeaning d
        | energyPTangentMeaning d
        | energyQTangentMeaning d =
  solve
    ( amplitude d ∷ energyK d ∷ energyP d ∷ energyQ d
    ∷ rhoK d ∷ rhoP d ∷ rhoQ d
    ∷ selfAmplitudeForcing d ∷ externalAmplitudeForcing d
    ∷ selfTransferK d ∷ selfTransferP d ∷ selfTransferQ d
    ∷ externalTransferK d ∷ externalTransferP d ∷ externalTransferQ d
    ∷ [])

------------------------------------------------------------------------
-- Waleffe self-transfer specialization.
------------------------------------------------------------------------

record WaleffeSelfTransferData : Set where
  constructor waleffe-self-transfer-data
  field
    tangentData : NormalizedPhaseTangentData
    lambdaK lambdaP lambdaQ : ℚ

    selfTransferKMeaning :
      selfTransferK tangentData
      ≡ (lambdaQ + neg lambdaP) * amplitude tangentData

    selfTransferPMeaning :
      selfTransferP tangentData
      ≡ (lambdaK + neg lambdaQ) * amplitude tangentData

    selfTransferQMeaning :
      selfTransferQ tangentData
      ≡ (lambdaP + neg lambdaK) * amplitude tangentData

open WaleffeSelfTransferData public

energyImbalancePolynomial : WaleffeSelfTransferData → ℚ
energyImbalancePolynomial w =
    lambdaK w * energyK (tangentData w)
      * (energyP (tangentData w) + neg (energyQ (tangentData w)))
  + lambdaP w * energyP (tangentData w)
      * (energyQ (tangentData w) + neg (energyK (tangentData w)))
  + lambdaQ w * energyQ (tangentData w)
      * (energyK (tangentData w) + neg (energyP (tangentData w)))

waleffeSelfNormalizedDriftExact :
  (w : WaleffeSelfTransferData) →
  selfNormalizedDrift (tangentData w)
  ≡
    2 * amplitude (tangentData w)
      * selfAmplitudeForcing (tangentData w)
      * energyProduct (tangentData w)
    + cube (amplitude (tangentData w)) * energyImbalancePolynomial w
waleffeSelfNormalizedDriftExact w
  rewrite selfTransferKMeaning w
        | selfTransferPMeaning w
        | selfTransferQMeaning w =
  solve
    ( amplitude (tangentData w)
    ∷ energyK (tangentData w) ∷ energyP (tangentData w)
    ∷ energyQ (tangentData w)
    ∷ selfAmplitudeForcing (tangentData w)
    ∷ lambdaK w ∷ lambdaP w ∷ lambdaQ w ∷ [])

------------------------------------------------------------------------
-- Equipartition calibration.
--
-- The Waleffe ENERGY-IMBALANCE polynomial vanishes when all three modal
-- energies coincide.  The full self normalized drift still contains
-- 2 A F_A^self E^3.  Thus equipartition alone does not prove Psi' = 0.
------------------------------------------------------------------------

energyImbalanceVanishesAtEquipartition :
  ∀ (lambdaK lambdaP lambdaQ E : ℚ) →
    lambdaK * E * (E + neg E)
  + lambdaP * E * (E + neg E)
  + lambdaQ * E * (E + neg E)
  ≡ 0ℚ
energyImbalanceVanishesAtEquipartition lambdaK lambdaP lambdaQ E =
  solve (lambdaK ∷ lambdaP ∷ lambdaQ ∷ E ∷ [])

round95NormalizedPhaseViscosityCancellationClosed : Bool
round95NormalizedPhaseViscosityCancellationClosed = true

round95WaleffeSelfEnergyImbalanceExact : Bool
round95WaleffeSelfEnergyImbalanceExact = true

round95SelfAmplitudeForcingStillRequiresIdentification : Bool
round95SelfAmplitudeForcingStillRequiresIdentification = true

round95NormalizedPhaseViscosityCancellationClosedIsTrue :
  round95NormalizedPhaseViscosityCancellationClosed ≡ true
round95NormalizedPhaseViscosityCancellationClosedIsTrue = refl

round95WaleffeSelfEnergyImbalanceExactIsTrue :
  round95WaleffeSelfEnergyImbalanceExact ≡ true
round95WaleffeSelfEnergyImbalanceExactIsTrue = refl

round95SelfAmplitudeForcingStillRequiresIdentificationIsTrue :
  round95SelfAmplitudeForcingStillRequiresIdentification ≡ true
round95SelfAmplitudeForcingStillRequiresIdentificationIsTrue = refl
