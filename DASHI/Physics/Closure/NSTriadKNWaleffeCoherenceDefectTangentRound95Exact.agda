module DASHI.Physics.Closure.NSTriadKNWaleffeCoherenceDefectTangentRound95Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- ROUND95 / RADICAL-FREE COHERENCE DEFECT
--
-- The normalized phase coordinate
--
--   Psi = A^2 / (E_k E_p E_q)
--
-- is useful conceptually but introduces division and zero-leg singularities.
-- The equivalent homogeneous defect
--
--   H = E_k E_p E_q - A^2
--
-- is degree six and total.  H = 0 is the maximally coherent boundary whenever
-- the Cauchy/Gram inequality A^2 <= E_k E_p E_q is available on the physical
-- helical carrier.
--
-- This module derives the exact tangent from the Round95 normalized-phase
-- data.  Pure viscosity contributes
--
--   H' = -2 (rho_k+rho_p+rho_q) H,
--
-- while all movement relative to the coherent boundary is carried by a
-- self-triad defect-production term plus an external-network defect-production
-- term.  Thus viscosity alone preserves the normalized coherence ratio: the
-- decisive Clay estimate must come from nonlinear phase geometry / network
-- transfer, not from raw viscous damping of phase.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNNormalizedWaleffePhaseDerivativeRound95Exact as Phase

neg : ℚ → ℚ
neg x = - x

square : ℚ → ℚ
square x = x * x

coherenceDefect : Phase.NormalizedPhaseTangentData → ℚ
coherenceDefect d = Phase.energyProduct d + neg (square (Phase.amplitude d))

energyProductTangent : Phase.NormalizedPhaseTangentData → ℚ
energyProductTangent d =
    Phase.energyKTangent d * Phase.energyP d * Phase.energyQ d
  + Phase.energyK d * Phase.energyPTangent d * Phase.energyQ d
  + Phase.energyK d * Phase.energyP d * Phase.energyQTangent d

coherenceDefectTangent : Phase.NormalizedPhaseTangentData → ℚ
coherenceDefectTangent d =
  energyProductTangent d
  + neg (2 * Phase.amplitude d * Phase.amplitudeTangent d)

selfDefectProduction : Phase.NormalizedPhaseTangentData → ℚ
selfDefectProduction d =
    Phase.selfTransferK d * Phase.energyP d * Phase.energyQ d
  + Phase.energyK d * Phase.selfTransferP d * Phase.energyQ d
  + Phase.energyK d * Phase.energyP d * Phase.selfTransferQ d
  + neg (2 * Phase.amplitude d * Phase.selfAmplitudeForcing d)

externalDefectProduction : Phase.NormalizedPhaseTangentData → ℚ
externalDefectProduction d =
    Phase.externalTransferK d * Phase.energyP d * Phase.energyQ d
  + Phase.energyK d * Phase.externalTransferP d * Phase.energyQ d
  + Phase.energyK d * Phase.energyP d * Phase.externalTransferQ d
  + neg (2 * Phase.amplitude d * Phase.externalAmplitudeForcing d)

coherenceDefectDampedNetworkIdentity :
  (d : Phase.NormalizedPhaseTangentData) →
  coherenceDefectTangent d
  ≡
    neg (2 * (Phase.rhoK d + Phase.rhoP d + Phase.rhoQ d)
      * coherenceDefect d)
    + selfDefectProduction d
    + externalDefectProduction d
coherenceDefectDampedNetworkIdentity d
  rewrite Phase.amplitudeTangentMeaning d
        | Phase.energyKTangentMeaning d
        | Phase.energyPTangentMeaning d
        | Phase.energyQTangentMeaning d =
  solve
    ( Phase.amplitude d
    ∷ Phase.energyK d ∷ Phase.energyP d ∷ Phase.energyQ d
    ∷ Phase.rhoK d ∷ Phase.rhoP d ∷ Phase.rhoQ d
    ∷ Phase.selfAmplitudeForcing d ∷ Phase.externalAmplitudeForcing d
    ∷ Phase.selfTransferK d ∷ Phase.selfTransferP d ∷ Phase.selfTransferQ d
    ∷ Phase.externalTransferK d ∷ Phase.externalTransferP d
    ∷ Phase.externalTransferQ d ∷ [])

------------------------------------------------------------------------
-- Pure-viscosity calibration.
------------------------------------------------------------------------

record PureViscousPhaseData : Set where
  constructor pure-viscous-phase-data
  field
    tangentData : Phase.NormalizedPhaseTangentData
    selfAmplitudeForcingZero : Phase.selfAmplitudeForcing tangentData ≡ 0ℚ
    externalAmplitudeForcingZero : Phase.externalAmplitudeForcing tangentData ≡ 0ℚ
    selfTransferKZero : Phase.selfTransferK tangentData ≡ 0ℚ
    selfTransferPZero : Phase.selfTransferP tangentData ≡ 0ℚ
    selfTransferQZero : Phase.selfTransferQ tangentData ≡ 0ℚ
    externalTransferKZero : Phase.externalTransferK tangentData ≡ 0ℚ
    externalTransferPZero : Phase.externalTransferP tangentData ≡ 0ℚ
    externalTransferQZero : Phase.externalTransferQ tangentData ≡ 0ℚ

open PureViscousPhaseData public

pureViscosityOnlyScalesCoherenceDefect :
  (v : PureViscousPhaseData) →
  coherenceDefectTangent (tangentData v)
  ≡
  neg
    (2 *
      ( Phase.rhoK (tangentData v)
      + Phase.rhoP (tangentData v)
      + Phase.rhoQ (tangentData v))
      * coherenceDefect (tangentData v))
pureViscosityOnlyScalesCoherenceDefect v
  rewrite coherenceDefectDampedNetworkIdentity (tangentData v)
        | selfAmplitudeForcingZero v
        | externalAmplitudeForcingZero v
        | selfTransferKZero v | selfTransferPZero v | selfTransferQZero v
        | externalTransferKZero v | externalTransferPZero v
        | externalTransferQZero v =
  solve
    ( Phase.amplitude (tangentData v)
    ∷ Phase.energyK (tangentData v)
    ∷ Phase.energyP (tangentData v)
    ∷ Phase.energyQ (tangentData v)
    ∷ Phase.rhoK (tangentData v)
    ∷ Phase.rhoP (tangentData v)
    ∷ Phase.rhoQ (tangentData v) ∷ [])

round95CoherenceDefectTangentClosed : Bool
round95CoherenceDefectTangentClosed = true

round95PureViscosityDoesNotCreateRelativePhaseEscape : Bool
round95PureViscosityDoesNotCreateRelativePhaseEscape = true

round95CoherenceDefectTangentClosedIsTrue :
  round95CoherenceDefectTangentClosed ≡ true
round95CoherenceDefectTangentClosedIsTrue = refl

round95PureViscosityDoesNotCreateRelativePhaseEscapeIsTrue :
  round95PureViscosityDoesNotCreateRelativePhaseEscape ≡ true
round95PureViscosityDoesNotCreateRelativePhaseEscapeIsTrue = refl
