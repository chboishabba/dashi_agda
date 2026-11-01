module DASHI.Physics.Closure.NSTriadKNB2PressureResolvedExcessRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Dhawal Buaria; Alain Pumir.
-- Title: "Role of pressure in generation of intense velocity gradients in
-- turbulent flows".
-- DOI: 10.48550/arXiv.2308.03902.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- ROUND78 / RAW PHYSICAL B2 SCALAR
--
-- If a selected Round77 frame-weighted supercritical row is identified with
-- the exact pressure-Hessian stretching budget, then its positive excess is
-- literally
--
--   epsilon
--     = [ W.W - omega^T H omega ] - additionalDepletion.
--
-- Therefore B2 reduces to one strict source-native scalar inequality:
--
--   W.W - omega^T H omega > additionalDepletion.
--
-- The additional term is where the already-declared geometric, frame,
-- allocation and viscous costs live.  Conversely any proof that the raw
-- pressure-resolved acceleration is <= that cost refutes a supercritical row.
-- This is an exact reduction; it does not assume the DNS sign statistics.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _-_; _≤_; _<_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (subst; trans)

import DASHI.Physics.Closure.NSTriadKNFrameWeightedSupercriticalPropagationRound77Exact as Propagation
import DASHI.Physics.Closure.NSTriadKNPressureStretchingCompetitionRound78Exact as Competition
import DASHI.Physics.Closure.NSTriadKNPressureHessianVortexStretchingSplitRound78Exact as Pressure
import DASHI.Physics.Closure.NSTriadKNFrameWeightedStretchingDepletionGateRound78Exact as Gate

record PressureResolvedPhysicalExcess
    (row : Propagation.FrameWeightedSupercriticalRow) : Set where
  field
    rawPressureStretching : Pressure.RawPressureStretchingContractions
    additionalDepletion : ℚ
    excessIsPressureResolvedSurplus :
      Propagation.excess row
      ≡ Competition.netStretchingSurplus
          (Pressure.asCompetitionBudget rawPressureStretching additionalDepletion)

open PressureResolvedPhysicalExcess public

pressureResolvedExcessMeaning :
  ∀ {row} (resolved : PressureResolvedPhysicalExcess row) →
  Propagation.excess row
  ≡ Pressure.inviscidStretchingAcceleration (rawPressureStretching resolved)
      - additionalDepletion resolved
pressureResolvedExcessMeaning resolved =
  trans
    (excessIsPressureResolvedSurplus resolved)
    (Pressure.competitionSurplusIsRawAccelerationMinusAdditionalDepletion
      (rawPressureStretching resolved)
      (additionalDepletion resolved))

physicalSupercriticalityForcesPositivePressureResolvedSurplus :
  ∀ {row} (resolved : PressureResolvedPhysicalExcess row) →
  0ℚ <
    Pressure.inviscidStretchingAcceleration (rawPressureStretching resolved)
      - additionalDepletion resolved
physicalSupercriticalityForcesPositivePressureResolvedSurplus {row} resolved =
  subst
    (0ℚ <_)
    (pressureResolvedExcessMeaning resolved)
    (Propagation.excessPositive row)

pressureResolvedDepletionDominanceRefutesB2 :
  ∀ {row} (resolved : PressureResolvedPhysicalExcess row) →
  Pressure.inviscidStretchingAcceleration (rawPressureStretching resolved)
    ≤ additionalDepletion resolved →
  0ℚ < 0ℚ
pressureResolvedDepletionDominanceRefutesB2 resolved dominance =
  ℚP.<-≤-trans
    (physicalSupercriticalityForcesPositivePressureResolvedSurplus resolved)
    (Gate.differenceNonpositiveFromDominance
      (Pressure.inviscidStretchingAcceleration (rawPressureStretching resolved))
      (additionalDepletion resolved)
      dominance)

round78B2ReducedToPressureResolvedStrictSurplus : Bool
round78B2ReducedToPressureResolvedStrictSurplus = true

round78SelectedEventPressureResolvedIdentityConstructed : Bool
round78SelectedEventPressureResolvedIdentityConstructed = false

round78B2ReducedToPressureResolvedStrictSurplusIsTrue :
  round78B2ReducedToPressureResolvedStrictSurplus ≡ true
round78B2ReducedToPressureResolvedStrictSurplusIsTrue = refl
