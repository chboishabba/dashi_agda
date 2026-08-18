module DASHI.Physics.Closure.NSTriadKNCrossModePositiveVortexStretchingWitnessRound78Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- DOI: 10.1063/1.858309.
--
-- ROUND78 / POSITIVE CROSS-MODE FINITE WITNESS
--
-- Round78 proved exact same-mode self-stretching vanishes.  This file checks
-- that the literal Fourier strain carrier nevertheless admits a genuinely
-- positive CROSS-vector interaction.
--
-- Choose
--
--   k      = (1,0,0), |k|^-2 = 1,
--   source = (0,1,0),
--   target = (1,0,-1).
--
-- The existing exact formula gives
--
--   target . S_k(source) target
--     = - (k.target) k.(source x target)
--     = -(1)(-1)
--     = 1.
--
-- This is not yet a selected NS descendant/triad theorem: target is an exact
-- vector in the strain action, not an assertion that the Round77 critical
-- event dynamically realizes this configuration.  It proves the local Fourier
-- geometry has not killed the only viable B2 mechanism after the same-mode
-- no-go; positive cross-mode stretching is algebraically possible.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact as Strain

unitXMode : V.ProjectionMode
unitXMode = V.projection-mode (V.v3 1ℚ 0ℚ 0ℚ) 1ℚ refl

crossSource : V.Vector3
crossSource = V.v3 0ℚ 1ℚ 0ℚ

crossTarget : V.Vector3
crossTarget = V.v3 1ℚ 0ℚ (- 1ℚ)

positiveCrossModeStretchingExact :
  Strain.fourierStretchingScalar unitXMode crossSource crossTarget ≡ 1ℚ
positiveCrossModeStretchingExact =
  trans
    (Strain.fourierStretchingMisalignmentExact
      unitXMode crossSource crossTarget)
    (solve [])

round78PositiveCrossModeStretchingExistsOnFourierCarrier : Bool
round78PositiveCrossModeStretchingExistsOnFourierCarrier = true

round78PositiveCrossModeWitnessAlreadyIsSelectedB2 : Bool
round78PositiveCrossModeWitnessAlreadyIsSelectedB2 = false

round78PositiveCrossModeStretchingExistsOnFourierCarrierIsTrue :
  round78PositiveCrossModeStretchingExistsOnFourierCarrier ≡ true
round78PositiveCrossModeStretchingExistsOnFourierCarrierIsTrue = refl
