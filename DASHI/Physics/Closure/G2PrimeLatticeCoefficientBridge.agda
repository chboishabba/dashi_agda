module DASHI.Physics.Closure.G2PrimeLatticeCoefficientBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Geometry.PrimeLattice as PL
import DASHI.Physics.Closure.G2DiscreteCurvatureCarrier as G2DCC
import DASHI.Physics.ShiftFiniteGaugeCoupling as SFGC
import DASHI.Physics.ShiftFiniteGaugeSymmetry as SFGS
import DASHI.Physics.ShiftPhaseTableInterference as SPTI4

------------------------------------------------------------------------
-- Concrete Phase4 coefficients for the standalone prime lattice.
--
-- PrimeLattice supplies the square geometry and asks callers for the exact
-- four-term cancellation law of their coefficient object.  Phase4 is the
-- finite C4 phase table already used by SFGC, so the law is closed by finite
-- normalization over its four constructors.

phase4Sub :
  SPTI4.Phase4 →
  SPTI4.Phase4 →
  SPTI4.Phase4
phase4Sub a b =
  SFGS.phaseAdd4 a (SFGS.phaseInv4 b)

phase4-d2SquareCancellation :
  (sw se nw ne : SPTI4.Phase4) →
  phase4Sub
    (SFGS.phaseAdd4 (phase4Sub se sw) (phase4Sub ne se))
    (SFGS.phaseAdd4 (phase4Sub ne nw) (phase4Sub nw sw))
    ≡
  SPTI4.φ0
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 SPTI4.φ3 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 SPTI4.φ0 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 SPTI4.φ1 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 SPTI4.φ2 = refl
phase4-d2SquareCancellation SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 SPTI4.φ3 = refl

phase4PrimeLatticeCoefficientLaw :
  PL.PrimeLatticeCoefficientLaw SPTI4.Phase4
phase4PrimeLatticeCoefficientLaw =
  record
    { zero =
        SPTI4.φ0
    ; _+_ =
        SFGS.phaseAdd4
    ; _-_ =
        phase4Sub
    ; d2SquareCancellation =
        phase4-d2SquareCancellation
    }

phase4PrimeLatticeD2Zero :
  (f : PL.0Form SPTI4.Phase4) →
  (cell : PL.PrimeLattice2Cell) →
  PL.δ₁ phase4PrimeLatticeCoefficientLaw
    (PL.δ₀ phase4PrimeLatticeCoefficientLaw f)
    cell
    ≡
  SPTI4.φ0
phase4PrimeLatticeD2Zero =
  PL.δ₁∘δ₀-zero phase4PrimeLatticeCoefficientLaw

------------------------------------------------------------------------
-- Fail-closed bridge status.
--
-- This module intentionally does not produce a DiscreteCurvatureCarrier for
-- SFGC.GaugeField.  The missing bridge is not coefficient algebra anymore:
-- it is the action/projection that turns a prime-lattice edge into the SFGC
-- field's existing ShiftPressurePoint-indexed Phase4 link.

data G2PrimeLatticeCoefficientBridgeStatus : Set where
  phase4CoefficientLawClosedButNoSFGCCarrier :
    G2PrimeLatticeCoefficientBridgeStatus

data G2PrimeLatticeSFGCBridgeMissing : Set where
  missingPrimeLatticeEdgeToShiftPressurePoint :
    G2PrimeLatticeSFGCBridgeMissing

  missingPrimeIndexedSFGCLinkAction :
    G2PrimeLatticeSFGCBridgeMissing

  missingSFGCPrimeLatticeConnectionTo1Form :
    G2PrimeLatticeSFGCBridgeMissing

  missingSFGCPrimeLatticeVacuumFlatness :
    G2PrimeLatticeSFGCBridgeMissing

record G2PrimeLatticeCoefficientBridgeReceipt : Set₁ where
  field
    status :
      G2PrimeLatticeCoefficientBridgeStatus

    coefficientCarrier :
      Set

    coefficientLaw :
      PL.PrimeLatticeCoefficientLaw coefficientCarrier

    phase4D2Zero :
      (f : PL.0Form SPTI4.Phase4) →
      (cell : PL.PrimeLattice2Cell) →
      PL.δ₁ phase4PrimeLatticeCoefficientLaw
        (PL.δ₀ phase4PrimeLatticeCoefficientLaw f)
        cell
        ≡
      SPTI4.φ0

    inspectedConnectionCarrier :
      Set

    inspectedConnectionCarrierIsSFGC :
      inspectedConnectionCarrier ≡ SFGC.GaugeField

    existingPointLinkBridge :
      G2DCC.SFGCPointLink1FormBridge

    exactMissing :
      G2PrimeLatticeSFGCBridgeMissing

    remainingMissing :
      List G2PrimeLatticeSFGCBridgeMissing

    nextRequiredInterface :
      String

    nonPromotionBoundary :
      List String

canonicalG2PrimeLatticeCoefficientBridgeReceipt :
  G2PrimeLatticeCoefficientBridgeReceipt
canonicalG2PrimeLatticeCoefficientBridgeReceipt =
  record
    { status =
        phase4CoefficientLawClosedButNoSFGCCarrier
    ; coefficientCarrier =
        SPTI4.Phase4
    ; coefficientLaw =
        phase4PrimeLatticeCoefficientLaw
    ; phase4D2Zero =
        phase4PrimeLatticeD2Zero
    ; inspectedConnectionCarrier =
        SFGC.GaugeField
    ; inspectedConnectionCarrierIsSFGC =
        refl
    ; existingPointLinkBridge =
        G2DCC.canonicalSFGCPointLink1FormBridge
    ; exactMissing =
        missingPrimeLatticeEdgeToShiftPressurePoint
    ; remainingMissing =
        missingPrimeLatticeEdgeToShiftPressurePoint
        ∷ missingPrimeIndexedSFGCLinkAction
        ∷ missingSFGCPrimeLatticeConnectionTo1Form
        ∷ missingSFGCPrimeLatticeVacuumFlatness
        ∷ []
    ; nextRequiredInterface =
        "PrimeLatticeEdge -> ShiftPressurePoint, or a prime-indexed SFGC link action FactorVec -> SSP -> Phase4"
    ; nonPromotionBoundary =
        "Phase4 now supplies the concrete PrimeLatticeCoefficientLaw required by PrimeLattice.d2"
        ∷ "The closed law is coefficient-level only: it proves d1(d0 f) = φ0 for Phase4-valued prime-lattice 0-forms"
        ∷ "SFGC.GaugeField is still ShiftPressurePoint -> Phase4 on a three-point process chain"
        ∷ "No honest map from PrimeLatticeEdge to the SFGC ShiftPressurePoint carrier is available in the inspected API"
        ∷ "Therefore this module does not construct DiscreteCurvatureCarrier SFGC.GaugeField and does not promote G2"
        ∷ []
    }

g2PrimeLatticeCoefficientBridgeFirstMissing :
  G2PrimeLatticeCoefficientBridgeReceipt.exactMissing
    canonicalG2PrimeLatticeCoefficientBridgeReceipt
    ≡
  missingPrimeLatticeEdgeToShiftPressurePoint
g2PrimeLatticeCoefficientBridgeFirstMissing =
  refl
