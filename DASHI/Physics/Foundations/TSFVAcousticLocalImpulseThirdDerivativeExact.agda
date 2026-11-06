{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.TSFVAcousticLocalImpulseThirdDerivativeExact where

------------------------------------------------------------------------
-- P01.L06--08 / P02.L01,06,07 / S02 source-native local probe.
--
-- On the chosen nearest-neighbour 3D scalar lattice, the operator is
--   L(q)_n = mu² q_n + k * sum_(6 neighbors)(q_n - q_neighbor).
-- For the UNIT LOCAL INITIAL VELOCITY kick, q(0)=0 and q'(0)=δ0,
-- the linear wave equation q''=-Lq gives q'''(0)=-Lδ0.
-- Hence ALL SIX first neighbouring readouts have q'''(0)=k,
-- independent of mu²; the zero-distance readout differs by
-- -(mu²+6k), and all sites outside the closed one-step ball read
-- q'''(0)=0. These are derivative/readout equations on an actual
-- CHOSEN finite-neighbour lattice, not metric axiom declarations.
--
-- Scope: no Agda construction of an independently measured
-- original TSVF quantum observer, retarded continuum Green field,
-- physical Born measurements, or three spatial dimensions *emerging*
-- from an initially dimension-free micro-system. The selected
-- 3-axis graph is an explicit physical model CONTROL.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; -_)
import Data.Rational.Tactic.RingSolver as Ring

data LocalAxis : Set where
  x-axis y-axis z-axis : LocalAxis

data LocalOrientation : Set where
  plus minus : LocalOrientation

data LocalObservationSite : Set where
  kicked-site : LocalObservationSite
  neighboring-site : LocalAxis → LocalOrientation → LocalObservationSite
  outside-nearest-ball : LocalObservationSite

sixNeighborWeights : ℚ → ℚ
sixNeighborWeights k = (k + k) + (k + k) + (k + k)

sourceLatticeImpulseStiffness :
  (neighborCoupling massSquared : ℚ) →
  LocalObservationSite → ℚ
sourceLatticeImpulseStiffness k massSquared kicked-site =
  massSquared + sixNeighborWeights k
sourceLatticeImpulseStiffness k massSquared
  (neighboring-site axis orientation) = - k
sourceLatticeImpulseStiffness k massSquared outside-nearest-ball =
  0ℚ

-- Actual selected linear response (third time derivative at t=0):
-- q'''(0) = - L delta_0. The linear wave equation is the model's
-- source, not a theorem about every quantum observer.
sourceLocalImpulseThirdDerivative :
  (neighborCoupling massSquared : ℚ) →
  LocalObservationSite → ℚ
sourceLocalImpulseThirdDerivative k massSquared site =
  - sourceLatticeImpulseStiffness k massSquared site

allSixFirstNeighborResponsesReadCoupling :
  ∀ coupling massSquared axis orientation →
    sourceLocalImpulseThirdDerivative
      coupling massSquared (neighboring-site axis orientation)
    ≡ coupling
allSixFirstNeighborResponsesReadCoupling
    coupling massSquared axis orientation =
  Ring.solve-∀ coupling

outsideNearestBallHasZeroThirdDerivative :
  ∀ coupling massSquared →
    sourceLocalImpulseThirdDerivative
      coupling massSquared outside-nearest-ball
    ≡ 0ℚ
outsideNearestBallHasZeroThirdDerivative coupling massSquared =
  Ring.solve-∀

originalKickedSiteThirdDerivative :
  ∀ coupling massSquared →
    sourceLocalImpulseThirdDerivative
      coupling massSquared kicked-site
    ≡ - (massSquared + sixNeighborWeights coupling)
originalKickedSiteThirdDerivative coupling massSquared = refl

-- The third-derivative CHANNEL measurement is mass-blind:
-- an independent zero-momentum/full-frequency measurement is
-- needed to distinguish otherwise equal-cone mass models.
firstNeighborImpulseResponseIsMassIndependent :
  ∀ coupling massSquared1 massSquared2 axis orientation →
    sourceLocalImpulseThirdDerivative
      coupling massSquared1 (neighboring-site axis orientation)
    ≡
    sourceLocalImpulseThirdDerivative
      coupling massSquared2 (neighboring-site axis orientation)
firstNeighborImpulseResponseIsMassIndependent
    coupling massSquared1 massSquared2 axis orientation =
  Ring.solve-∀ coupling

-- Source-specific nonpromotion: the chosen local-response graph
-- and its time derivatives do not inhabit the original physical
-- TSVF-selected many-body/Born observer or construct a continuum.
