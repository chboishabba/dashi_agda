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
-- PROOF BOUNDARY: sourceLocalImpulseThirdDerivative is DEFINED as
-- the coefficient -L delta_0. No differentiability/existence or
-- uniqueness theorem for a retarded C³ solution is formalised here.
-- The identity with q'''(0) follows analytically for any selected
-- C³ solution satisfying q''=-Lq and q'(0)=delta_0.
--
-- Scope: no Agda construction of an independently measured
-- original TSVF quantum observer, retarded continuum Green field,
-- physical Born measurements, or three spatial dimensions *emerging*
-- from an initially dimension-free micro-system. The selected
-- 3-axis graph is an explicit physical model CONTROL.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_)
import Data.Rational.Tactic.RingSolver as Ring
open import Relation.Binary.PropositionalEquality using (cong)

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


------------------------------------------------------------------------
-- AR: the original origin AND one marked neighbour jointly determine
-- the complete two-parameter selected local impulse family. Neither
-- a measured physical clock nor spatial calibration is inferred.
------------------------------------------------------------------------
open import Data.Product using (_×_; _,_)

sourceImpulseProbePair : ℚ → ℚ → ℚ × ℚ
sourceImpulseProbePair coupling massSquared =
  sourceLocalImpulseThirdDerivative coupling massSquared
    (neighboring-site x-axis plus) ,
  sourceLocalImpulseThirdDerivative coupling massSquared kicked-site

reopenSourceImpulseProbePair : ℚ × ℚ → ℚ × ℚ
reopenSourceImpulseProbePair (neighbor , center) =
  neighbor , (- center - sixNeighborWeights neighbor)

sourceImpulseProbePairReopens :
  ∀ coupling massSquared →
  reopenSourceImpulseProbePair (sourceImpulseProbePair coupling massSquared)
  ≡ (coupling , massSquared)
sourceImpulseProbePairReopens coupling massSquared
  rewrite allSixFirstNeighborResponsesReadCoupling coupling massSquared x-axis plus
        | originalKickedSiteThirdDerivative coupling massSquared =
  cong (λ m → coupling , m) (Ring.solve-∀ coupling massSquared)

sourceImpulseProbePairRightInverse :
  (readout : ℚ × ℚ) →
  let (coupling , massSquared) = reopenSourceImpulseProbePair readout
  in sourceImpulseProbePair coupling massSquared ≡ readout
sourceImpulseProbePairRightInverse (neighbor , center)
  rewrite allSixFirstNeighborResponsesReadCoupling
    neighbor (- center - sixNeighborWeights neighbor) x-axis plus =
  cong (λ z → neighbor , z) (Ring.solve-∀ neighbor center)


------------------------------------------------------------------------
-- AT: coordination counts of the original five-site periodic axes.
-- Coefficients of (1+2z+2z²)^m. This computes the shell polynomial;
-- the graph counting proof and arbitrary dimension Delannoy formula
-- are supplied analytically in the source ledger, not asserted here.
------------------------------------------------------------------------
import Agda.Builtin.Nat as N

periodFiveShell : N.Nat → N.Nat → N.Nat
periodFiveShell N.zero N.zero = 1
periodFiveShell N.zero (N.suc r) = 0
periodFiveShell (N.suc m) N.zero = periodFiveShell m N.zero
periodFiveShell (N.suc m) (N.suc N.zero) =
  N._+_ (periodFiveShell m 1) (N._*_ 2 (periodFiveShell m 0))
periodFiveShell (N.suc m) (N.suc (N.suc r)) =
  N._+_ (N._+_ (periodFiveShell m (N.suc (N.suc r)))
               (N._*_ 2 (periodFiveShell m (N.suc r))))
        (N._*_ 2 (periodFiveShell m r))

oddResponseOrder : N.Nat → N.Nat
oddResponseOrder r = N.suc (N._*_ 2 r)

originalTorusMiddleShell : periodFiveShell 3 3 ≡ 32
originalTorusMiddleShell = refl

originalTorusLastShell : periodFiveShell 3 6 ≡ 8
originalTorusLastShell = refl

originalTorusLastResponseOrder : oddResponseOrder 6 ≡ 13
originalTorusLastResponseOrder = refl
