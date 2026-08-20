module DASHI.Physics.Closure.NSTriadKNCompactTransferHomogeneityCalibrationRound82Exact where

------------------------------------------------------------------------
-- ROUND82 / HOMOGENEITY CALIBRATION FOR THE TRANSFER DRIFT CORE
--
-- The physical compact-transfer numerator has now been reduced exactly to a
-- positive/common prefactor times
--
--   qdot D - q Ddot,
--
-- where q is cubic packet transfer and D is quadratic packet dissipation.
-- Along the pure amplitude tangent u -> (1+epsilon)u, homogeneity gives
--
--   qdot = 3 q,
--   Ddot = 2 D.
--
-- Therefore
--
--   qdot D - q Ddot = q D.
--
-- In particular, positive transfer q>0 and positive dissipation D>0 produce a
-- POSITIVE relative-growth core under positive amplitude motion.  Hence no
-- theorem using only boundedness of the compact potential, positivity, or
-- polynomial homogeneity can manufacture the required negative/coercive drift.
-- The actual Navier--Stokes tangent decomposition is essential.
--
-- This file proves the exact ring identity.  It is a calibration/no-go for an
-- over-strong proof strategy, not an assertion that the Navier--Stokes tangent
-- is a pure amplitude tangent.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNLiteralCompactTransferDriftDataRound82Exact as Drift

threeCarrier :
  ∀ {r} (F : C3.RealField r) → C3.Carrier F
threeCarrier F = C3.add F (C3.one F) (Drift.twoCarrier F)

amplitudeTransferTangent :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F
amplitudeTransferTangent F q = C3.multiply F (threeCarrier F) q

amplitudeDissipationTangent :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F
amplitudeDissipationTangent F d = C3.multiply F (Drift.twoCarrier F) d

amplitudeRelativeGrowthCore :
  ∀ {r} (F : C3.RealField r) →
  C3.Carrier F → C3.Carrier F → C3.Carrier F
amplitudeRelativeGrowthCore F q d =
  Drift.realSubtract F
    (C3.multiply F (amplitudeTransferTangent F q) d)
    (C3.multiply F q (amplitudeDissipationTangent F d))

amplitudeRelativeGrowthEqualsTransferTimesDissipation :
  ∀ {r} (F : C3.RealField r) →
  (q d : C3.Carrier F) →
  amplitudeRelativeGrowthCore F q d ≡ C3.multiply F q d
amplitudeRelativeGrowthEqualsTransferTimesDissipation F q d =
  P.R.solve 2
    (λ q d →
      ((((P.R.1# P.R.⊕ (P.R.1# P.R.⊕ P.R.1#)) P.R.⊗ q) P.R.⊗ d)
        P.R.⊕
        P.R.⊝ (q P.R.⊗ ((P.R.1# P.R.⊕ P.R.1#) P.R.⊗ d)))
      P.R.⊜ q P.R.⊗ d)
    refl q d
  where
  module P = Field.Polynomial F

round82HomogeneityAloneForcesNegativeCompactDrift : Bool
round82HomogeneityAloneForcesNegativeCompactDrift = false

round82AmplitudeRelativeGrowthCoreEqualsQTimesD : Bool
round82AmplitudeRelativeGrowthCoreEqualsQTimesD = true

round82ActualNSTangentStructureIsEssentialForC4 : Bool
round82ActualNSTangentStructureIsEssentialForC4 = true

round82AmplitudeRelativeGrowthCoreEqualsQTimesDIsTrue :
  round82AmplitudeRelativeGrowthCoreEqualsQTimesD ≡ true
round82AmplitudeRelativeGrowthCoreEqualsQTimesDIsTrue = refl
