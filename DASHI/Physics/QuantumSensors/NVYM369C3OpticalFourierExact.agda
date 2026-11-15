module DASHI.Physics.QuantumSensors.NVYM369C3OpticalFourierExact where

-- Optical three-channel C3 permutation: reuse the *actual* C3
-- equivariance authority from the 369/Yang--Mills programme.
-- This is an abelian/rational finite optical *symmetry test*, not an
-- SU(2) connection, Balaban RG proof, or a diamond C3v material action.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as YM
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid

record ThreePhotonChannels : Set where
  constructor channels
  field
    first second third : ℚ
open ThreePhotonChannels public

rotateChannels : ThreePhotonChannels → ThreePhotonChannels
rotateChannels (channels a b c) = channels c a b

rotateChannelsCubed :
  (x : ThreePhotonChannels) →
  rotateChannels (rotateChannels (rotateChannels x)) ≡ x
rotateChannelsCubed (channels a b c) = refl

photonC3 : C3.OrderThreeAction ThreePhotonChannels
photonC3 = record
  { rotate = rotateChannels
  ; rotateCubed = rotateChannelsCubed
  }

coherentRealSum : ThreePhotonChannels → ℚ
coherentRealSum (channels a b c) = a + b + c

coherentIntensity : ThreePhotonChannels → ℚ
coherentIntensity x = coherentRealSum x * coherentRealSum x

-- Permuting channels cannot alter the total amplitude in this
-- equal optical-path transfer fixture.
sumC3Invariant :
  (x : ThreePhotonChannels) →
  coherentRealSum (rotateChannels x) ≡ coherentRealSum x
sumC3Invariant (channels a b c) =
  solve (a ∷ b ∷ c ∷ [])

intensityC3Invariant :
  (x : ThreePhotonChannels) →
  coherentIntensity (rotateChannels x) ≡ coherentIntensity x
intensityC3Invariant (channels a b c) =
  solve (a ∷ b ∷ c ∷ [])

-- A scalar observation has the identity C3 action, so the exact
-- intertwiner is a theorem, not an assumed identification of YM and NV.
trivialScalarC3 : C3.OrderThreeAction ℚ
trivialScalarC3 = record
  { rotate = λ q → q
  ; rotateCubed = λ q → refl
  }

sumIntertwiner : C3.EquivariantMap photonC3 trivialScalarC3 coherentRealSum
sumIntertwiner = record { intertwines = sumC3Invariant }

intensityIntertwiner : C3.EquivariantMap photonC3 trivialScalarC3 coherentIntensity
intensityIntertwiner = record { intertwines = intensityC3Invariant }

-- The existing Balaban spatial XYZ permutation action is an unrelated
-- instance of the *same generic theorem shape*. A physical map from
-- YM grid/sources to these optical channels still requires a witness.
balabanSpatialC3 : C3.OrderThreeAction Grid.GridCell4
balabanSpatialC3 = YM.cmp109SpatialXYZC3Action
