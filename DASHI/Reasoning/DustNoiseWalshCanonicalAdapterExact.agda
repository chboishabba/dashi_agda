module DASHI.Reasoning.DustNoiseWalshCanonicalAdapterExact where

-- Reuse, do not duplicate, the existing 16-point rational Walsh owner.
-- Canonical mathematical owner: DASHI.Physics.YangMills.
-- The shared Walsh identities predate both Dust and Noise.
-- DASHI contributes only this consumer and conditional estimator interpretation.
-- No claim of full-dimensional GPU Noise algorithm or kernel receipt.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact as Cube
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
open import Data.Rational using (_*_)
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshCharacterExact as Walsh
import DASHI.Physics.YangMills.BalabanBooleanFourCubeWalshInversionExact as Inversion

-- A costed Noise probe that has already been reduced to one scalar value
-- per Walsh direction. The source code of the underlying training
-- experiment must supply these values and the hardware/timing receipts.
record CompleteProbeValues : Set where
  field
    coefficient : Cube.Subset4 → ℚ
    sourceAttribution : String

-- The canonical inverse Walsh transform is the *actual* algorithm here.
-- This is a finite basis reconstruction, not a stochastic expectation claim.
decodeProbeValues :
  (Cube.Subset4 → ℚ) → Cube.Subset4 → ℚ
decodeProbeValues measurements coordinate =
  Inversion.oneSixteenth *
    Sums.sumRational Cube.allSubsets4
      (λ direction → Walsh.walshCharacter direction coordinate *
        measurements direction)

-- One can recover ANY source vector exactly from all its Walsh
-- coefficients, using the original 16-point rational proof.
fullProbeReconstruction :
  (activationCredit : Cube.Subset4 → ℚ) →
  (coordinate : Cube.Subset4) →
  decodeProbeValues (Walsh.walshCoefficient activationCredit) coordinate
    ≡ activationCredit coordinate
fullProbeReconstruction = Inversion.walshReconstructionExact

-- The complete collection of coefficient observations separates source
-- vectors, unlike a compressed subfamily.
fullProbeIdentifiability :
  (left right : Cube.Subset4 → ℚ) →
  ((direction : Cube.Subset4) →
    Walsh.walshCoefficient left direction ≡
      Walsh.walshCoefficient right direction) →
  (coordinate : Cube.Subset4) →
  left coordinate ≡ right coordinate
fullProbeIdentifiability = Inversion.walshTransformInjective

-- Critical BIDI distinction: a real measured perturbed loss vector is
-- not definitionally the Walsh transform of an unknown exact gradient.
-- That reduction needs a linear-response/source-specific proof.
record DirectionalMeasurementBridge : Set₁ where
  field
    latentCredit : Cube.Subset4 → ℚ
    measuredDirectionalResponse : Cube.Subset4 → ℚ
    measurementIsWalshCoefficient :
      (direction : Cube.Subset4) →
      measuredDirectionalResponse direction
        ≡ Walsh.walshCoefficient latentCredit direction

recoverCreditFromMeasuredResponses :
  (bridge : DirectionalMeasurementBridge) →
  (coordinate : Cube.Subset4) →
  decodeProbeValues
    (DirectionalMeasurementBridge.measuredDirectionalResponse bridge)
    coordinate
  ≡ DirectionalMeasurementBridge.latentCredit bridge coordinate
recoverCreditFromMeasuredResponses bridge coordinate =
  trans
    (cong (λ x → Inversion.oneSixteenth * x)
      (Sums.sumRationalCong
        Cube.allSubsets4
        (λ direction →
          Walsh.walshCharacter direction coordinate *
          DirectionalMeasurementBridge.measuredDirectionalResponse bridge direction)
        (λ direction →
          Walsh.walshCharacter direction coordinate *
          Walsh.walshCoefficient
            (DirectionalMeasurementBridge.latentCredit bridge) direction)
        (λ direction →
          cong (λ v → Walsh.walshCharacter direction coordinate * v)
            (DirectionalMeasurementBridge.measurementIsWalshCoefficient bridge direction))))
    (Inversion.walshReconstructionExact
      (DirectionalMeasurementBridge.latentCredit bridge) coordinate)
