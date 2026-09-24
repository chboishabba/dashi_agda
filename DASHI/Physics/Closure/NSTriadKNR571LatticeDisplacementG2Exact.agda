module DASHI.Physics.Closure.NSTriadKNR571LatticeDisplacementG2Exact where

------------------------------------------------------------------------
-- PERIODIC B: LITERAL Z^3 DISPLACEMENT REALIZATION FOR THE DISCRETE G2 THEOREM
--
-- We choose the second-moment displacement scalar to be the literal natural
-- squared norm of the integer shift, embedded in Q:
--
--   d(y) = |y|_Z^2 in Q.
--
-- For y != 0, d(y) >= 1.  Combining this with
-- NSTriadKNR571DiscreteG2FromG1Exact removes the former physical-gradient
-- hypothesis from the state side of the periodic R571 route.
--
-- The remaining SAME-DISPLACEMENT obligation is radial: A1/A2 must be stated
-- using this d(y) (or proved below it).  No continuous frequency derivative is
-- required for B.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_; ∣_∣)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNRationalIntegerEmbeddingModeNormScaleExact as Scale
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact as G0
import DASHI.Physics.Closure.NSTriadKNR571HermitianStateAmplitudeEnvelopeExact as G1
import DASHI.Physics.Closure.NSTriadKNR571DiscreteG2FromG1Exact as G2

latticeSquaredDisplacement : Z3.FourierMode → ℚ
latticeSquaredDisplacement = Scale.modeNatNormAsRational

positiveNatAtLeastOne :
  ∀ {n} → ModeNorm.PositiveNat n → suc zero ≤ n
positiveNatAtLeastOne (ModeNorm.positive-suc n) = s≤s z≤n

nonzeroLatticeSquaredDisplacementAtLeastOne :
  (shift : Z3.FourierMode) →
  Z3.NonZeroMode shift →
  1ℚ ≤ latticeSquaredDisplacement shift
nonzeroLatticeSquaredDisplacementAtLeastOne shift nonzero =
  Scale.natAsRationalMonotone
    (positiveNatAtLeastOne
      (ModeNorm.nonzeroModeNatNormPositive shift nonzero))

latticeHermitianG2 :
  (shift : Z3.FourierMode) →
  Z3.NonZeroMode shift →
  (XPlus XMinus D : C3.Complex3 G0.Weld.F) →
  ∣ G0.hermitianScalar XPlus D - G0.hermitianScalar XMinus D ∣
  ≤
  latticeSquaredDisplacement shift
    * (G2.two * G1.stateAmplitudeEnvelope XPlus XMinus D)
latticeHermitianG2 shift nonzero XPlus XMinus D =
  G2.discreteHermitianG2
    XPlus XMinus D
    (latticeSquaredDisplacement shift)
    (nonzeroLatticeSquaredDisplacementAtLeastOne shift nonzero)

r571LiteralLatticeDisplacementG2Closed : Bool
r571LiteralLatticeDisplacementG2Closed = true

r571PeriodicStateSideRequiresFrequencyDifferentiability : Bool
r571PeriodicStateSideRequiresFrequencyDifferentiability = false

r571RadialSideUsesSameSquaredDisplacementClosedHere : Bool
r571RadialSideUsesSameSquaredDisplacementClosedHere = false

r571CutoffUniformFamilyAmplitudeClosedHere : Bool
r571CutoffUniformFamilyAmplitudeClosedHere = false

clayPromotion : Bool
clayPromotion = false

r571LiteralLatticeDisplacementG2ClosedIsTrue :
  r571LiteralLatticeDisplacementG2Closed ≡ true
r571LiteralLatticeDisplacementG2ClosedIsTrue = refl

r571PeriodicStateSideRequiresFrequencyDifferentiabilityIsFalse :
  r571PeriodicStateSideRequiresFrequencyDifferentiability ≡ false
r571PeriodicStateSideRequiresFrequencyDifferentiabilityIsFalse = refl
