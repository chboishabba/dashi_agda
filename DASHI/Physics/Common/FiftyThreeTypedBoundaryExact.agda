module DASHI.Physics.Common.FiftyThreeTypedBoundaryExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Keep two independently derived occurrences of 53 in different types:
--
--   * 53 fluctuation dimensions from 54 = 1 + 53;
--   * the rational high--low kernel budget 53/6 = 11/6 + 5 + 2.
--
-- The arithmetic relations are checked, while the type boundary prevents the
-- dimension deficit from being silently identified with an analytic kernel
-- mass.  No external theorem is imported by this repository-original audit.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base using (+_)
open import Data.Nat.Base using (ℕ; _+_) renaming (ℕ to Nat)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base as ℚ using
  (ℚ; _+_; _-_; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing

record DimensionDeficit : Set where
  constructor dimensionDeficit
  field
    dimensions : Nat

open DimensionDeficit public

record KernelMass : Set where
  constructor kernelMass
  field
    mass : ℚ

open KernelMass public

dashiReducedFiftyThree : DimensionDeficit
dashiReducedFiftyThree = dimensionDeficit 53

navierStokesHighLowFiftyThreeSixths : KernelMass
navierStokesHighLowFiftyThreeSixths = kernelMass (+ 53 / 6)

sixByNineSplitExact :
  54 ≡ 1 + dimensions dashiReducedFiftyThree
sixByNineSplitExact = refl

highLowKernelPartitionExact :
  mass navierStokesHighLowFiftyThreeSixths
  ≡ (+ 11 / 6) + 5 + 2
highLowKernelPartitionExact =
  ℚRing.solve-∀

highLowKernelAsNonaryDefectExact :
  mass navierStokesHighLowFiftyThreeSixths
  ≡ 9 - (+ 1 / 6)
highLowKernelAsNonaryDefectExact =
  ℚRing.solve-∀

sixTimesHighLowKernelMassIsFiftyThree :
  6 * mass navierStokesHighLowFiftyThreeSixths ≡ 53
sixTimesHighLowKernelMassIsFiftyThree =
  ℚRing.solve-∀

data QuantityKind : Set where
  dimensionQuantity : QuantityKind
  analyticKernelQuantity : QuantityKind

kindOfDimensionDeficit : DimensionDeficit → QuantityKind
kindOfDimensionDeficit deficit = dimensionQuantity

kindOfKernelMass : KernelMass → QuantityKind
kindOfKernelMass kernel = analyticKernelQuantity

fiftyThreeOccurrencesRemainTypeDistinct :
  kindOfDimensionDeficit dashiReducedFiftyThree ≡ dimensionQuantity
  × kindOfKernelMass navierStokesHighLowFiftyThreeSixths
    ≡ analyticKernelQuantity
fiftyThreeOccurrencesRemainTypeDistinct = refl , refl
