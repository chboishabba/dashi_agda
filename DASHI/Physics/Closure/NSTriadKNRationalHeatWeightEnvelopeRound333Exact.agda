module DASHI.Physics.Closure.NSTriadKNRationalHeatWeightEnvelopeRound333Exact where

------------------------------------------------------------------------
-- ROUND333 / LEAST-PRIVILEGE RATIONAL ENVELOPE FOR THE HEAT WEIGHT
--
-- R295 deliberately keeps the swap-invariant scalar weight abstract.  The
-- repository's genuine exponential implementation lives on Bishop reals, not
-- on the rational C3 Galerkin field.  Do not inject a transcendental scalar
-- into the rational physical carrier merely to run the Schur estimate.
--
-- The row/column consumer needs only a nonnegative rational majorant
--
--   |w(tau)|^2 <= H(tau).
--
-- This file installs exactly that interface.  A future Bishop/heat bridge may
-- produce H, but the finite shell proof can proceed using H without claiming
-- that the rational complex weight itself is an exact exponential.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Symmetry
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as L2
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNResolventWeightedMixedCommutatorRound294Exact as R294

F : C3.RealField _
F = Rational.rationalRealField

record RationalSquaredWeightEnvelope
    (W : R294.SwapInvariantCellWeight F) : Set where
  constructor rational-squared-weight-envelope
  field
    envelope : Physical.PhysicalTriadIncidence → ℚ
    envelopeNonnegative :
      (tau : Physical.PhysicalTriadIncidence) → 0ℚ ≤ envelope tau
    weightSquaredBelowEnvelope :
      (tau : Physical.PhysicalTriadIncidence) →
      L2.complexModulusSquared (R294.weight W tau) ≤ envelope tau

open RationalSquaredWeightEnvelope public

record SwapInvariantEnvelope
    (W : R294.SwapInvariantCellWeight F)
    (H : RationalSquaredWeightEnvelope W) : Set where
  constructor swap-invariant-envelope
  field
    envelopeSwapInvariant :
      (tau : Physical.PhysicalTriadIncidence) →
      envelope H (Symmetry.swapTriad tau) ≡ envelope H tau

round333ExactExponentialInsertedIntoRationalC3 : Bool
round333ExactExponentialInsertedIntoRationalC3 = false

round333RationalSquaredWeightEnvelopeInterfaceClosed : Bool
round333RationalSquaredWeightEnvelopeInterfaceClosed = true

round333BishopHeatRealizationToEnvelopeClosed : Bool
round333BishopHeatRealizationToEnvelopeClosed = false

round333WeightedRowShellBudgetClosed : Bool
round333WeightedRowShellBudgetClosed = false

round333NumericalColumnBudgetClosed : Bool
round333NumericalColumnBudgetClosed = false

round333PackageAClosed : Bool
round333PackageAClosed = false

round333ClayPromotion : Bool
round333ClayPromotion = false
