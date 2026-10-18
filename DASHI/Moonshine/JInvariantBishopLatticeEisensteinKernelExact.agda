module DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact where

------------------------------------------------------------------------
-- LITERAL BISHOP-COMPLEX EISENSTEIN LATTICE KERNEL
--
-- This owner constructs the actual denominator expression
--
--     m * tau + n
--
-- for integer lattice coordinates on the same Bishop complex carrier as the
-- q-series theorem, and then constructs its reciprocal powers.
--
-- The only semantic input not manufactured here is denominator nonzeroness for
-- nonzero lattice points.  That is isolated as a geometry certificate so that
-- the subsequent upper-half-plane proof cannot be confused with summability
-- or modularity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Integer.Base using (ℤ; +_; -[1+_])

import Real as BishopReal

import DASHI.Analysis.BishopComplexSeriesConvergenceExact as Complex
import DASHI.Analysis.BishopComplexAlgebraExact as Algebra
import DASHI.Analysis.BishopComplexReciprocalExact as Reciprocal
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Lattice

embedInteger : ℤ → BishopReal.ℝ
embedInteger (+ n) = NatReal.natReal n
embedInteger (-[1+ n ]) =
  BishopReal.- (NatReal.natReal (suc n))

integerAsComplex : ℤ → Complex.BishopComplex
integerAsComplex integer =
  Complex.complex (embedInteger integer) BishopReal.0ℝ

integerScaleComplex :
  ℤ → Complex.BishopComplex → Complex.BishopComplex
integerScaleComplex integer value =
  Algebra.scaleC (embedInteger integer) value

latticeDenominator :
  Lattice.LatticePoint →
  Complex.BishopComplex →
  Complex.BishopComplex
latticeDenominator point tau =
  Algebra._+C_
    (integerScaleComplex (Lattice.horizontal point) tau)
    (integerAsComplex (Lattice.vertical point))

origin : Lattice.LatticePoint
origin = Lattice.lattice-point (+ 0) (+ 0)

_≢_ : ∀ {A : Set} → A → A → Set
left ≢ right = left ≡ right → Lattice.⊥

record NonzeroLatticePoint : Set where
  constructor nonzero-lattice-point
  field
    point : Lattice.LatticePoint
    notOrigin : point ≢ origin

open NonzeroLatticePoint public

record BishopLatticeDenominatorGeometry
    (Parameter : Set)
    (tauOf : Parameter → Complex.BishopComplex) : Set₁ where
  field
    denominatorNonzero :
      (parameter : Parameter) →
      (index : NonzeroLatticePoint) →
      Reciprocal.BishopComplexNonzero
        (latticeDenominator (point index) (tauOf parameter))

open BishopLatticeDenominatorGeometry public

latticeReciprocal :
  ∀ {Parameter tauOf} →
  BishopLatticeDenominatorGeometry Parameter tauOf →
  Parameter →
  NonzeroLatticePoint →
  Complex.BishopComplex
latticeReciprocal geometry parameter index =
  Reciprocal.reciprocalC
    denominator
    (denominatorNonzero geometry parameter index)
  where
    denominator =
      latticeDenominator (point index) (tauOf parameter)

latticeEisensteinSummand :
  ∀ {Parameter tauOf} →
  BishopLatticeDenominatorGeometry Parameter tauOf →
  Nat →
  NonzeroLatticePoint →
  Parameter →
  Complex.BishopComplex
latticeEisensteinSummand geometry weight index parameter =
  Algebra.powC
    (latticeReciprocal geometry parameter index)
    weight

record BishopLiteralLatticeKernelBoundary : Set where
  field
    concreteIntegerEmbeddingConstructed : Bool
    literalMτPlusNConstructed : Bool
    complexReciprocalConstructed : Bool
    literalInversePowerSummandConstructed : Bool
    upperHalfPlaneDenominatorNonzeroProvedHere : Bool
    z2AbsoluteSummabilityProvedHere : Bool

canonicalBishopLiteralLatticeKernelBoundary :
  BishopLiteralLatticeKernelBoundary
canonicalBishopLiteralLatticeKernelBoundary = record
  { concreteIntegerEmbeddingConstructed = true
  ; literalMτPlusNConstructed = true
  ; complexReciprocalConstructed = true
  ; literalInversePowerSummandConstructed = true
  ; upperHalfPlaneDenominatorNonzeroProvedHere = false
  ; z2AbsoluteSummabilityProvedHere = false
  }
