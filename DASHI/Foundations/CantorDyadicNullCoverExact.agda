module DASHI.Foundations.CantorDyadicNullCoverExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 1ℚ; _≤_)

import DASHI.Analysis.CanonicalRationalMetric as Metric
import DASHI.Foundations.CantorAmbientWidthDecayExact as Width
import DASHI.Foundations.CantorProjectiveCylinderMeasureExact as Measure

------------------------------------------------------------------------
-- CONSTRUCTIVE DYADIC NULL-COVER CERTIFICATE
--
-- At stage n the ordinary ternary Cantor survivor is covered by its 2^n
-- surviving intervals with total width (2/3)^n.  The existing ambient-width
-- theorem gives the explicit modulus n = 2k for dyadic tolerance 2^-k.
------------------------------------------------------------------------

record DyadicNullCover (precision : Nat) : Set where
  constructor dyadicNullCover
  field
    coverDepth : Nat
    totalAmbientWidth : ℚ
    widthIsStageWidth : totalAmbientWidth ≡ Width.ambientWidth coverDepth
    belowTolerance : totalAmbientWidth ≤ Metric.dyadicQ precision

open DyadicNullCover public

canonicalDyadicNullCover : (precision : Nat) → DyadicNullCover precision
canonicalDyadicNullCover precision =
  dyadicNullCover
    (Width.evenDepth precision)
    (Width.ambientWidth (Width.evenDepth precision))
    refl
    (Width.ambientWidthAtEvenDepthBelowDyadic precision)

record CantorNullCoverModulus : Set where
  constructor cantorNullCoverModulus
  field
    coverAtPrecision : (precision : Nat) → DyadicNullCover precision

open CantorNullCoverModulus public

canonicalCantorNullCoverModulus : CantorNullCoverModulus
canonicalCantorNullCoverModulus = cantorNullCoverModulus canonicalDyadicNullCover

------------------------------------------------------------------------
-- Intrinsic/projective mass remains a separate certificate.
------------------------------------------------------------------------

intrinsicRootMassIsUnit :
  Measure.cylinderMass Measure.rootCylinder ≡ 1ℚ
intrinsicRootMassIsUnit = Measure.rootCylinderHasUnitMass

ambientNullCoverAndIntrinsicUnitMass :
  CantorNullCoverModulus
  × (Measure.cylinderMass Measure.rootCylinder ≡ 1ℚ)
ambientNullCoverAndIntrinsicUnitMass =
  canonicalCantorNullCoverModulus , intrinsicRootMassIsUnit

------------------------------------------------------------------------
-- This is the constructive covering content behind lambda(C)=0: arbitrarily
-- small dyadic total-width covers are explicit.  It still does not manufacture
-- a sigma-algebra or identify projective cylinder mass with a countably
-- additive measure on that sigma-algebra.
------------------------------------------------------------------------
