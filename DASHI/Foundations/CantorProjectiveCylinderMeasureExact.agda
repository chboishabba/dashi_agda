module DASHI.Foundations.CantorProjectiveCylinderMeasureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.List.Base using (length)
open import Data.Rational.Base using (ℚ; 1ℚ; _+_)

import DASHI.Analysis.CanonicalRationalMetric as Metric

------------------------------------------------------------------------
-- INFINITE POLAR CARRIER AND CYLINDER PREMEASURE
--
-- An infinite Cantor address is represented by a binary stream; false/true are
-- embedded as ternary digits 0/2.  Finite prefixes generate cylinder events.
-- The exact cylinder mass is dyadicQ(length prefix) = 2^{-length prefix}.
------------------------------------------------------------------------

BitStream : Set
BitStream = Nat → Bool

data CantorTrit : Set where
  leftTrit rightTrit : CantorTrit

cantorTritOfBit : Bool → CantorTrit
cantorTritOfBit false = leftTrit
cantorTritOfBit true = rightTrit

CantorTernaryStream : Set
CantorTernaryStream = Nat → CantorTrit

embedPolarStream : BitStream → CantorTernaryStream
embedPolarStream stream n = cantorTritOfBit (stream n)

record Cylinder : Set where
  constructor cylinder
  field
    prefix : List Bool

open Cylinder public

cylinderDepth : Cylinder → Nat
cylinderDepth event = length (prefix event)

cylinderMass : Cylinder → ℚ
cylinderMass event = Metric.dyadicQ (cylinderDepth event)

rootCylinder : Cylinder
rootCylinder = cylinder []

rootCylinderHasUnitMass : cylinderMass rootCylinder ≡ 1ℚ
rootCylinderHasUnitMass = refl

leftChild rightChild : Cylinder → Cylinder
leftChild (cylinder prefix) = cylinder (false ∷ prefix)
rightChild (cylinder prefix) = cylinder (true ∷ prefix)

childDepthIncrements :
  (event : Cylinder) → cylinderDepth (leftChild event) ≡ suc (cylinderDepth event)
childDepthIncrements (cylinder prefix) = refl

leftAndRightChildHaveSameMass :
  (event : Cylinder) → cylinderMass (leftChild event) ≡ cylinderMass (rightChild event)
leftAndRightChildHaveSameMass (cylinder prefix) = refl

parentMassSplitsExactly :
  (event : Cylinder) →
  cylinderMass (leftChild event) + cylinderMass (rightChild event)
  ≡ cylinderMass event
parentMassSplitsExactly (cylinder prefix) =
  Metric.dyadicDoubleStepℚ (length prefix)

------------------------------------------------------------------------
-- Projective consistency: refining by any one binary decision preserves total
-- mass exactly.  Repeating this identity gives every finite layer total mass 1.
------------------------------------------------------------------------

record PolarCylinderPremeasure : Set₁ where
  constructor polarCylinderPremeasure
  field
    mass : Cylinder → ℚ
    rootUnit : mass rootCylinder ≡ 1ℚ
    binaryConsistency :
      (event : Cylinder) →
      mass (leftChild event) + mass (rightChild event) ≡ mass event

open PolarCylinderPremeasure public

canonicalPolarCylinderPremeasure : PolarCylinderPremeasure
canonicalPolarCylinderPremeasure =
  polarCylinderPremeasure cylinderMass rootCylinderHasUnitMass parentMassSplitsExactly

------------------------------------------------------------------------
-- Support statement: every infinite polar path maps to a ternary stream whose
-- digits are only left/right Cantor digits.  No middle digit exists in this
-- carrier, so the support is intrinsically Cantor-polar rather than ambient
-- ternary.
------------------------------------------------------------------------

data PolarDigit : CantorTrit → Set where
  leftIsPolar : PolarDigit leftTrit
  rightIsPolar : PolarDigit rightTrit

embeddedStreamIsPolar :
  (stream : BitStream) → (n : Nat) → PolarDigit (embedPolarStream stream n)
embeddedStreamIsPolar stream n with stream n
... | false = leftIsPolar
... | true = rightIsPolar

------------------------------------------------------------------------
-- Boundary: this is an infinite carrier plus an exact finitely/projectively
-- consistent rational cylinder premeasure.  Countable additivity and extension
-- from the cylinder algebra to a sigma-algebra remain separate measure-theory
-- obligations; they are not inferred from finite consistency alone.
------------------------------------------------------------------------
