module DASHI.Biology.MoonshineOrbifoldSectorProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- Chongying Dong, Haisheng Li and Geoffrey Mason,
-- "Modular-Invariance of Trace Functions in Orbifold Theory and Generalized
-- Moonshine".
-- DOI: 10.1007/s002200000242.
--
-- James Lepowsky and Haisheng Li,
-- "Introduction to Vertex Operator Algebras and Their Representations".
-- DOI: 10.1007/978-0-8176-8186-9.
--
-- DASHI CONTRIBUTION
--
-- Give an exact rational regression for the Z/2 eigenspace projections used
-- in an orbifold construction.  For the involution swapping two coordinates,
--
--   P+(x,y) = ((x+y)/2,(x+y)/2),
--   P-(x,y) = ((x-y)/2,(y-x)/2),
--
-- we prove decomposition, parity and idempotence coordinate by coordinate.
-- The Moonshine orbifold has two distinct inputs: the untwisted fixed sector
-- and the selected parity sector of a twisted module.  The fixed-point algebra
-- alone is therefore not the full orbifold extension.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Integer.Base using (+_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; -_; _/_)
open import Data.Rational.Tactic.RingSolver using (solve)

record RationalPair : Set where
  constructor pair
  field
    first second : ℚ

open RationalPair public

swap : RationalPair → RationalPair
swap value = pair (second value) (first value)

positiveProjection : RationalPair → RationalPair
positiveProjection value =
  pair
    ((+ 1 / 2) * (first value + second value))
    ((+ 1 / 2) * (first value + second value))

negativeProjection : RationalPair → RationalPair
negativeProjection value =
  pair
    ((+ 1 / 2) * (first value - second value))
    ((+ 1 / 2) * (second value - first value))

positivePlusNegativeFirst :
  (value : RationalPair) →
  first (positiveProjection value)
    + first (negativeProjection value)
  ≡ first value
positivePlusNegativeFirst (pair x y) = solve (x ∷ y ∷ [])

positivePlusNegativeSecond :
  (value : RationalPair) →
  second (positiveProjection value)
    + second (negativeProjection value)
  ≡ second value
positivePlusNegativeSecond (pair x y) = solve (x ∷ y ∷ [])

positiveProjectionSwapInvariantFirst :
  (value : RationalPair) →
  first (positiveProjection (swap value))
  ≡ first (positiveProjection value)
positiveProjectionSwapInvariantFirst (pair x y) = solve (x ∷ y ∷ [])

positiveProjectionSwapInvariantSecond :
  (value : RationalPair) →
  second (positiveProjection (swap value))
  ≡ second (positiveProjection value)
positiveProjectionSwapInvariantSecond (pair x y) = solve (x ∷ y ∷ [])

negativeProjectionSwapOddFirst :
  (value : RationalPair) →
  first (negativeProjection (swap value))
  ≡ - first (negativeProjection value)
negativeProjectionSwapOddFirst (pair x y) = solve (x ∷ y ∷ [])

negativeProjectionSwapOddSecond :
  (value : RationalPair) →
  second (negativeProjection (swap value))
  ≡ - second (negativeProjection value)
negativeProjectionSwapOddSecond (pair x y) = solve (x ∷ y ∷ [])

positiveProjectionIdempotentFirst :
  (value : RationalPair) →
  first (positiveProjection (positiveProjection value))
  ≡ first (positiveProjection value)
positiveProjectionIdempotentFirst (pair x y) = solve (x ∷ y ∷ [])

positiveProjectionIdempotentSecond :
  (value : RationalPair) →
  second (positiveProjection (positiveProjection value))
  ≡ second (positiveProjection value)
positiveProjectionIdempotentSecond (pair x y) = solve (x ∷ y ∷ [])

negativeProjectionIdempotentFirst :
  (value : RationalPair) →
  first (negativeProjection (negativeProjection value))
  ≡ first (negativeProjection value)
negativeProjectionIdempotentFirst (pair x y) = solve (x ∷ y ∷ [])

negativeProjectionIdempotentSecond :
  (value : RationalPair) →
  second (negativeProjection (negativeProjection value))
  ≡ second (negativeProjection value)
negativeProjectionIdempotentSecond (pair x y) = solve (x ∷ y ∷ [])

data OrbifoldSector : Set where
  untwistedFixedSector : OrbifoldSector
  twistedPositiveSector : OrbifoldSector

orbifoldSectorsDistinct :
  untwistedFixedSector ≡ twistedPositiveSector → ⊥
orbifoldSectorsDistinct ()

record MoonshineOrbifoldAssemblyBoundary : Set where
  constructor moonshineOrbifoldAssemblyBoundary
  field
    fixedPointSectorConstructed : Set
    twistedModuleConstructed : Set
    localityOfExtensionProved : Set
    moonshineVOAIdentified : Set

-- This record is intentionally a target surface.  The exact P+/P- algebra
-- above is proved; the Leech-lattice VOA, its twisted module and the locality
-- theorem for their extension are not fabricated by the finite regression.
