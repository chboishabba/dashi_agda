module DASHI.Biology.MoonshineConformalReductionVsFiftyFourReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Igor Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course".
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
-- Answer the exact question whether the conformal-vector line removed from
-- 196884 to obtain the 196883-dimensional Monster constituent is "the same"
-- as the invariant line removed in 54 = 1 + 53.  They instantiate the same
-- abstract one-plus-reduced dimension pattern, but they are different typed
-- lines in different carriers; no identification map is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_)

import DASHI.Biology.MoonshineVacuumConformalLineBoundaryExact as Moonshine
import DASHI.Biology.JCompletionTrivialLineSeparationExact as Reduced54

record OnePlusReduction : Set where
  constructor onePlusReduction
  field
    totalDimension : Nat
    reducedDimension : Nat
    totalIsOnePlusReduced :
      totalDimension ≡ 1 + reducedDimension

open OnePlusReduction public

moonshineWeightTwoReduction : OnePlusReduction
moonshineWeightTwoReduction =
  onePlusReduction 196884 196883 refl

fiftyFourToFiftyThreeReduction : OnePlusReduction
fiftyFourToFiftyThreeReduction =
  onePlusReduction 54 53 refl

sameReductionCoefficient : Nat
sameReductionCoefficient = 1

moonshineRemovedMultiplicityIsOne :
  Moonshine.weightTwoConformalMultiplicity ≡ sameReductionCoefficient
moonshineRemovedMultiplicityIsOne = refl

fiftyFourRemovedMultiplicityIsOne :
  Reduced54.roleMultiplicity Reduced54.removedTrivialRepresentation
  ≡ sameReductionCoefficient
fiftyFourRemovedMultiplicityIsOne = refl

data ConcreteRemovedLine : Set where
  moonshineConformalRemovedLine : ConcreteRemovedLine
  fiftyFourInvariantRemovedLine : ConcreteRemovedLine

removedLinesAreDistinct :
  moonshineConformalRemovedLine ≡ fiftyFourInvariantRemovedLine → ⊥
removedLinesAreDistinct ()

record ReductionComparison : Set where
  constructor reductionComparison
  field
    leftReduction : OnePlusReduction
    rightReduction : OnePlusReduction
    equalRemovedMultiplicity : Nat
    concreteLinesIdentified : Set
    concreteLinesNotIdentified : concreteLinesIdentified → Set

canonicalReductionComparison : ReductionComparison
canonicalReductionComparison =
  reductionComparison
    moonshineWeightTwoReduction
    fiftyFourToFiftyThreeReduction
    sameReductionCoefficient
    ⊥
    (λ impossible → ⊥)

record ReductionAuthorityBoundary : Set where
  constructor reductionAuthorityBoundary
  field
    equalDimensionPatternProvesSameRepresentation : Set
    equalDimensionPatternDoesNotProveSameRepresentation :
      equalDimensionPatternProvesSameRepresentation → Set

    reducedFiftyThreeIsMoonshineWeightTwoConstituent : Set
    reducedFiftyThreeIsNotIdentifiedWithMoonshineConstituent :
      reducedFiftyThreeIsMoonshineWeightTwoConstituent → Set

canonicalReductionAuthorityBoundary : ReductionAuthorityBoundary
canonicalReductionAuthorityBoundary =
  reductionAuthorityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
