module DASHI.Biology.JCompletionTrivialLineSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
-- Type-separate the two unit phenomena in the structured carrier:
--
--   * the included j completion channel in T^2 disjoint-union {j};
--   * the removed trivial representation in V54 = 1 plus V53-reduced.
--
-- Both have scalar multiplicity one, but they are provably distinct
-- constructors with opposite construction roles.  The included j channel
-- contributes a full 3^9 elementary harmonic fibre, whereas the removed
-- invariant line produces the 54-to-53 reduction.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat using (_+_; _*_)

data UnitRole : Set where
  includedCompletionChannel : UnitRole
  removedTrivialRepresentation : UnitRole

roleMultiplicity : UnitRole → Nat
roleMultiplicity includedCompletionChannel = 1
roleMultiplicity removedTrivialRepresentation = 1

roleContribution : UnitRole → Nat
roleContribution includedCompletionChannel = 19683
roleContribution removedTrivialRepresentation = 1

unitRolesHaveEqualMultiplicity :
  roleMultiplicity includedCompletionChannel
  ≡ roleMultiplicity removedTrivialRepresentation
unitRolesHaveEqualMultiplicity = refl

unitRolesAreDistinct :
  includedCompletionChannel ≡ removedTrivialRepresentation → ⊥
unitRolesAreDistinct ()

coarseChannelCount : Nat
coarseChannelCount = 9 + roleMultiplicity includedCompletionChannel

coarseChannelCountExact : coarseChannelCount ≡ 10
coarseChannelCountExact = refl

completionFineContribution : Nat
completionFineContribution =
  roleMultiplicity includedCompletionChannel * 19683

completionFineContributionExact : completionFineContribution ≡ 19683
completionFineContributionExact = refl

reducedCarrierDimension : Nat
reducedCarrierDimension = 53

unreducedCarrierDimension : Nat
unreducedCarrierDimension =
  roleMultiplicity removedTrivialRepresentation + reducedCarrierDimension

unreducedCarrierDimensionExact : unreducedCarrierDimension ≡ 54
unreducedCarrierDimensionExact = refl

record UnitRoleBoundary : Set where
  constructor unitRoleBoundary
  field
    completionChannelIsKnownMonsterInvariantLine : Set
    completionChannelIsNotKnownMonsterInvariantLine :
      completionChannelIsKnownMonsterInvariantLine → Set

canonicalUnitRoleBoundary : UnitRoleBoundary
canonicalUnitRoleBoundary =
  unitRoleBoundary
    ⊥ (λ impossible → ⊥)
