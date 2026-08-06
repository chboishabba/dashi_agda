module DASHI.Physics.Common.TrivialRepresentationReductionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics
-- 129, Springer, 1991.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Fan R. K. Chung,
-- "Spectral Graph Theory", CBMS Regional Conference Series in Mathematics
-- 92, American Mathematical Society, 1997.
-- DOI: 10.1090/cbms/092.
--
-- DASHI CONTRIBUTION
--
-- Make the intended meaning of 54 - 1 precise: the subtraction is removal of
-- one declared trivial/invariant summand from a 54-dimensional permutation
-- carrier.  The resulting reduced carrier has dimension 53.
--
-- This is stronger than an untyped arithmetic remainder, but weaker than a
-- Monster-theoretic identification.  No irreducibility, Monster action, or
-- relation to the 196883-dimensional Monster representation is asserted.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_)

record RepresentationReduction : Set where
  constructor representationReduction
  field
    totalDimension : Nat
    trivialMultiplicity : Nat
    reducedDimension : Nat
    directSumDimension :
      totalDimension ≡ trivialMultiplicity + reducedDimension

open RepresentationReduction public

sixByNineTrivialReduction : RepresentationReduction
sixByNineTrivialReduction = representationReduction 54 1 53 refl

sixByNineCarrierIsTrivialPlusReduced :
  totalDimension sixByNineTrivialReduction
  ≡ trivialMultiplicity sixByNineTrivialReduction
    + reducedDimension sixByNineTrivialReduction
sixByNineCarrierIsTrivialPlusReduced =
  directSumDimension sixByNineTrivialReduction

------------------------------------------------------------------------
-- Typed semantic boundary.
------------------------------------------------------------------------

data ReductionMeaning : Set where
  removeTrivialRepresentation : ReductionMeaning
  arbitraryNumericRemainder : ReductionMeaning
  monsterModuleIdentification : ReductionMeaning

meaningOfSixByNineMinusOne : ReductionMeaning
meaningOfSixByNineMinusOne = removeTrivialRepresentation

sixByNineMinusOneIsTrivialReduction :
  meaningOfSixByNineMinusOne ≡ removeTrivialRepresentation
sixByNineMinusOneIsTrivialReduction = refl

record TrivialReductionBoundary : Set where
  constructor trivialReductionBoundary
  field
    reductionSuppliesCanonicalCarrierDecomposition : Set
    reductionSuppliesCanonicalCarrierDecompositionWitness :
      reductionSuppliesCanonicalCarrierDecomposition

    reductionProvesReducedCarrierIrreducible : Set
    reductionDoesNotProveReducedCarrierIrreducible :
      reductionProvesReducedCarrierIrreducible → Set

    reductionIdentifiesMonsterRepresentation : Set
    reductionDoesNotIdentifyMonsterRepresentation :
      reductionIdentifiesMonsterRepresentation → Set

canonicalTrivialReductionBoundary : TrivialReductionBoundary
canonicalTrivialReductionBoundary =
  trivialReductionBoundary
    ⊤ tt
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
  where
  open import Data.Unit using (⊤; tt)
  open import Data.Empty using (⊥)
