module DASHI.Mathematics.Algebra.NoetherianityMeaningSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Emmy Noether,
-- "Idealtheorie in Ringbereichen", Mathematische Annalen 83 (1921),
-- 24--66.
-- DOI: 10.1007/BF01464225.
--
-- David Eisenbud,
-- "Commutative Algebra: with a View Toward Algebraic Geometry".
-- DOI: 10.1007/978-1-4612-5350-1.
--
-- Emmy Noether,
-- "Invariante Variationsprobleme" (1918).  No DOI was assigned to the
-- original; M. A. Tavel translation:
-- DOI: 10.48550/arXiv.physics/0503066.
--
-- DASHI CONTRIBUTION
--
-- Keep Noether's two relevant legacies type-distinct.  Variational symmetry
-- and Noetherian finite-generation/ascending-chain data are not interchangeable
-- merely because they share an author.  The records below expose the correct
-- obligation surfaces for future algebraic-geometry, invariant-ring and PDE
-- integrations without claiming the equivalence of standard Noetherianity
-- characterizations for an arbitrary ring.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_+_)

data NoetherThread : Set where
  variationalSymmetryThread : NoetherThread
  noetherianAlgebraThread : NoetherThread

noetherianityIsNotVariationalSymmetry :
  noetherianAlgebraThread ≡ variationalSymmetryThread → ⊥
noetherianityIsNotVariationalSymmetry ()

record AscendingChainCondition : Set₁ where
  field
    IdealCarrier : Set
    included : IdealCarrier → IdealCarrier → Set
    chain : Nat → IdealCarrier
    ascending : ∀ index → included (chain index) (chain (index + 1))
    stabilizationIndex : Nat
    stableTail : ∀ offset →
      chain (stabilizationIndex + offset) ≡ chain stabilizationIndex

record FinitelyGeneratedIdealCondition : Set₁ where
  field
    RingCarrier : Set
    IdealCarrier : Set
    GeneratorCarrier : Set
    finiteGeneratorBound : Nat
    generates : GeneratorCarrier → IdealCarrier → Set
    everyIdealHasFiniteGenerators : Set

record NoetherianEquivalenceObligation : Set₁ where
  field
    ascendingChainCondition : AscendingChainCondition
    finiteGenerationCondition : FinitelyGeneratedIdealCondition
    accImpliesFiniteGeneration : Set
    finiteGenerationImpliesAcc : Set

record VariationalNoetherObligation : Set₁ where
  field
    fieldCarrier : Set
    oneParameterSymmetry : Set
    actionFunctional : Set
    firstVariationIdentity : Set
    currentCarrier : Set
    divergenceIdentity : Set

record CrossPollinatedNoetherSurface : Set₁ where
  field
    algebraicNoetherSurface : NoetherianEquivalenceObligation
    variationalNoetherSurface : VariationalNoetherObligation

-- CrossPollinatedNoetherSurface requires both threads but contains no field
-- identifying them.  The algebraic branch supports finite generation and
-- stabilization; the variational branch supports symmetry/current arguments.
