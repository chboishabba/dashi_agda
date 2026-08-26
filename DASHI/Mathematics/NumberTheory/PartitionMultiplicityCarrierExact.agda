module DASHI.Mathematics.NumberTheory.PartitionMultiplicityCarrierExact where

------------------------------------------------------------------------
-- INTEGER PARTITIONS AS MULTIPLICITY VECTORS
--
-- A partition of n can be represented by multiplicities
--
--   (m_1 , ... , m_n)
--
-- satisfying
--
--   1*m_1 + 2*m_2 + ... + n*m_n = n.
--
-- This representation is tailored to the Erdos deletion identity: deleting k
-- copies of a part of size v is a coordinate operation, and the conventional
-- coefficient v is represented independently by a Fin v unit fibre.
--
-- This module owns the all-n *carrier shape*.  Finite enumeration of all such
-- vectors and the exact coordinate-deletion bijection are kept as explicit
-- subsequent theorem layers.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin; toℕ)
open import Data.Vec.Base using (Vec; []; _∷_)

------------------------------------------------------------------------
-- Weighted mass of a multiplicity vector.  The first coordinate has the
-- supplied positive part size, and later coordinates increase it by one.

weightedMassFrom :
  ∀ {dimension : Nat} → Nat → Vec Nat dimension → Nat
weightedMassFrom first [] = 0
weightedMassFrom first (multiplicity ∷ rest) =
  first * multiplicity + weightedMassFrom (suc first) rest

weightedMass :
  ∀ {n : Nat} → Vec Nat n → Nat
weightedMass = weightedMassFrom 1

record MultiplicityPartition (n : Nat) : Set where
  constructor multiplicityPartition
  field
    multiplicities : Vec Nat n
    massExact : weightedMass multiplicities ≡ n

open MultiplicityPartition public

------------------------------------------------------------------------
-- Coordinate / part-size interpretation.

partValue : ∀ {n : Nat} → Fin n → Nat
partValue index = suc (toℕ index)

record PositiveDeletionChoice {n : Nat}
    (partition : MultiplicityPartition n) : Set where
  field
    partIndex : Fin n
    copies : Nat

    -- These propositions intentionally state only the local coordinate facts.
    -- The subsequent exact deletion owner constructs the updated vector and
    -- proves its mass is n - copies*partValue.
    copiesPositive : Set
    copiesAvailable : Set

open PositiveDeletionChoice public

------------------------------------------------------------------------
-- Classical residual coordinate.  Rather than hiding the factor v as a
-- coefficient, retain an explicit Fin v label.  A residual therefore carries
-- (v,k,mu,u), with u : Fin v.

record ErdosMultiplicityResidual (n : Nat) : Set where
  constructor erdosMultiplicityResidual
  field
    partIndex : Fin n
    copies : Nat
    residualMass : Nat
    residualPartition : MultiplicityPartition residualMass
    decompositionExact :
      residualMass + copies * partValue partIndex ≡ n
    unit : Fin (partValue partIndex)

open ErdosMultiplicityResidual public

------------------------------------------------------------------------
-- Forgetting the unit coordinate produces the conventional weighted triple.

record ErdosResidualTriple (n : Nat) : Set where
  constructor erdosResidualTriple
  field
    partIndex : Fin n
    copies : Nat
    residualMass : Nat
    residualPartition : MultiplicityPartition residualMass
    decompositionExact :
      residualMass + copies * partValue partIndex ≡ n

open ErdosResidualTriple public

tripleWeight : ∀ {n : Nat} → ErdosResidualTriple n → Nat
tripleWeight triple = partValue (ErdosResidualTriple.partIndex triple)

------------------------------------------------------------------------
-- Completion boundary.  The carrier itself is no longer missing; what remains
-- is finite exhaustivity/uniqueness and exact coordinate deletion.

record MultiplicityPartitionEnumerationCompletion : Set₁ where
  field
    enumeratePartitions :
      (n : Nat) → Set
    enumerationFiniteExact :
      (n : Nat) → Set
    enumerationUniqueExact :
      (n : Nat) → Set
    enumerationSoundExact :
      (n : Nat) → Set
    enumerationCompleteExact :
      (n : Nat) → Set

record MultiplicityDeletionCompletion : Set₁ where
  field
    subtractCopiesAtCoordinateExact : Set
    residualMassExact : Set
    markedUnitToResidualExact : Set
    residualToMarkedUnitExact : Set
    deletionInverseLawsExact : Set

------------------------------------------------------------------------
-- No analytic input appears here.  In particular the Bishop submodule is not
-- imported into this combinatorial carrier.
------------------------------------------------------------------------
