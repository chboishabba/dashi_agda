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
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Fin.Base using (Fin; toℕ)
  renaming (zero to fzero; suc to fsuc)
open import Data.Nat.Base using (_≤_; _<_)
import Data.Nat.Properties as NatP
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (subst)

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

lookupMultiplicity :
  ∀ {n : Nat} → Fin n → Vec Nat n → Nat
lookupMultiplicity fzero (x ∷ xs) = x
lookupMultiplicity (fsuc index) (x ∷ xs) =
  lookupMultiplicity index xs

partValue : ∀ {n : Nat} → Fin n → Nat
partValue index = suc (toℕ index)

coordinateWeightFrom :
  ∀ {n : Nat} → Nat → Fin n → Nat
coordinateWeightFrom first fzero = first
coordinateWeightFrom first (fsuc index) =
  coordinateWeightFrom (suc first) index

------------------------------------------------------------------------
-- Every coordinate and every weighted coordinate contribution are bounded by
-- the total positive-weighted mass.

coordinate≤weightedMassFrom :
  ∀ {dimension : Nat}
    (offset : Nat)
    (index : Fin dimension)
    (vector : Vec Nat dimension) →
  lookupMultiplicity index vector
  ≤ weightedMassFrom (suc offset) vector
coordinate≤weightedMassFrom offset fzero (multiplicity ∷ rest) =
  NatP.≤-trans
    (NatP.≤-trans
      (NatP.m≤m*n multiplicity (suc offset))
      (NatP.≤-reflexive (NatP.*-comm multiplicity (suc offset))))
    (NatP.m≤m+n
      ((suc offset) * multiplicity)
      (weightedMassFrom (suc (suc offset)) rest))
coordinate≤weightedMassFrom offset (fsuc index) (multiplicity ∷ rest) =
  NatP.≤-trans
    (coordinate≤weightedMassFrom (suc offset) index rest)
    (NatP.≤-trans
      (NatP.m≤m+n
        (weightedMassFrom (suc (suc offset)) rest)
        ((suc offset) * multiplicity))
      (NatP.≤-reflexive
        (NatP.+-comm
          (weightedMassFrom (suc (suc offset)) rest)
          ((suc offset) * multiplicity))))

coordinateContribution≤weightedMassFrom :
  ∀ {dimension : Nat}
    (first : Nat)
    (index : Fin dimension)
    (vector : Vec Nat dimension) →
  coordinateWeightFrom first index * lookupMultiplicity index vector
  ≤ weightedMassFrom first vector
coordinateContribution≤weightedMassFrom first fzero
    (multiplicity ∷ rest) =
  NatP.m≤m+n
    (first * multiplicity)
    (weightedMassFrom (suc first) rest)
coordinateContribution≤weightedMassFrom first (fsuc index)
    (multiplicity ∷ rest) =
  NatP.≤-trans
    (coordinateContribution≤weightedMassFrom (suc first) index rest)
    (NatP.≤-trans
      (NatP.m≤m+n
        (weightedMassFrom (suc first) rest)
        (first * multiplicity))
      (NatP.≤-reflexive
        (NatP.+-comm
          (weightedMassFrom (suc first) rest)
          (first * multiplicity))))

coordinate≤weightedMass :
  ∀ {n : Nat}
    (index : Fin n)
    (vector : Vec Nat n) →
  lookupMultiplicity index vector ≤ weightedMass vector
coordinate≤weightedMass = coordinate≤weightedMassFrom zero

partitionCoordinateAtMostGrade :
  ∀ {n : Nat}
    (partition : MultiplicityPartition n)
    (index : Fin n) →
  lookupMultiplicity index (multiplicities partition) ≤ n
partitionCoordinateAtMostGrade partition index =
  subst
    (λ total → lookupMultiplicity index (multiplicities partition) ≤ total)
    (massExact partition)
    (coordinate≤weightedMass index (multiplicities partition))

------------------------------------------------------------------------
-- If a coordinate's part weight lies strictly above the exact total mass, its
-- multiplicity must be zero.  This is the normalization lemma for ambient
-- residual vectors: all coordinates above residual mass vanish.

coordinateAboveExactMassIsZero :
  ∀ {dimension mass : Nat}
    (vector : Vec Nat dimension)
    (massExactProof : weightedMass vector ≡ mass)
    (index : Fin dimension) →
  mass < coordinateWeightFrom 1 index →
  lookupMultiplicity index vector ≡ zero
coordinateAboveExactMassIsZero vector massExactProof index above
  with lookupMultiplicity index vector
... | zero = refl
... | suc multiplicity =
  ⊥-elim
    (NatP.<⇒≱ above weight≤mass)
  where
  contribution≤mass :
    coordinateWeightFrom 1 index * suc multiplicity ≤ mass
  contribution≤mass =
    subst
      (λ total →
        coordinateWeightFrom 1 index * suc multiplicity ≤ total)
      massExactProof
      (coordinateContribution≤weightedMassFrom 1 index vector)

  weight≤contribution :
    coordinateWeightFrom 1 index
    ≤ coordinateWeightFrom 1 index * suc multiplicity
  weight≤contribution =
    NatP.m≤m*n (coordinateWeightFrom 1 index) (suc multiplicity)

  weight≤mass : coordinateWeightFrom 1 index ≤ mass
  weight≤mass = NatP.≤-trans weight≤contribution contribution≤mass

record PositiveDeletionChoice {n : Nat}
    (partition : MultiplicityPartition n) : Set where
  field
    partIndex : Fin n
    copies : Nat
    copiesPositive : suc zero ≤ copies
    copiesAvailable :
      copies ≤ lookupMultiplicity partIndex (multiplicities partition)

open PositiveDeletionChoice public

------------------------------------------------------------------------
-- Classical residual coordinate.  Rather than hiding the factor v as a
-- coefficient, retain an explicit Fin v label.

record ErdosMultiplicityResidual (n : Nat) : Set where
  constructor erdosMultiplicityResidual
  field
    partIndex : Fin n
    copies : Nat
    copiesPositive : suc zero ≤ copies
    residualMass : Nat
    residualPartition : MultiplicityPartition residualMass
    decompositionExact :
      residualMass + copies * partValue partIndex ≡ n
    unit : Fin (partValue partIndex)

open ErdosMultiplicityResidual public

record ErdosResidualTriple (n : Nat) : Set where
  constructor erdosResidualTriple
  field
    partIndex : Fin n
    copies : Nat
    copiesPositive : suc zero ≤ copies
    residualMass : Nat
    residualPartition : MultiplicityPartition residualMass
    decompositionExact :
      residualMass + copies * partValue partIndex ≡ n

open ErdosResidualTriple public

tripleWeight : ∀ {n : Nat} → ErdosResidualTriple n → Nat
tripleWeight triple = partValue (ErdosResidualTriple.partIndex triple)

------------------------------------------------------------------------
-- Remaining explicit normalization/deletion boundaries.

record MultiplicityPartitionEnumerationCompletion : Set₁ where
  field
    enumeratePartitions : (n : Nat) → Set
    enumerationFiniteExact : (n : Nat) → Set
    enumerationUniqueExact : (n : Nat) → Set
    enumerationSoundExact : (n : Nat) → Set
    enumerationCompleteExact : (n : Nat) → Set

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
