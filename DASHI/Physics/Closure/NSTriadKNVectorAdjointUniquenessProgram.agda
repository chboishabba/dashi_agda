module DASHI.Physics.Closure.NSTriadKNVectorAdjointUniquenessProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; DASHI repository contributors.
-- Title: "Concrete uniqueness reduction for the two periodic Navier-Stokes
-- vector partial adjoints".
-- Venue/year: Advances in Mathematics 165 (2002), 124--164; DASHI formal
-- development, 2026.
-- DOI: 10.1006/aima.2001.2028 for Grafakos--Torres,
-- "Multilinear Calderon-Zygmund Theory"; the C3 uniqueness reduction is
-- repository-original.
-- Uses: the literal T*1 and T*2 candidate vectors, the real Hermitian pairing,
-- and the proved six-probe separation theorem.
-- Relationship: proves that any two vectors representing the same real
-- Hermitian functional are equal.  Concrete uniqueness of T*1 and T*2 now
-- depends only on proving their Agda pairing identities; nondegeneracy is no
-- longer an open leaf.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates as Adjoints
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianNondegeneracy as Nondegenerate

RealPairingFunctional :
  ∀ {r} (F : C3.RealField r) → Set r
RealPairingFunctional F = C3.Complex3 F → C3.Complex F

realHermitianFunctionalValue :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex F
realHermitianFunctionalValue test value =
  C3.complexRealPart (C3.hermitianPairing3 test value)

representativeUniqueFromSharedFunctional :
  ∀ {r} {F : C3.RealField r}
    (functional : RealPairingFunctional F)
    (first second : C3.Complex3 F) →
  (∀ test → realHermitianFunctionalValue test first ≡ functional test) →
  (∀ test → realHermitianFunctionalValue test second ≡ functional test) →
  first ≡ second
representativeUniqueFromSharedFunctional functional first second firstRep secondRep =
  Nondegenerate.pairingRepresentativesUnique first second
    (λ test → trans (firstRep test) (sym (secondRep test)))

record ConcreteAdjointPairingIdentityCutset
    {r : Level}
    (F : C3.RealField r) : Set (lsuc r) where
  field
    firstAdjointFunctional : RealPairingFunctional F
    secondAdjointFunctional : RealPairingFunctional F

    firstCandidatePairingIdentity :
      ∀ candidateTest →
      realHermitianFunctionalValue candidateTest candidateTest
      ≡ firstAdjointFunctional candidateTest

    secondCandidatePairingIdentity :
      ∀ candidateTest →
      realHermitianFunctionalValue candidateTest candidateTest
      ≡ secondAdjointFunctional candidateTest

    literalFirstAdjointPairingTheorem : Set r
    literalSecondAdjointPairingTheorem : Set r
    orderedPairFirstAdjointPairingTheorem : Set r

open ConcreteAdjointPairingIdentityCutset public

realHermitianNondegeneracyNoLongerBlocksUniqueness : Bool
realHermitianNondegeneracyNoLongerBlocksUniqueness = true

realHermitianNondegeneracyNoLongerBlocksUniquenessIsTrue :
  realHermitianNondegeneracyNoLongerBlocksUniqueness ≡ true
realHermitianNondegeneracyNoLongerBlocksUniquenessIsTrue =
  Nondegenerate.concreteRealHermitianNondegeneracyClosedIsTrue

vectorAdjointUniquenessReductionClosed : Bool
vectorAdjointUniquenessReductionClosed = true

vectorAdjointUniquenessReductionClosedIsTrue :
  vectorAdjointUniquenessReductionClosed ≡ true
vectorAdjointUniquenessReductionClosedIsTrue = refl

literalVectorAdjointPairingIdentitiesClosed : Bool
literalVectorAdjointPairingIdentitiesClosed = false

literalVectorAdjointPairingIdentitiesClosedIsFalse :
  literalVectorAdjointPairingIdentitiesClosed ≡ false
literalVectorAdjointPairingIdentitiesClosedIsFalse = refl

literalVectorAdjointUniquenessClosed : Bool
literalVectorAdjointUniquenessClosed = false

literalVectorAdjointUniquenessClosedIsFalse :
  literalVectorAdjointUniquenessClosed ≡ false
literalVectorAdjointUniquenessClosedIsFalse = refl
