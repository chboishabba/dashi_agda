module DASHI.Moonshine.MatchedDihedralWeightHeckeQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Nicholas M. Katz and Barry Mazur,
-- "Arithmetic Moduli of Elliptic Curves", Princeton University Press, 1985.
-- DOI: 10.1515/9781400881710.
--
-- DASHI CONTRIBUTION
--
-- Make the matched-dihedral restriction into an actual quotient carrier rather
-- than only a branching-count theorem.  The standard SO(3) weight labels are
-- represented finitely as
--
--   0, +1, -1, ..., +j, -j,
--
-- and the quotient identifies +m with -m while retaining the central m=0
-- line.  The quotient classes are definitionally the already-constructed
-- matched D_(2j+1) sectors
--
--   epsilon_j, rho_1, ..., rho_j.
--
-- The repository's generic Hecke correspondence quotient theorem then says:
-- any fine correspondence on these weight labels whose projected 15-way list
-- is invariant under the +/- pairing has a canonical induced correspondence
-- on the matched-dihedral sectors, and every Nat-valued sector observable
-- satisfies the exact Hecke commuting square.
--
-- This is a domain-specific representation reduction, but it still does NOT
-- construct the geometric/Brandt/Hecke correspondence on SO(3) weights.  The
-- remaining theorem is therefore a correspondence producer plus its +/-
-- congruence, followed by identification of the induced sector correspondence
-- with the arithmetic one.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import MonsterOntos as Monster
import Ontology.Hecke.CorrespondenceRepresentation as Hecke
import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Descent

------------------------------------------------------------------------
-- Finite SO(3) weight-label carrier at angular momentum j.
------------------------------------------------------------------------

data SO3WeightLabel (j : Nat) : Set where
  centralWeight : SO3WeightLabel j
  positiveWeight : Matched.PairIndex j → SO3WeightLabel j
  negativeWeight : Matched.PairIndex j → SO3WeightLabel j

weightSector :
  ∀ {j} →
  SO3WeightLabel j →
  Matched.MatchedDihedralSector j
weightSector centralWeight = Matched.selectedSinglet
weightSector (positiveWeight pair) = Matched.pairedDoublet pair
weightSector (negativeWeight pair) = Matched.pairedDoublet pair

sectorRepresentative :
  ∀ {j} →
  Matched.MatchedDihedralSector j →
  SO3WeightLabel j
sectorRepresentative Matched.selectedSinglet = centralWeight
sectorRepresentative (Matched.pairedDoublet pair) = positiveWeight pair

weightSectorSection :
  ∀ {j} →
  (sector : Matched.MatchedDihedralSector j) →
  weightSector (sectorRepresentative sector) ≡ sector
weightSectorSection Matched.selectedSinglet = refl
weightSectorSection (Matched.pairedDoublet pair) = refl

------------------------------------------------------------------------
-- Exact quotient by the +/- weight pairing.
------------------------------------------------------------------------

weightPairEquivalence :
  (j : Nat) →
  Quotient.EquivalenceOn (SO3WeightLabel j)
weightPairEquivalence j =
  record
    { _≈_ = λ left right → weightSector left ≡ weightSector right
    ; refl = λ _ → refl
    ; sym = λ equality → sym equality
    ; trans = λ leftMiddle middleRight → trans leftMiddle middleRight
    }

matchedWeightQuotient :
  (j : Nat) →
  Quotient.QuotientInterfaceOn
    (SO3WeightLabel j)
    (Matched.MatchedDihedralSector j)
matchedWeightQuotient j =
  record
    { equiv = weightPairEquivalence j
    ; proj = weightSector
    ; respect-proj = λ equality → equality
    ; representative = sectorRepresentative
    ; section = weightSectorSection
    }

matchedWeightExactPresentation :
  (j : Nat) →
  Descent.ExactQuotientPresentation (matchedWeightQuotient j)
matchedWeightExactPresentation j =
  record
    { projectionComplete = λ equality → equality
    }

------------------------------------------------------------------------
-- The representation-theoretic +/- identification is literal.
------------------------------------------------------------------------

oppositeWeightsSameSector :
  ∀ {j} →
  (pair : Matched.PairIndex j) →
  weightSector (positiveWeight pair)
  ≡ weightSector (negativeWeight pair)
oppositeWeightsSameSector pair = refl

positiveRepresentativeOfDoublet :
  ∀ {j} →
  (pair : Matched.PairIndex j) →
  sectorRepresentative (Matched.pairedDoublet pair)
  ≡ positiveWeight pair
positiveRepresentativeOfDoublet pair = refl

centralRepresentativeOfSinglet :
  ∀ {j} →
  sectorRepresentative {j} Matched.selectedSinglet ≡ centralWeight
centralRepresentativeOfSinglet = refl

------------------------------------------------------------------------
-- Fine correspondence congruence is now the only quotient condition.
------------------------------------------------------------------------

record MatchedWeightCorrespondenceCongruence
    (j : Nat)
    (fineHecke : Hecke.PrimeCorrespondenceHeckeOn (SO3WeightLabel j)) : Set₁ where
  field
    projectedCorrespondenceCongruent :
      (prime : Monster.SSP) →
      ∀ {left right : SO3WeightLabel j} →
      weightSector left ≡ weightSector right →
      Hecke.map15 weightSector
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime left)
      ≡
      Hecke.map15 weightSector
        (Hecke.PrimeCorrespondenceHeckeOn.correspondence fineHecke prime right)

open MatchedWeightCorrespondenceCongruence public

matchedWeightCorrespondenceDescent :
  ∀ {j}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn (SO3WeightLabel j)} →
  MatchedWeightCorrespondenceCongruence j fineHecke →
  Descent.QuotientStablePrimeCorrespondence
    (matchedWeightQuotient j) fineHecke
matchedWeightCorrespondenceDescent {j} congruence =
  record
    { exactPresentation = matchedWeightExactPresentation j
    ; correspondenceRespectsEquiv =
        projectedCorrespondenceCongruent congruence
    }

matchedSectorHecke :
  ∀ {j}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn (SO3WeightLabel j)} →
  MatchedWeightCorrespondenceCongruence j fineHecke →
  Hecke.PrimeCorrespondenceHeckeOn (Matched.MatchedDihedralSector j)
matchedSectorHecke congruence =
  Descent.inducedHecke (matchedWeightCorrespondenceDescent congruence)

------------------------------------------------------------------------
-- Exact observable intertwining on the actual matched restriction quotient.
------------------------------------------------------------------------

matchedSectorObservableHeckeCommutes :
  ∀ {j}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn (SO3WeightLabel j)}
    (congruence : MatchedWeightCorrespondenceCongruence j fineHecke)
    (observable : Matched.MatchedDihedralSector j → Nat)
    (prime : Monster.SSP)
    (weight : SO3WeightLabel j) →
  Hecke.PrimeCorrespondenceHeckeOn.operator fineHecke
    (λ state → observable (weightSector state)) prime weight
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.operator
    (matchedSectorHecke congruence)
    observable prime (weightSector weight)
matchedSectorObservableHeckeCommutes congruence observable prime weight =
  Descent.projectedObservableHeckeCommutes
    (matchedWeightCorrespondenceDescent congruence)
    observable prime weight

------------------------------------------------------------------------
-- In particular, +/- paired weights have identical projected Hecke readout for
-- every quotient observable once fine correspondence congruence is supplied.
------------------------------------------------------------------------

oppositeWeightObservableHeckeEqual :
  ∀ {j}
    {fineHecke : Hecke.PrimeCorrespondenceHeckeOn (SO3WeightLabel j)}
    (congruence : MatchedWeightCorrespondenceCongruence j fineHecke)
    (observable : Matched.MatchedDihedralSector j → Nat)
    (prime : Monster.SSP)
    (pair : Matched.PairIndex j) →
  Hecke.PrimeCorrespondenceHeckeOn.operator fineHecke
    (λ state → observable (weightSector state))
    prime (positiveWeight pair)
  ≡
  Hecke.PrimeCorrespondenceHeckeOn.operator fineHecke
    (λ state → observable (weightSector state))
    prime (negativeWeight pair)
oppositeWeightObservableHeckeEqual
  {fineHecke = fineHecke} congruence observable prime pair =
  trans
    (matchedSectorObservableHeckeCommutes
      congruence observable prime (positiveWeight pair))
    (sym
      (matchedSectorObservableHeckeCommutes
        congruence observable prime (negativeWeight pair)))

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record MatchedDihedralWeightHeckeBoundary : Set where
  field
    standardWeightPairQuotientConstructed : Bool
    standardWeightPairQuotientConstructedIsTrue :
      standardWeightPairQuotientConstructed ≡ true

    quotientClassesAreExistingMatchedDihedralSectors : Bool
    quotientClassesAreExistingMatchedDihedralSectorsIsTrue :
      quotientClassesAreExistingMatchedDihedralSectors ≡ true

    heckeDescentDerivedFromPairCongruence : Bool
    heckeDescentDerivedFromPairCongruenceIsTrue :
      heckeDescentDerivedFromPairCongruence ≡ true

    fineSO3WeightCorrespondenceConstructedHere : Bool
    fineSO3WeightCorrespondenceConstructedHereIsFalse :
      fineSO3WeightCorrespondenceConstructedHere ≡ false

    inducedSectorHeckeIdentifiedWithArithmeticHeckeHere : Bool
    inducedSectorHeckeIdentifiedWithArithmeticHeckeHereIsFalse :
      inducedSectorHeckeIdentifiedWithArithmeticHeckeHere ≡ false

canonicalMatchedDihedralWeightHeckeBoundary :
  MatchedDihedralWeightHeckeBoundary
canonicalMatchedDihedralWeightHeckeBoundary =
  record
    { standardWeightPairQuotientConstructed = true
    ; standardWeightPairQuotientConstructedIsTrue = refl
    ; quotientClassesAreExistingMatchedDihedralSectors = true
    ; quotientClassesAreExistingMatchedDihedralSectorsIsTrue = refl
    ; heckeDescentDerivedFromPairCongruence = true
    ; heckeDescentDerivedFromPairCongruenceIsTrue = refl
    ; fineSO3WeightCorrespondenceConstructedHere = false
    ; fineSO3WeightCorrespondenceConstructedHereIsFalse = refl
    ; inducedSectorHeckeIdentifiedWithArithmeticHeckeHere = false
    ; inducedSectorHeckeIdentifiedWithArithmeticHeckeHereIsFalse = refl
    }
