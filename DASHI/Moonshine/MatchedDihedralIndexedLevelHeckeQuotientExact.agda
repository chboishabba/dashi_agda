module DASHI.Moonshine.MatchedDihedralIndexedLevelHeckeQuotientExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- DASHI CONTRIBUTION
--
-- Lift the matched-dihedral weight quotient to the repository's unbiased
-- natural-level Hecke API without identifying the level with the angular
-- momentum index.  The dependent families are inhabited precisely through
-- constructors at levels
--
--   p = 2*j+1 = so3Dimension j.
--
-- Thus non-Ogg odd controls such as p=9 and p=15 live in exactly the same
-- operator family as Ogg levels.  The p=2 spinor remains outside this SO(3)
-- family, as required by the existing SU(2)/SO(3) boundary.
--
-- Once a level-dependent fine correspondence is supplied and is congruent
-- under m <-> -m, IndexedLevelHeckeQuotientDescentExact canonically produces
-- the matched-sector correspondence and the observable intertwiner at every
-- represented odd level.  This removes the level-indexing and quotient
-- bookkeeping from the remaining Brandt/Hecke theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Ontology.Hecke.LevelCorrespondenceRepresentation as Level
import Ontology.Hecke.IndexedLevelCorrespondenceRepresentation as Indexed
import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as PrimeDescent
import DASHI.Moonshine.IndexedLevelHeckeQuotientDescentExact as IndexedDescent
import DASHI.Moonshine.MatchedDihedralWeightHeckeQuotientExact as Weight

------------------------------------------------------------------------
-- Natural-level dependent fine/coarse families.
------------------------------------------------------------------------

data SO3WeightAtLevel : Nat → Set where
  weightAtSO3Level :
    (j : Nat) →
    Weight.SO3WeightLabel j →
    SO3WeightAtLevel (Spin.so3Dimension j)

data MatchedSectorAtLevel : Nat → Set where
  sectorAtSO3Level :
    (j : Nat) →
    Matched.MatchedDihedralSector j →
    MatchedSectorAtLevel (Spin.so3Dimension j)

levelWeightSector :
  ∀ {level} →
  SO3WeightAtLevel level →
  MatchedSectorAtLevel level
levelWeightSector (weightAtSO3Level j weight) =
  sectorAtSO3Level j (Weight.weightSector weight)

levelSectorRepresentative :
  ∀ {level} →
  MatchedSectorAtLevel level →
  SO3WeightAtLevel level
levelSectorRepresentative (sectorAtSO3Level j sector) =
  weightAtSO3Level j (Weight.sectorRepresentative sector)

levelSection :
  ∀ {level} →
  (sector : MatchedSectorAtLevel level) →
  levelWeightSector (levelSectorRepresentative sector) ≡ sector
levelSection (sectorAtSO3Level j Matched.selectedSinglet) = refl
levelSection (sectorAtSO3Level j (Matched.pairedDoublet pair)) = refl

------------------------------------------------------------------------
-- Exact quotient at every natural level.  At levels with no SO(3) constructor
-- the carriers are simply empty; no artificial default sector is inserted.
------------------------------------------------------------------------

levelWeightEquivalence :
  (level : Nat) →
  Quotient.EquivalenceOn (SO3WeightAtLevel level)
levelWeightEquivalence level =
  record
    { _≈_ = λ left right → levelWeightSector left ≡ levelWeightSector right
    ; refl = λ _ → refl
    ; sym = λ equality → sym equality
    ; trans = λ leftMiddle middleRight → trans leftMiddle middleRight
    }

matchedLevelQuotient :
  (level : Nat) →
  Quotient.QuotientInterfaceOn
    (SO3WeightAtLevel level)
    (MatchedSectorAtLevel level)
matchedLevelQuotient level =
  record
    { equiv = levelWeightEquivalence level
    ; proj = levelWeightSector
    ; respect-proj = λ equality → equality
    ; representative = levelSectorRepresentative
    ; section = levelSection
    }

matchedLevelExactPresentation :
  (level : Nat) →
  PrimeDescent.ExactQuotientPresentation (matchedLevelQuotient level)
matchedLevelExactPresentation level =
  record
    { projectionComplete = λ equality → equality
    }

------------------------------------------------------------------------
-- Concrete odd-level witnesses, including a non-Ogg control level p=9.
------------------------------------------------------------------------

p3CentralWeight : SO3WeightAtLevel 3
p3CentralWeight = weightAtSO3Level 1 Weight.centralWeight

p9CentralWeight : SO3WeightAtLevel 9
p9CentralWeight = weightAtSO3Level 4 Weight.centralWeight

p9FirstPair : Matched.PairIndex 4
p9FirstPair = Matched.firstPair {j = 3}

p9PositiveWeight : SO3WeightAtLevel 9
p9PositiveWeight =
  weightAtSO3Level 4 (Weight.positiveWeight p9FirstPair)

p9NegativeWeight : SO3WeightAtLevel 9
p9NegativeWeight =
  weightAtSO3Level 4 (Weight.negativeWeight p9FirstPair)

p9OppositeWeightsSameSector :
  levelWeightSector p9PositiveWeight ≡ levelWeightSector p9NegativeWeight
p9OppositeWeightsSameSector = refl

------------------------------------------------------------------------
-- Level-dependent fine correspondence congruence.
------------------------------------------------------------------------

record MatchedIndexedCorrespondenceCongruence
    (fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn SO3WeightAtLevel) : Set₁ where
  field
    projectedCorrespondenceCongruentAt :
      (level : Nat) →
      ∀ {left right : SO3WeightAtLevel level} →
      levelWeightSector left ≡ levelWeightSector right →
      Level.map15 levelWeightSector
        (Indexed.correspondence fineHecke level left)
      ≡
      Level.map15 levelWeightSector
        (Indexed.correspondence fineHecke level right)

open MatchedIndexedCorrespondenceCongruence public

matchedIndexedDescent :
  {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn SO3WeightAtLevel} →
  MatchedIndexedCorrespondenceCongruence fineHecke →
  IndexedDescent.IndexedQuotientStableCorrespondence
    SO3WeightAtLevel MatchedSectorAtLevel fineHecke
matchedIndexedDescent congruence =
  record
    { quotientAt = matchedLevelQuotient
    ; exactAt = matchedLevelExactPresentation
    ; correspondenceRespectsEquivAt =
        projectedCorrespondenceCongruentAt congruence
    }

matchedIndexedSectorHecke :
  {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn SO3WeightAtLevel} →
  MatchedIndexedCorrespondenceCongruence fineHecke →
  Indexed.IndexedLevelCorrespondenceHeckeOn MatchedSectorAtLevel
matchedIndexedSectorHecke congruence =
  IndexedDescent.inducedIndexedHecke (matchedIndexedDescent congruence)

matchedIndexedObservableHeckeCommutes :
  {fineHecke : Indexed.IndexedLevelCorrespondenceHeckeOn SO3WeightAtLevel} →
  (congruence : MatchedIndexedCorrespondenceCongruence fineHecke) →
  (level : Nat) →
  (observable : MatchedSectorAtLevel level → Nat) →
  (weight : SO3WeightAtLevel level) →
  Indexed.operator fineHecke level
    (λ state → observable (levelWeightSector state)) weight
  ≡
  Indexed.operator (matchedIndexedSectorHecke congruence)
    level observable (levelWeightSector weight)
matchedIndexedObservableHeckeCommutes congruence level observable weight =
  IndexedDescent.indexedProjectedObservableHeckeCommutes
    (matchedIndexedDescent congruence) level observable weight

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record MatchedDihedralIndexedLevelBoundary : Set where
  field
    oddSO3LevelsUseDependentCarrier : Bool
    oddSO3LevelsUseDependentCarrierIsTrue :
      oddSO3LevelsUseDependentCarrier ≡ true

    nonOggLevelNineRepresented : Bool
    nonOggLevelNineRepresentedIsTrue :
      nonOggLevelNineRepresented ≡ true

    levelwiseWeightPairQuotientConstructed : Bool
    levelwiseWeightPairQuotientConstructedIsTrue :
      levelwiseWeightPairQuotientConstructed ≡ true

    fineBrandtCorrespondenceConstructedHere : Bool
    fineBrandtCorrespondenceConstructedHereIsFalse :
      fineBrandtCorrespondenceConstructedHere ≡ false

    arithmeticHeckeIdentificationConstructedHere : Bool
    arithmeticHeckeIdentificationConstructedHereIsFalse :
      arithmeticHeckeIdentificationConstructedHere ≡ false

canonicalMatchedDihedralIndexedLevelBoundary :
  MatchedDihedralIndexedLevelBoundary
canonicalMatchedDihedralIndexedLevelBoundary =
  record
    { oddSO3LevelsUseDependentCarrier = true
    ; oddSO3LevelsUseDependentCarrierIsTrue = refl
    ; nonOggLevelNineRepresented = true
    ; nonOggLevelNineRepresentedIsTrue = refl
    ; levelwiseWeightPairQuotientConstructed = true
    ; levelwiseWeightPairQuotientConstructedIsTrue = refl
    ; fineBrandtCorrespondenceConstructedHere = false
    ; fineBrandtCorrespondenceConstructedHereIsFalse = refl
    ; arithmeticHeckeIdentificationConstructedHere = false
    ; arithmeticHeckeIdentificationConstructedHereIsFalse = refl
    }
