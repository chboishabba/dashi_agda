module DASHI.Foundations.MatchedDihedralSO3RestrictionExact where

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
-- DASHI CONTRIBUTION
--
-- Construct a natural candidate-indexed finite restriction family rather than
-- choosing one fixed point group for every angular momentum:
--
--   V_j  downarrow  D_(2j+1).
--
-- Pair the SO(3) weights m and -m.  The m=0 line supplies one one-dimensional
-- parity sector, while every pair +/-m, 1<=m<=j, supplies one two-dimensional
-- dihedral sector.  Thus the occurring restriction is multiplicity-free:
--
--   V_j | D_(2j+1) = epsilon_j + rho_1 + ... + rho_j,
--
-- with dimensions
--
--   2j+1 = 1 + 2 + ... + 2.
--
-- For j=4 this is the literal "five irreps of nine" reduction
--
--   9 = 1 + 2 + 2 + 2 + 2.
--
-- The construction is Ogg-blind and works for every j in the scan.  Therefore
-- matched-dihedral multiplicity-freeness is a geometric producer, not an Ogg
-- selector by itself.
--
-- epsilon_j records the one-dimensional sector actually occurring.  For the
-- full odd dihedral group it is the trivial or reflection-sign character
-- according to parity conventions; this file does not identify the two labels
-- because the dimension/branching theorem needs only the selected line.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using (map; length)

import DASHI.Foundations.FiniteRepresentationRestrictionCore as Core
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.CandidateIndexedFiniteRestrictionFamilyExact as Candidate

------------------------------------------------------------------------
-- Finite pair index, equivalent to Fin j but kept local and structurally
-- recursive so the all-sectors list and its dimension proof normalize cleanly.
------------------------------------------------------------------------

data PairIndex : Nat → Set where
  firstPair : {j : Nat} → PairIndex (suc j)
  nextPair : {j : Nat} → PairIndex j → PairIndex (suc j)

allPairIndices : (j : Nat) → List (PairIndex j)
allPairIndices 0 = []
allPairIndices (suc j) = firstPair ∷ map nextPair (allPairIndices j)

pairCount : ∀ {j} → List (PairIndex j) → Nat
pairCount [] = 0
pairCount (_ ∷ rest) = suc (pairCount rest)

mapNextPairPreservesCount :
  ∀ {j} →
  (pairs : List (PairIndex j)) →
  pairCount (map nextPair pairs) ≡ pairCount pairs
mapNextPairPreservesCount [] = refl
mapNextPairPreservesCount (_ ∷ rest)
  rewrite mapNextPairPreservesCount rest = refl

allPairCountIsJ :
  (j : Nat) →
  pairCount (allPairIndices j) ≡ j
allPairCountIsJ 0 = refl
allPairCountIsJ (suc j)
  rewrite mapNextPairPreservesCount (allPairIndices j)
        | allPairCountIsJ j = refl

pairCountIsLength :
  ∀ {j} →
  (pairs : List (PairIndex j)) →
  pairCount pairs ≡ length pairs
pairCountIsLength [] = refl
pairCountIsLength (_ ∷ rest)
  rewrite pairCountIsLength rest = refl

allPairLengthIsJ :
  (j : Nat) →
  length (allPairIndices j) ≡ j
allPairLengthIsJ j =
  trans
    (sym (pairCountIsLength (allPairIndices j)))
    (allPairCountIsJ j)

------------------------------------------------------------------------
-- The occurring matched-dihedral sectors.
------------------------------------------------------------------------

data MatchedDihedralSector (j : Nat) : Set where
  selectedSinglet : MatchedDihedralSector j
  pairedDoublet : PairIndex j → MatchedDihedralSector j

sectorDimension :
  ∀ {j} → MatchedDihedralSector j → Nat
sectorDimension selectedSinglet = 1
sectorDimension (pairedDoublet _) = 2

sectorMultiplicity :
  ∀ {j} → MatchedDihedralSector j → Nat
sectorMultiplicity _ = 1

allSectors : (j : Nat) → List (MatchedDihedralSector j)
allSectors j = selectedSinglet ∷ map pairedDoublet (allPairIndices j)

occurringSectorCount : Nat → Nat
occurringSectorCount j = length (allSectors j)

mapPreservesLength :
  ∀ {A B : Set} →
  (f : A → B) →
  (values : List A) →
  length (map f values) ≡ length values
mapPreservesLength f [] = refl
mapPreservesLength f (_ ∷ rest)
  rewrite mapPreservesLength f rest = refl

occurringSectorCountIsSuccJ :
  (j : Nat) →
  occurringSectorCount j ≡ suc j
occurringSectorCountIsSuccJ j
  rewrite mapPreservesLength pairedDoublet (allPairIndices j)
        | allPairLengthIsJ j = refl

------------------------------------------------------------------------
-- Exact dimension conservation.
------------------------------------------------------------------------

doubletMass : ∀ {j} → List (PairIndex j) → Nat
doubletMass [] = 0
doubletMass (_ ∷ rest) = 2 + doubletMass rest

mapNextPairPreservesMass :
  ∀ {j} →
  (pairs : List (PairIndex j)) →
  doubletMass (map nextPair pairs) ≡ doubletMass pairs
mapNextPairPreservesMass [] = refl
mapNextPairPreservesMass (_ ∷ rest)
  rewrite mapNextPairPreservesMass rest = refl

allPairMassIsTwiceJ :
  (j : Nat) →
  doubletMass (allPairIndices j) ≡ Spin.twice j
allPairMassIsTwiceJ 0 = refl
allPairMassIsTwiceJ (suc j)
  rewrite mapNextPairPreservesMass (allPairIndices j)
        | allPairMassIsTwiceJ j = refl

coreDoubletMass :
  ∀ {j} →
  (pairs : List (PairIndex j)) →
  Core.sumWeighted
    (map pairedDoublet pairs)
    sectorDimension
    sectorMultiplicity
  ≡ doubletMass pairs
coreDoubletMass [] = refl
coreDoubletMass (_ ∷ rest)
  rewrite coreDoubletMass rest = refl

matchedDimensionConserved :
  (j : Nat) →
  Core.sumWeighted
    (allSectors j)
    sectorDimension
    sectorMultiplicity
  ≡ Spin.so3Dimension j
matchedDimensionConserved j
  rewrite coreDoubletMass (allPairIndices j)
        | allPairMassIsTwiceJ j = refl

------------------------------------------------------------------------
-- Canonical finite-restriction family.
------------------------------------------------------------------------

matchedTargetFamilyNat : Nat → Core.FiniteIrrepFamily
matchedTargetFamilyNat j =
  Core.finite-irrep-family
    (MatchedDihedralSector j)
    (allSectors j)
    sectorDimension
    "occurring irreducible sectors of matched rotational dihedral D_(2j+1)"

matchedBranchingAt :
  (j : Spin.AngularMomentum0To35) →
  Core.BranchingSpectrum
    (Spin.continuousSO3Irrep j)
    (matchedTargetFamilyNat (Spin.jNat j))
matchedBranchingAt j =
  Core.branching-spectrum
    sectorMultiplicity
    (matchedDimensionConserved (Spin.jNat j))
    "multiplicity-free selected singlet plus all +/-m dihedral doublets"

data MatchedRotationFixedProbe : Set where
  matchedAxialCyclic : MatchedRotationFixedProbe

matchedFixedSpaces :
  Spin.AngularMomentum0To35 → Core.FixedSpaceSpectrum
matchedFixedSpaces j =
  Core.fixed-space-spectrum
    MatchedRotationFixedProbe
    (λ _ → 1)
    (λ _ → "C_(2j+1) axial-rotation invariant line m=0")
    "matched cyclic rotation fixes exactly the central m=0 weight line"

matchedDihedralCandidateFamily :
  Candidate.CandidateIndexedFiniteRestrictionFamily
matchedDihedralCandidateFamily =
  record
    { targetFamily =
        λ j → matchedTargetFamilyNat (Spin.jNat j)
    ; branchingAt = matchedBranchingAt
    ; fixedSpacesAt = matchedFixedSpaces
    ; restrictionReceiptAt =
        λ _ → "SO(3) carrier restricted to matched D_(2j+1) occurring sectors"
    ; familyLabel =
        "candidate-indexed matched odd-dihedral restriction family"
    ; knownOggListUsedToChooseTarget = false
    ; knownOggListUsedToChooseTargetIsFalse = refl
    }

------------------------------------------------------------------------
-- Five irreps of nine: j=4 gives one singlet plus four doublets.
------------------------------------------------------------------------

j4SectorCountIsFive : occurringSectorCount 4 ≡ 5
j4SectorCountIsFive = refl

j4SectorCountFromGenericTheorem : occurringSectorCount 4 ≡ suc 4
j4SectorCountFromGenericTheorem = occurringSectorCountIsSuccJ 4

j4MatchedDimensionIsNine :
  Core.sumWeighted
    (allSectors 4)
    sectorDimension
    sectorMultiplicity
  ≡ 9
j4MatchedDimensionIsNine = refl

j4RestrictionMatchesSO3Nine :
  Core.sumWeighted
    (allSectors 4)
    sectorDimension
    sectorMultiplicity
  ≡ Spin.jDimension Spin.j4
j4RestrictionMatchesSO3Nine = refl

------------------------------------------------------------------------
-- Universal multiplicity-free boundary.
------------------------------------------------------------------------

matchedMultiplicityIsAlwaysOne :
  (j : Nat) →
  (sector : MatchedDihedralSector j) →
  sectorMultiplicity sector ≡ 1
matchedMultiplicityIsAlwaysOne j sector = refl

record MatchedDihedralRestrictionBoundary : Set where
  field
    candidateIndexedFamilyConstructed : Bool
    candidateIndexedFamilyConstructedIsTrue :
      candidateIndexedFamilyConstructed ≡ true
    fiveIrrepsOfNineConstructed : Bool
    fiveIrrepsOfNineConstructedIsTrue : fiveIrrepsOfNineConstructed ≡ true
    sectorCountIsJPlusOne : Bool
    sectorCountIsJPlusOneIsTrue : sectorCountIsJPlusOne ≡ true
    multiplicityFreeForEveryCandidate : Bool
    multiplicityFreeForEveryCandidateIsTrue :
      multiplicityFreeForEveryCandidate ≡ true
    multiplicityFreeAloneSelectsOgg : Bool
    multiplicityFreeAloneSelectsOggIsFalse :
      multiplicityFreeAloneSelectsOgg ≡ false
    knownOggListUsedUpstream : Bool
    knownOggListUsedUpstreamIsFalse : knownOggListUsedUpstream ≡ false

canonicalMatchedDihedralRestrictionBoundary :
  MatchedDihedralRestrictionBoundary
canonicalMatchedDihedralRestrictionBoundary =
  record
    { candidateIndexedFamilyConstructed = true
    ; candidateIndexedFamilyConstructedIsTrue = refl
    ; fiveIrrepsOfNineConstructed = true
    ; fiveIrrepsOfNineConstructedIsTrue = refl
    ; sectorCountIsJPlusOne = true
    ; sectorCountIsJPlusOneIsTrue = refl
    ; multiplicityFreeForEveryCandidate = true
    ; multiplicityFreeForEveryCandidateIsTrue = refl
    ; multiplicityFreeAloneSelectsOgg = false
    ; multiplicityFreeAloneSelectsOggIsFalse = refl
    ; knownOggListUsedUpstream = false
    ; knownOggListUsedUpstreamIsFalse = refl
    }
