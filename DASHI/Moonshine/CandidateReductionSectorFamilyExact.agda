module DASHI.Moonshine.CandidateReductionSectorFamilyExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- William Fulton and Joe Harris,
-- "Representation Theory: A First Course", Graduate Texts in Mathematics 129,
-- Springer.
-- DOI: 10.1007/978-1-4612-0979-9.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Graduate Texts in Mathematics 42,
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- DASHI CONTRIBUTION
--
-- Construct the actual level-dependent *target carrier* required by the new
-- indexed Hecke quotient theorem.
--
-- * level 2 keeps the genuine SU(2) doublet boundary as one irreducible sector;
-- * every scanned odd level 2*j+1 uses the already-constructed occurring
--   sectors of V_j downarrow D_(2j+1): one selected singlet plus j doublets.
--
-- The carrier is indexed by the numerical level itself, so Ogg and non-Ogg odd
-- controls inhabit the same type family.  No external exceptional predicate is
-- consulted.  The missing theorem is now specifically a fine representation
-- state/correspondence plus a quotient projection into this family.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using (map; length)

import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.CandidateLevelRepresentationHeckeSquareExact as Candidate

------------------------------------------------------------------------
-- Level-indexed occurring sector carrier.
------------------------------------------------------------------------

data CandidateReductionSector (level : Nat) : Set where
  spinorDoublet :
    level ≡ 2 →
    CandidateReductionSector level

  spatialSector :
    (j : Spin.AngularMomentum0To35) →
    level ≡ Spin.jDimension j →
    Matched.MatchedDihedralSector (Spin.jNat j) →
    CandidateReductionSector level

candidateReductionSectorDimension :
  ∀ {level} → CandidateReductionSector level → Nat
candidateReductionSectorDimension (spinorDoublet equality) = 2
candidateReductionSectorDimension (spatialSector j equality sector) =
  Matched.sectorDimension sector

------------------------------------------------------------------------
-- Every unbiased candidate level has an explicit carrier.
------------------------------------------------------------------------

carrierAtCandidate : Candidate.CandidateLevel → Set
carrierAtCandidate candidate =
  CandidateReductionSector (Candidate.candidateLevelNat candidate)

canonicalCandidateSector :
  (candidate : Candidate.CandidateLevel) → carrierAtCandidate candidate
canonicalCandidateSector Candidate.spinorLevel2 = spinorDoublet refl
canonicalCandidateSector (Candidate.spatialLevel j) =
  spatialSector j refl Matched.selectedSinglet

spinorSectorDimensionIsTwo :
  candidateReductionSectorDimension
    (canonicalCandidateSector Candidate.spinorLevel2)
  ≡ 2
spinorSectorDimensionIsTwo = refl

------------------------------------------------------------------------
-- The literal five-irrep-of-nine carrier is retained at numerical level 9.
------------------------------------------------------------------------

liftJ4Sector :
  Matched.MatchedDihedralSector 4 → CandidateReductionSector 9
liftJ4Sector sector = spatialSector Spin.j4 refl sector

j4FiveSectorFamily : List (CandidateReductionSector 9)
j4FiveSectorFamily = map liftJ4Sector (Matched.allSectors 4)

j4FiveSectorFamilyHasFiveEntries : length j4FiveSectorFamily ≡ 5
j4FiveSectorFamilyHasFiveEntries = refl

------------------------------------------------------------------------
-- Representative non-Ogg controls inhabit the same family without any special
-- branch or selector premise.
------------------------------------------------------------------------

level15CanonicalSector : CandidateReductionSector 15
level15CanonicalSector = spatialSector Spin.j7 refl Matched.selectedSinglet

level21CanonicalSector : CandidateReductionSector 21
level21CanonicalSector = spatialSector Spin.j10 refl Matched.selectedSinglet

level27CanonicalSector : CandidateReductionSector 27
level27CanonicalSector = spatialSector Spin.j13 refl Matched.selectedSinglet

level43CanonicalSector : CandidateReductionSector 43
level43CanonicalSector = spatialSector Spin.j21 refl Matched.selectedSinglet

level53CanonicalSector : CandidateReductionSector 53
level53CanonicalSector = spatialSector Spin.j26 refl Matched.selectedSinglet

level67CanonicalSector : CandidateReductionSector 67
level67CanonicalSector = spatialSector Spin.j33 refl Matched.selectedSinglet

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record CandidateReductionSectorFamilyBoundary : Set where
  field
    levelDependentReductionCarrierConstructed : Bool
    levelDependentReductionCarrierConstructedIsTrue :
      levelDependentReductionCarrierConstructed ≡ true

    p2SpinorBoundaryRetained : Bool
    p2SpinorBoundaryRetainedIsTrue : p2SpinorBoundaryRetained ≡ true

    matchedDihedralOddSectorCarrierReused : Bool
    matchedDihedralOddSectorCarrierReusedIsTrue :
      matchedDihedralOddSectorCarrierReused ≡ true

    nonOggControlsInSameCarrierFamily : Bool
    nonOggControlsInSameCarrierFamilyIsTrue :
      nonOggControlsInSameCarrierFamily ≡ true

    fineRepresentationStateQuotientConstructedHere : Bool
    fineRepresentationStateQuotientConstructedHereIsFalse :
      fineRepresentationStateQuotientConstructedHere ≡ false

canonicalCandidateReductionSectorFamilyBoundary :
  CandidateReductionSectorFamilyBoundary
canonicalCandidateReductionSectorFamilyBoundary =
  record
    { levelDependentReductionCarrierConstructed = true
    ; levelDependentReductionCarrierConstructedIsTrue = refl
    ; p2SpinorBoundaryRetained = true
    ; p2SpinorBoundaryRetainedIsTrue = refl
    ; matchedDihedralOddSectorCarrierReused = true
    ; matchedDihedralOddSectorCarrierReusedIsTrue = refl
    ; nonOggControlsInSameCarrierFamily = true
    ; nonOggControlsInSameCarrierFamilyIsTrue = refl
    ; fineRepresentationStateQuotientConstructedHere = false
    ; fineRepresentationStateQuotientConstructedHereIsFalse = refl
    }
