module DASHI.Moonshine.SO3WeightMatchedDihedralQuotientExact where

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
-- Construct the explicit finite state quotient that was still missing between
-- the SO(3) weight picture and the already-built matched-dihedral irreducible
-- sector family.
--
-- For integer spin j the fine carrier is
--
--   m = 0, +/-1, ..., +/-j.
--
-- The quotient sends m=0 to the selected one-dimensional sector and identifies
-- the pair +/-m with the existing two-dimensional D_(2j+1) sector rho_m.
-- Thus the fine 2j+1 weight states quotient onto j+1 occurring irreducible
-- sectors.  At j=4 this is literally
--
--   9 fine weight states -> 5 sectors = 1 + 2 + 2 + 2 + 2.
--
-- Level 2 is kept separate as two SU(2) spinor basis states mapping to the one
-- doublet irrep sector.  This file constructs the carrier and exact quotient;
-- it does not yet construct a level-indexed 15-way Hecke/Brandt correspondence
-- on the fine weight states.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List.Base using (List; []; _∷_; length)

import Ontology.Hecke.QuotientRepresentation as Quotient
import DASHI.Moonshine.HeckeCorrespondenceQuotientDescentExact as Descent
import DASHI.Foundations.SU2SO3IrrepDimensionExact as Spin
import DASHI.Foundations.MatchedDihedralSO3RestrictionExact as Matched
import DASHI.Moonshine.CandidateReductionSectorFamilyExact as Sector

------------------------------------------------------------------------
-- Integer-spin SO(3) weight-state carrier.
------------------------------------------------------------------------

data WeightSign : Set where
  positiveWeight negativeWeight : WeightSign

data SO3WeightState (j : Nat) : Set where
  centralWeight : SO3WeightState j
  pairedWeight : Matched.PairIndex j → WeightSign → SO3WeightState j

weightToMatchedSector :
  ∀ {j} → SO3WeightState j → Matched.MatchedDihedralSector j
weightToMatchedSector centralWeight = Matched.selectedSinglet
weightToMatchedSector (pairedWeight index sign) = Matched.pairedDoublet index

matchedSectorRepresentative :
  ∀ {j} → Matched.MatchedDihedralSector j → SO3WeightState j
matchedSectorRepresentative Matched.selectedSinglet = centralWeight
matchedSectorRepresentative (Matched.pairedDoublet index) =
  pairedWeight index positiveWeight

matchedSectorSection :
  ∀ {j}
    (sector : Matched.MatchedDihedralSector j) →
  weightToMatchedSector (matchedSectorRepresentative sector) ≡ sector
matchedSectorSection Matched.selectedSinglet = refl
matchedSectorSection (Matched.pairedDoublet index) = refl

matchedWeightEquivalence :
  (j : Nat) → Quotient.EquivalenceOn (SO3WeightState j)
matchedWeightEquivalence j =
  record
    { _≈_ =
        λ left right → weightToMatchedSector left ≡ weightToMatchedSector right
    ; refl = λ state → refl
    ; sym = sym
    ; trans = trans
    }

matchedWeightQuotient :
  (j : Nat) →
  Quotient.QuotientInterfaceOn
    (SO3WeightState j) (Matched.MatchedDihedralSector j)
matchedWeightQuotient j =
  record
    { equiv = matchedWeightEquivalence j
    ; proj = weightToMatchedSector
    ; respect-proj = λ equality → equality
    ; representative = matchedSectorRepresentative
    ; section = matchedSectorSection
    }

matchedWeightExactPresentation :
  (j : Nat) → Descent.ExactQuotientPresentation (matchedWeightQuotient j)
matchedWeightExactPresentation j =
  record
    { projectionComplete = λ equality → equality
    }

------------------------------------------------------------------------
-- Explicit fine enumeration; j=4 has nine weight states.
------------------------------------------------------------------------

pairWeightStates :
  ∀ {j} → List (Matched.PairIndex j) → List (SO3WeightState j)
pairWeightStates [] = []
pairWeightStates (index ∷ rest) =
  pairedWeight index positiveWeight
  ∷ pairedWeight index negativeWeight
  ∷ pairWeightStates rest

allSO3WeightStates : (j : Nat) → List (SO3WeightState j)
allSO3WeightStates j =
  centralWeight ∷ pairWeightStates (Matched.allPairIndices j)

j4FineWeightCountIsNine : length (allSO3WeightStates 4) ≡ 9
j4FineWeightCountIsNine = refl

------------------------------------------------------------------------
-- Full numerical-level family, including the p=2 spinor boundary.
------------------------------------------------------------------------

data CandidateWeightState (level : Nat) : Set where
  spinorUp : level ≡ 2 → CandidateWeightState level
  spinorDown : level ≡ 2 → CandidateWeightState level

  spatialWeight :
    (j : Spin.AngularMomentum0To35) →
    level ≡ Spin.jDimension j →
    SO3WeightState (Spin.jNat j) →
    CandidateWeightState level

candidateWeightToSector :
  ∀ {level} →
  CandidateWeightState level → Sector.CandidateReductionSector level
candidateWeightToSector (spinorUp equality) = Sector.spinorDoublet equality
candidateWeightToSector (spinorDown equality) = Sector.spinorDoublet equality
candidateWeightToSector (spatialWeight j equality weight) =
  Sector.spatialSector j equality (weightToMatchedSector weight)

candidateSectorRepresentative :
  ∀ {level} →
  Sector.CandidateReductionSector level → CandidateWeightState level
candidateSectorRepresentative (Sector.spinorDoublet equality) =
  spinorUp equality
candidateSectorRepresentative
  (Sector.spatialSector j equality sector) =
  spatialWeight j equality (matchedSectorRepresentative sector)

candidateSectorSection :
  ∀ {level}
    (sector : Sector.CandidateReductionSector level) →
  candidateWeightToSector (candidateSectorRepresentative sector) ≡ sector
candidateSectorSection (Sector.spinorDoublet equality) = refl
candidateSectorSection
  (Sector.spatialSector j equality Matched.selectedSinglet) = refl
candidateSectorSection
  (Sector.spatialSector j equality (Matched.pairedDoublet index)) = refl

candidateWeightEquivalence :
  (level : Nat) → Quotient.EquivalenceOn (CandidateWeightState level)
candidateWeightEquivalence level =
  record
    { _≈_ =
        λ left right → candidateWeightToSector left ≡ candidateWeightToSector right
    ; refl = λ state → refl
    ; sym = sym
    ; trans = trans
    }

candidateWeightQuotient :
  (level : Nat) →
  Quotient.QuotientInterfaceOn
    (CandidateWeightState level)
    (Sector.CandidateReductionSector level)
candidateWeightQuotient level =
  record
    { equiv = candidateWeightEquivalence level
    ; proj = candidateWeightToSector
    ; respect-proj = λ equality → equality
    ; representative = candidateSectorRepresentative
    ; section = candidateSectorSection
    }

candidateWeightExactPresentation :
  (level : Nat) →
  Descent.ExactQuotientPresentation (candidateWeightQuotient level)
candidateWeightExactPresentation level =
  record
    { projectionComplete = λ equality → equality
    }

------------------------------------------------------------------------
-- Exact local checks.
------------------------------------------------------------------------

spinorUpAndDownShareIrrepSector :
  candidateWeightToSector (spinorUp refl)
  ≡ candidateWeightToSector (spinorDown refl)
spinorUpAndDownShareIrrepSector = refl

j4PositiveNegativePairShareSector :
  (index : Matched.PairIndex 4) →
  weightToMatchedSector (pairedWeight index positiveWeight)
  ≡ weightToMatchedSector (pairedWeight index negativeWeight)
j4PositiveNegativePairShareSector index = refl

------------------------------------------------------------------------
-- Authority boundary.
------------------------------------------------------------------------

record SO3WeightMatchedDihedralBoundary : Set where
  field
    explicitSO3WeightCarrierConstructed : Bool
    explicitSO3WeightCarrierConstructedIsTrue :
      explicitSO3WeightCarrierConstructed ≡ true

    matchedDihedralSectorQuotientConstructed : Bool
    matchedDihedralSectorQuotientConstructedIsTrue :
      matchedDihedralSectorQuotientConstructed ≡ true

    level2SpinorFineCarrierConstructed : Bool
    level2SpinorFineCarrierConstructedIsTrue :
      level2SpinorFineCarrierConstructed ≡ true

    nineFineStatesToFiveSectorsConstructed : Bool
    nineFineStatesToFiveSectorsConstructedIsTrue :
      nineFineStatesToFiveSectorsConstructed ≡ true

    fineWeightHeckeCorrespondenceConstructedHere : Bool
    fineWeightHeckeCorrespondenceConstructedHereIsFalse :
      fineWeightHeckeCorrespondenceConstructedHere ≡ false

canonicalSO3WeightMatchedDihedralBoundary :
  SO3WeightMatchedDihedralBoundary
canonicalSO3WeightMatchedDihedralBoundary =
  record
    { explicitSO3WeightCarrierConstructed = true
    ; explicitSO3WeightCarrierConstructedIsTrue = refl
    ; matchedDihedralSectorQuotientConstructed = true
    ; matchedDihedralSectorQuotientConstructedIsTrue = refl
    ; level2SpinorFineCarrierConstructed = true
    ; level2SpinorFineCarrierConstructedIsTrue = refl
    ; nineFineStatesToFiveSectorsConstructed = true
    ; nineFineStatesToFiveSectorsConstructedIsTrue = refl
    ; fineWeightHeckeCorrespondenceConstructedHere = false
    ; fineWeightHeckeCorrespondenceConstructedHereIsFalse = refl
    }
