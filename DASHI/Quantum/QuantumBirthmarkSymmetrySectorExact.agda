{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkSymmetrySectorExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)

------------------------------------------------------------------------
-- ADDITIONAL-SYMMETRY / SECTOR ACCOUNTING
--
-- PRX explains that the standard 2/3 factor is recovered when the state is
-- confined to one symmetry subspace, and also when it uniformly spans all
-- symmetry-related subspaces.  Intermediate weighting can produce an overall
-- enhancement exceeding the standard value relative to the full Hilbert
-- space.  Therefore "additional symmetry" cannot be represented faithfully by
-- silently substituting the GOE value 3.
------------------------------------------------------------------------

data SectorOccupancy : Set where
  singleSector : SectorOccupancy
  uniformAllSectors : SectorOccupancy
  intermediateWeights : SectorOccupancy

record SymmetrySectorModel : Set₁ where
  field
    Sector : Set
    Weight : Set
    sectorCount : Nat
    weight : Sector → Weight
    NormalisedWeights : Set
    standardFactor : Nat
    OverallEnhancement : Set
    overallEnhancement : OverallEnhancement
    ExceedsStandardRelativeToFullSpace : OverallEnhancement → Set

record SectorClaimBoundary : Set where
  field
    singleSectorRecoversStandardFactor : Bool
    uniformSectorSpanRecoversStandardFactor : Bool
    intermediateSectorWeightingMayExceedStandardFactor : Bool
    sectorStructureCannotBeDropped : Bool
    degeneracyNeedsExplicitTreatment : Bool

sectorClaimBoundary : SectorClaimBoundary
sectorClaimBoundary = record
  { singleSectorRecoversStandardFactor = true
  ; uniformSectorSpanRecoversStandardFactor = true
  ; intermediateSectorWeightingMayExceedStandardFactor = true
  ; sectorStructureCannotBeDropped = true
  ; degeneracyNeedsExplicitTreatment = true
  }

record SectorPromotionFirewall : Set where
  field
    additionalSymmetryDoesNotMeanExactlyThree : Bool
    fullHilbertDimensionIsNotSectorDimension : Bool
    symmetryLabelAloneDoesNotDetermineWeights : Bool

sectorPromotionFirewall : SectorPromotionFirewall
sectorPromotionFirewall = record
  { additionalSymmetryDoesNotMeanExactlyThree = true
  ; fullHilbertDimensionIsNotSectorDimension = true
  ; symmetryLabelAloneDoesNotDetermineWeights = true
  }
