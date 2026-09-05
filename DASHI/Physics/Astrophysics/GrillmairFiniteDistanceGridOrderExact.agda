module DASHI.Physics.Astrophysics.GrillmairFiniteDistanceGridOrderExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EXECUTABLE DISTANCE-MODULUS GRID / FINITE ORDER INTERFACE
--
-- Grillmair shifts the colour-magnitude filter in 0.1-mag steps.  Published
-- source prose does not supply a machine-readable score table for every bin,
-- so DASHI computes the grid exactly but does not invent per-bin scores.
------------------------------------------------------------------------

record ScanBin : Set where
  constructor scan-bin
  field
    offsetTenthsMag : Nat
    score : Nat

open ScanBin public

scanOffsets4 : Nat → List Nat
scanOffsets4 start =
  start ∷
  suc start ∷
  suc (suc start) ∷
  suc (suc (suc start)) ∷
  []

zeroToThreeTenths : scanOffsets4 0 ≡ 0 ∷ 1 ∷ 2 ∷ 3 ∷ []
zeroToThreeTenths = refl

record FourBinScan : Set where
  constructor four-bin-scan
  field
    bin0 bin1 bin2 bin3 : ScanBin
    step01 : offsetTenthsMag bin1 ≡ suc (offsetTenthsMag bin0)
    step12 : offsetTenthsMag bin2 ≡ suc (offsetTenthsMag bin1)
    step23 : offsetTenthsMag bin3 ≡ suc (offsetTenthsMag bin2)
    sourceReference : String

open FourBinScan public

record FourBinBestWitness (scan : FourBinScan) : Set where
  constructor four-bin-best-witness
  field
    selected : ScanBin
    selectedIsOneOfBins : Bool
    selectedIsOneOfBinsIsTrue : selectedIsOneOfBins ≡ true
    geBin0 : score selected ≥ score (bin0 scan)
    geBin1 : score selected ≥ score (bin1 scan)
    geBin2 : score selected ≥ score (bin2 scan)
    geBin3 : score selected ≥ score (bin3 scan)

open FourBinBestWitness public

record GrillmairFiniteGridBoundary : Set where
  constructor grillmair-finite-grid-boundary
  field
    pointOneMagnitudeGridIsComputed : Bool
    pointOneMagnitudeGridIsComputedIsTrue : pointOneMagnitudeGridIsComputed ≡ true
    publishedPerBinNumericScoresLocated : Bool
    publishedPerBinNumericScoresLocatedIsFalse : publishedPerBinNumericScoresLocated ≡ false
    bestBinProofRequiresActualScores : Bool
    bestBinProofRequiresActualScoresIsTrue : bestBinProofRequiresActualScores ≡ true
    bestBinWouldEqualConfirmedStream : Bool
    bestBinWouldEqualConfirmedStreamIsFalse : bestBinWouldEqualConfirmedStream ≡ false

canonicalGrillmairFiniteGridBoundary : GrillmairFiniteGridBoundary
canonicalGrillmairFiniteGridBoundary =
  grillmair-finite-grid-boundary true refl false refl true refl false refl
