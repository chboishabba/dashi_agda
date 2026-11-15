module DASHI.Biology.Physical.OriginalDmscTwoGenotypeMeasuredExact where

------------------------------------------------------------------------
-- P0/P5: SMALL, SOURCE-IDENTIFIED ORIGINAL MEASURED BIOLOGICAL WITNESS.
--
-- Original Kuo et al. 2020 Shine-Dalgarno dmsC assay, as preserved in
-- cmarti/shine_dalgarno/data/dmsc.csv at Git blob
-- 151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c.
--
-- CSV first two rows (only the original dmsC replicates):
--   AAAAAAAAA : .256, .769, .664
--   AAAAAAAAC : .389, .908, .695
--
-- Decimal inputs are represented EXACTLY as thousandths of the original
-- assay readout; these are not physical SI voltages or inferred traits.
-- The means below are raw replicate arithmetic, not significance tests.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

data RNABase : Set where
  A C G U : RNABase

record RNA8 : Set where
  constructor rna8
  field
    first second third fourth fifth sixth seventh eighth : RNABase

record RNA9 : Set where
  constructor rna9
  field
    prefix : RNA8
    lastBase : RNABase

allA8 : RNA8
allA8 = rna8 A A A A A A A A

firstOriginalGenotype secondOriginalGenotype : RNA9
firstOriginalGenotype = rna9 allA8 A
secondOriginalGenotype = rna9 allA8 C

sameEightBasePrefix :
  RNA9.prefix firstOriginalGenotype
    ≡ RNA9.prefix secondOriginalGenotype
sameEightBasePrefix = refl

differentNinthBase :
  RNA9.lastBase firstOriginalGenotype
    ≡ RNA9.lastBase secondOriginalGenotype → ⊥
differentNinthBase ()

record ThreeReplicateMeasuredMean : Set where
  constructor threeReplicateMeasuredMean
  field
    replicate1Thousandths : Nat
    replicate2Thousandths : Nat
    replicate3Thousandths : Nat
    meanThousandths : Nat
    exactMeanIdentity :
      replicate1Thousandths + replicate2Thousandths
        + replicate3Thousandths ≡ 3 * meanThousandths

open ThreeReplicateMeasuredMean public

originalAAAA : ThreeReplicateMeasuredMean
originalAAAA = threeReplicateMeasuredMean 256 769 664 563 refl

originalAAAC : ThreeReplicateMeasuredMean
originalAAAC = threeReplicateMeasuredMean 389 908 695 664 refl

record OriginalDmscMeasuredNineMer : Set where
  constructor originalDmscMeasuredNineMer
  field
    genomeRNA : RNA9
    originalGenotypeText : String
    originalDataGitBlob : String
    originalResearchDOI : String
    rawReplicateObservation : ThreeReplicateMeasuredMean

originalOne originalTwo : OriginalDmscMeasuredNineMer
originalOne = originalDmscMeasuredNineMer
  firstOriginalGenotype "AAAAAAAAA"
  "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
  "10.1101/gr.260182.119" originalAAAA

originalTwo = originalDmscMeasuredNineMer
  secondOriginalGenotype "AAAAAAAAC"
  "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
  "10.1101/gr.260182.119" originalAAAC

sharedOriginalDataIdentity :
  OriginalDmscMeasuredNineMer.originalDataGitBlob originalOne
    ≡ OriginalDmscMeasuredNineMer.originalDataGitBlob originalTwo
sharedOriginalDataIdentity = refl

-- Exactly different arithmetic sample means, with NO assertion of a
-- statistically resolved biological effect or an organismal attractor.
differentRawMeanReadouts :
  meanThousandths
    (OriginalDmscMeasuredNineMer.rawReplicateObservation originalOne)
  ≡ meanThousandths
    (OriginalDmscMeasuredNineMer.rawReplicateObservation originalTwo) → ⊥
differentRawMeanReadouts ()

-- Provenance-bound, three-replicate quantitative fixture only.  It does
-- NOT assert RNA coding equivalence, a molecular mechanism, or an
-- instantiated source-to-CellStateAttractor dynamics map.
