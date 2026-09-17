module DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaSenegalBNFEdaphicLESExact as Edaphic

peerJDOIPinned : Edaphic.peerJ2018DOI ≡ "10.7717/peerj.5232"
peerJDOIPinned = refl

isaacDOIPinned : Edaphic.isaac2011DOI ≡ "10.1016/j.foreco.2010.11.011"
isaacDOIPinned = refl

ageAloneNotAdequate :
  Edaphic.treeAgeAloneAdequateForFixation Edaphic.canonicalEdaphicBoundary ≡ false
ageAloneNotAdequate = refl

phosphorusAloneNotAdequate :
  Edaphic.soilPAloneAdequateForFixation Edaphic.canonicalEdaphicBoundary ≡ false
phosphorusAloneNotAdequate = refl

soilNDoesNotIdentifyBNFContribution :
  Edaphic.soilNAccretionIdentifiesBNFContribution Edaphic.canonicalEdaphicBoundary ≡ false
soilNDoesNotIdentifyBNFContribution = refl

nitrogenFixerLabelDoesNotCreateRealisedContribution :
  Edaphic.nitrogenFixingSpeciesLabelCreatesRealisedContribution Edaphic.canonicalEdaphicBoundary ≡ false
nitrogenFixerLabelDoesNotCreateRealisedContribution = refl

peerJAndHydrologyStaySeparate :
  Edaphic.sameSudanProgrammeCreatesSameMeasurementObject Edaphic.canonicalEdaphicBoundary ≡ false
peerJAndHydrologyStaySeparate = refl
