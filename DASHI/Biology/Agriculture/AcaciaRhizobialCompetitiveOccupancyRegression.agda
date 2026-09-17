module DASHI.Biology.Agriculture.AcaciaRhizobialCompetitiveOccupancyRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AcaciaRhizobialCompetitiveOccupancyExact as O

sarr2005DOIPinned : O.sarrEtAl2005DOI ≡ "10.1007/s00248-004-0077-8"
sarr2005DOIPinned = refl

sarr2005PMIDPinned : O.sarrEtAl2005PMID ≡ "16184338"
sarr2005PMIDPinned = refl

sarrLesueur2007DOIPinned : O.sarrLesueur2007DOI ≡ "10.1007/s11274-006-9288-0"
sarrLesueur2007DOIPinned = refl

strainIdentityDoesNotDetermineOccupancy :
  O.strainIdentityAloneDeterminesNoduleOccupancy O.canonicalOccupancyBoundary ≡ false
strainIdentityDoesNotDetermineOccupancy = refl

soilBackgroundCannotBeDropped :
  O.indigenousPopulationAndSoilContextMustRemainIndexed O.canonicalOccupancyBoundary ≡ true
soilBackgroundCannotBeDropped = refl

nurseryOccupancyDoesNotUniversaliseToField :
  O.nurseryOccupancyImpliesFieldOccupancy O.canonicalOccupancyBoundary ≡ false
nurseryOccupancyDoesNotUniversaliseToField = refl

multiAcaciaResultDoesNotCreateSenegalRankReversal :
  O.multiAcaciaTransitionCreatesAcaciaSenegalRankReversal O.canonicalOccupancyBoundary ≡ false
multiAcaciaResultDoesNotCreateSenegalRankReversal = refl

occupancyDoesNotCreateFixationFlux :
  O.noduleOccupancyImpliesFixedNFlux O.canonicalOccupancyBoundary ≡ false
occupancyDoesNotCreateFixationFlux = refl
