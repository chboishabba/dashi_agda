module DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact as Nif

seefeldtDOIIsAttached :
  Attribution.doiState (Nif.attributedSource Nif.seefeldt2009) ≡
  Attribution.doiRecorded "10.1146/annurev.biochem.78.070907.103812"
seefeldtDOIIsAttached = refl

warmackReesDOIIsAttached :
  Attribution.doiState (Nif.attributedSource Nif.warmackRees2024) ≡
  Attribution.doiRecorded "10.1038/s41467-024-54713-0"
warmackReesDOIIsAttached = refl

narehoodDOIIsAttached :
  Attribution.doiState (Nif.attributedSource Nif.narehood2025) ≡
  Attribution.doiRecorded "10.1038/s41586-024-08311-1"
narehoodDOIIsAttached = refl

payaTormoDOIIsAttached :
  Attribution.doiState (Nif.attributedSource Nif.payaTormo2025) ≡
  Attribution.doiRecorded "10.1038/s41589-025-02070-4"
payaTormoDOIIsAttached = refl

proteinIdentityProjectionIsInadequate :
  Nif.proteinIdentityAloneAdequate Nif.canonicalNitrogenaseBoundary ≡ false
proteinIdentityProjectionIsInadequate = refl

balancedStoichiometryDoesNotCreateEffectiveFlux :
  Nif.balancedStoichiometryCreatesEffectiveFlux Nif.canonicalNitrogenaseBoundary ≡ false
balancedStoichiometryDoesNotCreateEffectiveFlux = refl

azotobacterProtectionIsNotAcaciaMechanism :
  Nif.azotobacterProtectionTransfersToAcacia Nif.canonicalNitrogenaseBoundary ≡ false
azotobacterProtectionIsNotAcaciaMechanism = refl

nifENStateDoesNotCreateCatalyticFlux :
  Nif.nifENMaturationStateCreatesCatalyticFlux Nif.canonicalNitrogenaseBoundary ≡ false
nifENStateDoesNotCreateCatalyticFlux = refl
