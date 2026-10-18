module DASHI.Biology.Agriculture.AustralianGrassDiazotrophNitrogenRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.AustralianGrassDiazotrophNitrogenExact as G

gupta2019DOIPinned :
  G.guptaEtAl2019DOI ≡ "10.3389/fmolb.2019.00115"
gupta2019DOIPinned = refl

gupta2019PMIDPinned : G.guptaEtAl2019PMID ≡ "31750314"
gupta2019PMIDPinned = refl

gupta2019PMCIDPinned : G.guptaEtAl2019PMCID ≡ "PMC6848460"
gupta2019PMCIDPinned = refl

venado2025DOIPinned :
  G.venadoEtAl2025DOI ≡ "10.1371/journal.pbio.3003037"
venado2025DOIPinned = refl

venado2025PMIDPinned : G.venadoEtAl2025PMID ≡ "40029899"
venado2025PMIDPinned = refl

venado2025PMCIDPinned : G.venadoEtAl2025PMCID ≡ "PMC12136154"
venado2025PMCIDPinned = refl

nFixingRoleDoesNotIdentifyMechanism :
  G.sameBiologicalNInputRoleImpliesSameMechanism G.canonicalGrassDiazotrophBoundary ≡ false
nFixingRoleDoesNotIdentifyMechanism = refl

nifHNotPlantNContribution :
  G.nifHAbundanceImpliesPlantNitrogenContribution G.canonicalGrassDiazotrophBoundary ≡ false
nifHNotPlantNContribution = refl

inVitroPotentialNotAnnualFieldContribution :
  G.inVitroFixationPotentialImpliesAnnualFieldNContribution G.canonicalGrassDiazotrophBoundary ≡ false
inVitroPotentialNotAnnualFieldContribution = refl

plantCompartmentRetained :
  G.plantCompartmentMayBeDropped G.canonicalGrassDiazotrophBoundary ≡ false
plantCompartmentRetained = refl

sorghumDoesNotBecomeSudangrass :
  G.sorghumBicolorMucilageCreatesSudangrassSameObjectEvidence G.canonicalGrassDiazotrophBoundary ≡ false
sorghumDoesNotBecomeSudangrass = refl

environmentAndGenotypeRetained :
  G.environmentAndGenotypeMayBeDropped G.canonicalGrassDiazotrophBoundary ≡ false
environmentAndGenotypeRetained = refl

avoidedMineralNStillNotPaid :
  G.sorghumNdfaCreatesAvoidedMineralNReceipt G.canonicalGrassDiazotrophBoundary ≡ false
avoidedMineralNStillNotPaid = refl
