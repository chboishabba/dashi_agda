module DASHI.Biology.Agriculture.QueenslandWoodyLegumeGrassNitrogenCyclingRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.Agriculture.QueenslandWoodyLegumeGrassNitrogenCyclingExact as Q

radrizzani2011DOIPinned : Q.radrizzaniEtAl2011DOI ≡ "10.1071/CP10115"
radrizzani2011DOIPinned = refl

conrad2018DOIPinned : Q.conradEtAl2018DOI ≡ "10.1016/j.geoderma.2017.10.029"
conrad2018DOIPinned = refl

radrizzani2010DOIPinned : Q.radrizzaniEtAl2010DOI ≡ "10.1071/AN10062"
radrizzani2010DOIPinned = refl

catchpooleBlair1990TransferDOIPinned : Q.catchpooleBlair1990TransferDOI ≡ "10.1071/AR9900531"
catchpooleBlair1990TransferDOIPinned = refl

catchpooleBlair1990ResidueDOIPinned : Q.catchpooleBlair1990ResidueDOI ≡ "10.1071/AR9900539"
catchpooleBlair1990ResidueDOIPinned = refl

vallis1983DOIPinned : Q.vallis1983DOI ≡ "10.1071/AR9830367"
vallis1983DOIPinned = refl

sierraNygren2006DOIPinned : Q.sierraNygren2006DOI ≡ "10.1016/j.soilbio.2005.12.012"
sierraNygren2006DOIPinned = refl

fixedNNotGrassCapture :
  Q.woodyLegumeFixedNImpliesCompanionGrassCapture Q.canonicalWoodyLegumeGrassBoundary ≡ false
fixedNNotGrassCapture = refl

soilTNNotTransferPathway :
  Q.soilTotalNitrogenIdentifiesLegumeToGrassTransfer Q.canonicalWoodyLegumeGrassBoundary ≡ false
soilTNNotTransferPathway = refl

grazingRedistributionRetained :
  Q.grazingExcretaRedistributionMayBeDropped Q.canonicalWoodyLegumeGrassBoundary ≡ false
grazingRedistributionRetained = refl

animalIntakeNotExport :
  Q.consumedPastureNitrogenEqualsAnimalProductExport Q.canonicalWoodyLegumeGrassBoundary ≡ false
animalIntakeNotExport = refl

controlledTransferNotFieldTransfer :
  Q.controlledTransferImpliesFieldTransfer Q.canonicalWoodyLegumeGrassBoundary ≡ false
controlledTransferNotFieldTransfer = refl

transportRouteRetained :
  Q.leafFaecesUrineTransportRouteMayBeDropped Q.canonicalWoodyLegumeGrassBoundary ≡ false
transportRouteRetained = refl

placementRetained :
  Q.residuePlacementMayBeDroppedFromNitrogenCapture Q.canonicalWoodyLegumeGrassBoundary ≡ false
placementRetained = refl

fieldResidueNotLivingTransfer :
  Q.fieldResidueTransferImpliesLivingLegumeTransfer Q.canonicalWoodyLegumeGrassBoundary ≡ false
fieldResidueNotLivingTransfer = refl

externalDonorNotQueenslandObject :
  Q.externalTransferDonorCreatesQueenslandSameObjectReceipt Q.canonicalWoodyLegumeGrassBoundary ≡ false
externalDonorNotQueenslandObject = refl

chronosequenceNotLongitudinal :
  Q.pairedChronosequenceCreatesLongitudinalCausalTrajectory Q.canonicalWoodyLegumeGrassBoundary ≡ false
chronosequenceNotLongitudinal = refl

nutrientLimitationRetained :
  Q.phosphorusSulfurLimitationMayBeDroppedFromFixation Q.canonicalWoodyLegumeGrassBoundary ≡ false
nutrientLimitationRetained = refl

grassCompetitionRetained :
  Q.companionGrassCompetitionMayBeDropped Q.canonicalWoodyLegumeGrassBoundary ≡ false
grassCompetitionRetained = refl

acaciaNotClosed :
  Q.queenslandLeucaenaEvidenceClosesAcaciaAvoidedMineralN Q.canonicalWoodyLegumeGrassBoundary ≡ false
acaciaNotClosed = refl


externalFieldBelowGroundDonorNotQueenslandObject :
  Q.externalFieldBelowGroundTransferCreatesQueenslandSameObjectReceipt
    Q.canonicalWoodyLegumeGrassBoundary ≡ false
externalFieldBelowGroundDonorNotQueenslandObject = refl

referencePlantProblemRetained :
  Q.belowGroundTransferReferencePlantProblemMayBeDropped
    Q.canonicalWoodyLegumeGrassBoundary ≡ false
referencePlantProblemRetained = refl
