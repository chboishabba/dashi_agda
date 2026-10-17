module DASHI.Biology.BH4NongNangMaxCutRegression where

open import DASHI.Core.Prelude

import DASHI.Biology.BH4SystemStateExact as System
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide
import DASHI.Biology.NitrousOxideMetabolismEvidenceExact as Nang
import DASHI.Biology.NonginNangNitrogenOxideRefinementExact as Nongin
import DASHI.Biology.KitzerowBH4SystemNongNangMaxCutExact as MaxCut
import DASHI.Biology.UniProtExternalKnowledgeExact as UniProt
import DASHI.Biology.UniProtBH4PanelCertificateExact as Panel
import DASHI.Biology.ExternalBiologyEvidenceCore as External

------------------------------------------------------------------------
-- Regression witnesses for the BH4 / NONG-NANG max-cut.
------------------------------------------------------------------------

nitricOxideIsNotNitrousOxide :
  Oxide.nitricOxide ≡ Oxide.nitrousOxide → ⊥
nitricOxideIsNotNitrousOxide = Oxide.nitricOxideNotNitrousOxide

coarseNitrogenOxideCannotServeFineChemicalConsumer :
  Nongin.CoarseChemicalDescent → ⊥
coarseNitrogenOxideCannotServeFineChemicalConsumer =
  Nongin.coarseNitrogenOxideCannotServeFineConsumer

proteinPresenceDoesNotEstablishNOSUncoupling :
  Oxide.NOSCouplingBoundary.proteinPresenceEstablishesUncoupling
    Oxide.canonicalNOSCouplingBoundary
  ≡ false
proteinPresenceDoesNotEstablishNOSUncoupling = refl

reactionAnnotationDoesNotPayWholeFluxBalance :
  System.BH4SystemBoundary.reactionAnnotationPaysWholeFluxBalance
    System.canonicalBH4SystemBoundary
  ≡ false
reactionAnnotationDoesNotPayWholeFluxBalance = refl

nangCobalaminLaneDoesNotBecomeNOSLane :
  Nang.NitrousOxideMetabolismBoundary.nitrousOxideEvidenceCreatesNOSUncouplingProof
    Nang.canonicalNitrousOxideMetabolismBoundary
  ≡ false
nangCobalaminLaneDoesNotBecomeNOSLane = refl

nongNangAliasDoesNotIdentifyNitricOxide :
  Nongin.NongNangGenealogyBoundary.nongNangAliasIdentifiesNitricOxide
    Nongin.canonicalNongNangGenealogyBoundary
  ≡ false
nongNangAliasDoesNotIdentifyNitricOxide = refl

exactPanelAcquisitionIsClosed :
  MaxCut.KitzerowBH4SystemMaxCutBoundary.exactProteinPanelAcquisitionClosed
    MaxCut.canonicalKitzerowBH4SystemMaxCutBoundary
  ≡ true
exactPanelAcquisitionIsClosed = refl

allSixteenPanelRecordsArePinned :
  Panel.UniProtBH4PanelBoundary.everyMemberBytePinned
    Panel.canonicalUniProtBH4PanelBoundary
  ≡ true
allSixteenPanelRecordsArePinned = refl

completePanelStillDoesNotCreateAllocatorFlux :
  Panel.UniProtBH4PanelBoundary.completePanelCreatesAllocatorFlux
    Panel.canonicalUniProtBH4PanelBoundary
  ≡ false
completePanelStillDoesNotCreateAllocatorFlux = refl

isolatedNodesDoNotConfirmKitzerowWholeGraph :
  MaxCut.KitzerowBH4SystemMaxCutBoundary.isolatedNodeSupportConfirmsWholeGraph
    MaxCut.canonicalKitzerowBH4SystemMaxCutBoundary
  ≡ false
isolatedNodesDoNotConfirmKitzerowWholeGraph = refl

n2oLaneDoesNotCreateKitzerowMechanism :
  MaxCut.KitzerowBH4SystemMaxCutBoundary.nitrousOxideLaneCreatesKitzerowMechanism
    MaxCut.canonicalKitzerowBH4SystemMaxCutBoundary
  ≡ false
n2oLaneDoesNotCreateKitzerowMechanism = refl

qdprSnapshotIsBytePinned :
  External.exactBinaryPinned UniProt.uniProt2026-03 ≡ true
qdprSnapshotIsBytePinned = refl

sprAccessionIsCurrentHumanSPR :
  MaxCut.accession MaxCut.spr ≡ "P35270"
sprAccessionIsCurrentHumanSPR = refl

nos3AccessionIsCurrentHumanNOS3 :
  MaxCut.accession MaxCut.nos3 ≡ "P29474"
nos3AccessionIsCurrentHumanNOS3 = refl

agmoAccessionIsCurrentHumanAGMO :
  MaxCut.accession MaxCut.agmo ≡ "Q6ZNB7"
agmoAccessionIsCurrentHumanAGMO = refl
