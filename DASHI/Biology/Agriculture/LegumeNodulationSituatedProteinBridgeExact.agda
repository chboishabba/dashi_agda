module DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Protein.NitrogenaseSituatedProteinWitnessExact as Nitrogenase

------------------------------------------------------------------------
-- LEGUME NODULATION <-> SITUATED-PROTEIN BRIDGE
--
-- Acacia-specific nod/nif/LCO/heat-stress papers are retained independently
-- from the Lotus/barley receptor-engineering donor.  Structural analogy does
-- not transfer organism identity or mechanism.
------------------------------------------------------------------------

record NodulationSource : Set where
  constructor nodulation-source
  field
    attributedSource : Attribution.AttributedSource
    pmid : String
    pmcid : String
    sourceRole : String
    boundedReading : String
    excludedPromotion : String
open NodulationSource public

bakhoum2015 : NodulationSource
bakhoum2015 = nodulation-source
  (Attribution.mkDOISource
    "Niokhor Bakhoum; Antoine Galiana; Christine Le Roux; Aboubacry Kane; Robin Duponnois; Fatou Ndoye; Dioumacor Fall; Kandioura Noba; Samba Ndao Sylla; Diegane Diouf"
    "Phylogeny of nodulation genes and symbiotic diversity of Acacia senegal (L.) Willd. and A. seyal (Del.) Mesorhizobium strains from different regions of Senegal"
    "Microbial Ecology 69(3):641-651"
    "2015"
    "10.1007/s00248-014-0507-1"
    "https://pubmed.ncbi.nlm.nih.gov/25315832/"
    Attribution.academicArticleSource
    "Acacia-specific symbiotic-gene and inoculation-efficiency source."
    Attribution.publicAttribution)
  "25315832"
  "not recorded by this atlas"
  "Acacia/Senegal nodA, nodC, nifH phylogeny plus nodulation, biomass, ARA and SARA efficiency tests"
  "Supports Acacia-specific separation between symbiotic-gene identity and measured nodulation/fixation-proxy outcomes in the reported inoculation tests."
  "nodA/nodC/nifH presence or sequence identity alone does not establish realised fixation rate, plant N delivery or field deployment authority."

nowak2004 : NodulationSource
nowak2004 = nodulation-source
  (Attribution.mkDOISource
    "Petri Nowak; Laura Soupas; Jane Thomas-Oates; Kristina Lindstrom"
    "Acacia senegal and Prosopis chilensis-nodulating rhizobia Sinorhizobium arboris HAMBI 2361 and S. kostiense HAMBI 2362 produce tetra- and pentameric LCOs that are N-methylated, O-6-carbamoylated and partially sulfated"
    "Carbohydrate Research 339(6):1061-1067"
    "2004"
    "10.1016/j.carres.2004.02.013"
    "https://pubmed.ncbi.nlm.nih.gov/15063192/"
    Attribution.academicArticleSource
    "Acacia-nodulating rhizobial LCO/Nod-factor chemistry source."
    Attribution.publicAttribution)
  "15063192"
  "not recorded by this atlas"
  "Lipochitooligosaccharide structural characterization in Acacia-senegal-nodulating Sinorhizobium strains"
  "Supports explicit Nod-factor/LCO identity as a signalling coordinate rather than an undifferentiated rhizobium token."
  "LCO structure alone does not prove successful infection, nodule formation, active nitrogenase or net N transfer."

rasanen1999 : NodulationSource
rasanen1999 = nodulation-source
  (Attribution.mkDOISource
    "Leena A. Rasanen; Kristina Lindstrom"
    "The effect of heat stress on the symbiotic interaction between Sinorhizobium sp. and Acacia senegal"
    "FEMS Microbiology Ecology 28(1):63-74"
    "1999"
    "10.1111/j.1574-6941.1999.tb00561.x"
    "https://academic.oup.com/femsec/article/28/1/63/434743"
    Attribution.academicArticleSource
    "Acacia-specific temperature-context source for infection/nodulation failure and reversibility."
    Attribution.publicAttribution)
  "not recorded by this atlas"
  "not recorded by this atlas"
  "Heat-stress perturbation of Sinorhizobium-Acacia senegal infection and nodulation"
  "Supports a context-sensitive symbiosis distinction: rhizobia can remain present while infection threads/nodulation fail under sufficiently high root temperature, with later recovery after stress."
  "Rhizobial presence does not determine successful infection, nodule formation or active fixation independently of environmental context."

tsitsikli2025 : NodulationSource
tsitsikli2025 = nodulation-source
  (Attribution.mkDOISource
    "Magdalini Tsitsikli; Bine Simonsen; Thi-Bich Luu; Maria M. Larsen; Camilla G. Andersen; Kira Gysel; Damiano Lironi; Christina Kronauer; Henriette Rubsam; Simon B. Hansen; Rene Baerentsen; Jesper Lundsgaard Wulff; Sarah Holt Johansen; Gulendam Sezer; Jens Stougaard; Kasper Rojkjaer Andersen; Simona Radutoiu"
    "Two residues reprogram immunity receptors for nitrogen-fixing symbiosis"
    "Nature 648:443-450"
    "2025"
    "10.1038/s41586-025-09696-3"
    "https://pubmed.ncbi.nlm.nih.gov/41193803/"
    Attribution.academicArticleSource
    "Residue-level receptor-signalling donor for situated-protein query adequacy."
    Attribution.publicAttribution)
  "41193803"
  "not recorded by this atlas"
  "NFR1/CERK-family residue-level signalling specificity in Lotus/barley engineering experiments"
  "Supports that highly related receptor identities can differ in symbiotic-vs-immune signalling output because local residue state matters."
  "Does not establish Acacia receptor sequence, Acacia signalling mechanism, nodule phenotype or field fixation rate."

nodulationAttributedAtlas : Attribution.AttributedSourceAtlas
nodulationAttributedAtlas = Attribution.mkSourceAtlas
  "Legume nodulation situated-protein bridge sources"
  "DASHI.Biology.Agriculture.LegumeNodulationSituatedProteinBridgeExact"
  (attributedSource bakhoum2015 ∷ attributedSource nowak2004 ∷ attributedSource rasanen1999 ∷ attributedSource tsitsikli2025 ∷ [])
  "Acacia-specific nod/nif/LCO/environmental-context sources plus a Lotus/barley receptor-state structural donor; cross-organism transfer remains blocked."

------------------------------------------------------------------------
-- Receptor-state query witness.
------------------------------------------------------------------------

data ReceptorIdentity : Set where
  nodFactorReceptorFamily : ReceptorIdentity

data ReceptorSignalOutput : Set where
  symbioticSignal : ReceptorSignalOutput
  immuneLikeSignal : ReceptorSignalOutput

data ReceptorWorld : Set where
  symbiosisDeterminantWorld : ReceptorWorld
  alternateResidueWorld : ReceptorWorld

receptorIdentity : ReceptorWorld → ReceptorIdentity
receptorIdentity symbiosisDeterminantWorld = nodFactorReceptorFamily
receptorIdentity alternateResidueWorld = nodFactorReceptorFamily

signalOutput : ReceptorWorld → ReceptorSignalOutput
signalOutput symbiosisDeterminantWorld = symbioticSignal
signalOutput alternateResidueWorld = immuneLikeSignal

sameReceptorIdentity :
  receptorIdentity symbiosisDeterminantWorld ≡ receptorIdentity alternateResidueWorld
sameReceptorIdentity = refl

signalOutputSeparates :
  signalOutput symbiosisDeterminantWorld ≡ signalOutput alternateResidueWorld → ⊥
signalOutputSeparates ()

data ReceptorQuery : Set where
  signallingOutputQuery : ReceptorQuery

receptorAnswer : ReceptorQuery → ReceptorWorld → ReceptorSignalOutput
receptorAnswer signallingOutputQuery world = signalOutput world

receptorSemantics : Query.QuerySemantics ReceptorWorld ReceptorQuery ReceptorSignalOutput
receptorSemantics = Query.querySemantics receptorAnswer

receptorIdentityDefect :
  Query.QueryAdequacyDefect receptorIdentity receptorSemantics signallingOutputQuery
receptorIdentityDefect = Query.queryAdequacyDefect
  symbiosisDeterminantWorld
  alternateResidueWorld
  sameReceptorIdentity
  signalOutputSeparates

receptorSituatedWitness : Situated.SituatedProteinQueryWitness
receptorSituatedWitness = Situated.situated-protein-query-witness
  ReceptorWorld
  ReceptorIdentity
  ReceptorQuery
  ReceptorSignalOutput
  receptorIdentity
  receptorSemantics
  signallingOutputQuery
  receptorIdentityDefect
  Situated.slowlyVarying
  "local receptor residue state separates symbiotic and immune-like signalling outputs while coarse receptor-family identity is unchanged"
  "Tsitsikli et al. 2025 DOI 10.1038/s41586-025-09696-3 PMID 41193803 owns the bounded residue/signalling premise; Bakhoum 2015 DOI 10.1007/s00248-014-0507-1 PMID 25315832, Nowak 2004 DOI 10.1016/j.carres.2004.02.013 PMID 15063192 and Rasanen/Lindstrom 1999 DOI 10.1111/j.1574-6941.1999.tb00561.x retain Acacia-specific nod/nif/LCO/environment context."
  "DASHI owns the finite query-inadequacy witness and the cross-source bridge; the witness is not an additional Acacia observation."

receptorIdentityNotAdequateForSignal :
  Query.AdequateFor receptorIdentity receptorSemantics signallingOutputQuery → ⊥
receptorIdentityNotAdequateForSignal =
  Situated.witnessBlocksCoarseAdequacy receptorSituatedWitness

------------------------------------------------------------------------
-- Stage separation.  These are no-promotion boundaries, not causal-denial
-- claims: later stages require additional receipts rather than being inferred
-- definitionally from earlier ones.
------------------------------------------------------------------------

record NodulationBoundary : Set where
  constructor nodulation-boundary
  field
    receptorIdentityAloneAdequate : Bool
    nodFactorRecognitionImpliesSuccessfulNodulation : Bool
    successfulNodulationImpliesActiveNitrogenase : Bool
    activeNitrogenaseImpliesIntegratedFixedNDelivery : Bool
    nifHIdentityImpliesFixationRate : Bool
    rhizobialPresenceImpliesSuccessfulSymbiosis : Bool
    lotusBarleyMechanismTransfersToAcacia : Bool
    nitrogenaseProtectionMechanismTransfersToNodule : Bool
    integratedFixedNDeliveryImpliesSoilNOutcome : Bool
open NodulationBoundary public

canonicalNodulationBoundary : NodulationBoundary
canonicalNodulationBoundary = nodulation-boundary
  false false false false false false false false false

receptorIdentityAloneIsInadequate :
  receptorIdentityAloneAdequate canonicalNodulationBoundary ≡ false
receptorIdentityAloneIsInadequate = refl

noduleDoesNotCreateActiveNitrogenase :
  successfulNodulationImpliesActiveNitrogenase canonicalNodulationBoundary ≡ false
noduleDoesNotCreateActiveNitrogenase = refl

nitrogenaseSituatedBoundaryReused : Nitrogenase.NitrogenaseSituatedBoundary
nitrogenaseSituatedBoundaryReused = Nitrogenase.canonicalNitrogenaseBoundary

attributionRule : String
attributionRule =
  "Bakhoum et al., Nowak et al., Rasanen/Lindstrom and Tsitsikli et al. retain source ownership of their cited propositions. DASHI owns receptor-query factorisation, stage firewalls and cross-source synthesis. DOI/PMID metadata records provenance only; Lotus/barley receptor results and Azotobacter nitrogenase protection are not silently promoted into Acacia mechanisms."
