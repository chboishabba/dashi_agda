module DASHI.Chemistry.LineageAcquiredQuantitativePaymentsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact as Evidence

------------------------------------------------------------------------
-- SOURCE-BOUNDED QUANTITATIVE / DIRECT-MEASUREMENT PAYMENTS
--
-- Values are represented as source-faithful strings so units/context stay
-- inseparable from the cited measurement. These receipts do not invent a
-- globally normalized numeric semantics or transfer values across contexts.
------------------------------------------------------------------------

data AcquiredPaymentKind : Set where
  isotopeLineagePayment : AcquiredPaymentKind
  kineticParameterPayment : AcquiredPaymentKind
  activationDosePayment : AcquiredPaymentKind
  targetRecognitionPayment : AcquiredPaymentKind
  comparativeChemistryPayment : AcquiredPaymentKind
  provenanceDiscoveryPayment : AcquiredPaymentKind

record AcquiredEvidencePayment : Set where
  constructor acquiredEvidencePayment
  field
    source : Source.AttributedSource
    paymentKind : AcquiredPaymentKind
    coordinateKey : String
    measuredOrReportedValue : String
    unitsAndDefinition : String
    assayOrMethodContext : String
    exactLocator : String
    paidClaim : String
    unpaidResidual : String
    sameObjectScope : String
    paymentCreatesCausalGeneralization : Bool
    paymentCreatesCausalGeneralizationIsFalse : paymentCreatesCausalGeneralization ≡ false
    paymentCreatesPriority : Bool
    paymentCreatesPriorityIsFalse : paymentCreatesPriority ≡ false

open AcquiredEvidencePayment public

pah4aOxygenLineagePayment : AcquiredEvidencePayment
pah4aOxygenLineagePayment =
  acquiredEvidencePayment
    Evidence.pahOxygenLineage1985
    isotopeLineagePayment
    "PAH 4a-hydroxypterin oxygen source"
    "18O from molecular O2 detected in the 4a-hydroxy pterin adduct"
    "isotopic lineage / 18O-induced 13C NMR shift, not a concentration"
    "rat-liver PAH; [4a-13C]-6-methyltetrahydropterin + 18O2; spectroscopic assignment"
    "Biochemistry 24(12):2955-2958; DOI 10.1021/bi00333a022"
    "Molecular O2 is the source of the measured 4a-hydroxypterin oxygen in this PAH intermediate under the reported experiment."
    "complete substrate/product atom map, human isoform equivalence, all catalytic intermediates and in-vivo flux"
    "same PAH experiment/intermediate only"
    false refl false refl

pahHumanPhenylalanineKmPayment : AcquiredEvidencePayment
pahHumanPhenylalanineKmPayment =
  acquiredEvidencePayment
    Evidence.pahHumanKinetics1996
    kineticParameterPayment
    "recombinant human PAH apparent Km for phenylalanine with BH4"
    "0.050"
    "mM apparent Km"
    "recombinant human liver PAH expressed in E. coli; in-vitro enzyme study; BH4 present"
    "Arch Biochem Biophys 333(1):85-95; DOI 10.1006/abbi.1996.0367; abstract-reported value"
    "The study reports an apparent phenylalanine Km of 0.050 mM in the specified recombinant-human PAH/BH4 context."
    "Vmax/kcat, cellular concentration, tissue flux, other isoforms, alternate pH/temperature/substrate contexts"
    "same recombinant-human PAH assay context only"
    false refl false refl

pahHuman7BH4KmPayment : AcquiredEvidencePayment
pahHuman7BH4KmPayment =
  acquiredEvidencePayment
    Evidence.pahHumanKinetics1996
    kineticParameterPayment
    "recombinant human PAH apparent Km for 7-BH4"
    "0.2"
    "mM apparent Km"
    "recombinant human liver PAH expressed in E. coli; 7-BH4 substitution study"
    "Arch Biochem Biophys 333(1):85-95; DOI 10.1006/abbi.1996.0367; abstract-reported value"
    "The study reports an apparent Km of 0.2 mM for 7-BH4 in the stated recombinant-human PAH context."
    "natural-BH4 Km equivalence, in-vivo cofactor competition, tissue flux and cross-condition portability"
    "same recombinant-human PAH 7-BH4 assay context only"
    false refl false refl

pbCaFluorescenceCaEC50Payment : AcquiredEvidencePayment
pbCaFluorescenceCaEC50Payment =
  acquiredEvidencePayment
    Evidence.pbCaCalmodulin2000
    activationDosePayment
    "calmodulin fluorescence activation EC50 for free Ca2+"
    "approximately 450-500"
    "nM free Ca2+ EC50"
    "calmodulin conformational fluorescence using NPN/ANS in the reported aqueous assay"
    "NeuroToxicology 21(3):353-363; PMID 10894125; abstract"
    "Source-bounded Ca2+ EC50 for the fluorescence activation assay."
    "other calmodulin targets, intracellular effective concentrations, structural occupancy and organism toxicity"
    "same calmodulin fluorescence assay only"
    false refl false refl

pbCaFluorescencePbEC50Payment : AcquiredEvidencePayment
pbCaFluorescencePbEC50Payment =
  acquiredEvidencePayment
    Evidence.pbCaCalmodulin2000
    activationDosePayment
    "calmodulin fluorescence activation EC50 for free Pb2+"
    "approximately 400-550"
    "pM free Pb2+ EC50"
    "calmodulin conformational fluorescence using NPN/ANS in the reported aqueous assay"
    "NeuroToxicology 21(3):353-363; PMID 10894125; abstract"
    "Source-bounded Pb2+ EC50 for the fluorescence activation assay."
    "universal Pb/Ca potency ordering, other protein targets, intracellular dose-response and clinical inference"
    "same calmodulin fluorescence assay only"
    false refl false refl

pbCaPdeCaEC50Payment : AcquiredEvidencePayment
pbCaPdeCaEC50Payment =
  acquiredEvidencePayment
    Evidence.pbCaCalmodulin2000
    activationDosePayment
    "calmodulin-stimulated PDE activation EC50 for free Ca2+"
    "approximately 1200"
    "nM free Ca2+ EC50"
    "PDE1 activity stimulated by Ca2+/calmodulin in the reported assay"
    "NeuroToxicology 21(3):353-363; PMID 10894125; abstract"
    "Source-bounded Ca2+ EC50 for calmodulin-stimulated PDE activity."
    "other effectors, structural mechanism and organism-wide signalling"
    "same PDE/calmodulin assay only"
    false refl false refl

pbCaPdePbEC50Payment : AcquiredEvidencePayment
pbCaPdePbEC50Payment =
  acquiredEvidencePayment
    Evidence.pbCaCalmodulin2000
    activationDosePayment
    "calmodulin-stimulated PDE activation EC50 for free Pb2+"
    "approximately 430"
    "pM free Pb2+ EC50"
    "PDE1 activity stimulated by Pb2+/calmodulin in the reported assay"
    "NeuroToxicology 21(3):353-363; PMID 10894125; abstract"
    "Source-bounded Pb2+ EC50 for calmodulin-stimulated PDE activity."
    "universal Ca-site substitution, all downstream targets and organism dose-response"
    "same PDE/calmodulin assay only"
    false refl false refl

pbCaNnosTargetRecognitionPayment : AcquiredEvidencePayment
pbCaNnosTargetRecognitionPayment =
  acquiredEvidencePayment
    Evidence.pbCaCalmodulinESIMS2009
    targetRecognitionPayment
    "CaM:4M:nNOS target-peptide complex formation"
    "Ca2+ and Pb2+ supported the assayed CaM:4M:nNOS complex; Mg2+/Sr2+/Cd2+ did not in the reported comparison"
    "categorical ESI-MS target-recognition outcome"
    "calmodulin metal competition/ligation followed by a 20-residue neuronal NOS calmodulin-binding target peptide"
    "J Am Soc Mass Spectrom 20(6):1159-1171; DOI 10.1016/j.jasms.2009.02.008"
    "Pb2+ can preserve this particular downstream target-recognition coordinate despite distinct fine atomic identity under the reported conditions."
    "full-length nNOS function, cellular signalling, all CaM targets and toxicity"
    "same ESI-MS calmodulin/nNOS-peptide system only"
    false refl false refl

siliconBiocatalysisPayment : AcquiredEvidencePayment
siliconBiocatalysisPayment =
  acquiredEvidencePayment
    Evidence.biologicalCarbonSiliconBond2016
    comparativeChemistryPayment
    "biological C-Si bond-forming catalysis"
    "heme proteins catalyse carbene insertion into Si-H bonds; evolved Rma cyt c exceeds reported synthetic catalyst turnover by >15-fold"
    "source-reported qualitative reaction plus relative turnover statement"
    "in-vitro and in-vivo directed-evolution/biocatalysis experiments"
    "Science 354(6315):1048-1051; DOI 10.1126/science.aah6219"
    "Biological macromolecular machinery can catalyse C-Si bond formation under the reported conditions."
    "silicon as a primary backbone, self-sustaining silicon metabolism, prebiotic accessibility and life viability"
    "same evolved cytochrome-c reaction system only"
    false refl false refl

stanfordPublicArtifactDiscoveryPayment : AcquiredEvidencePayment
stanfordPublicArtifactDiscoveryPayment =
  acquiredEvidencePayment
    Evidence.kitzerowTimelinePublicRecord
    provenanceDiscoveryPayment
    "27 Nov 2023 Stanford contact supporting-artifact discoverability"
    "public timeline exposes an Adobe link labelled View Email Screenshot"
    "public-link discovery only; no content authentication"
    "originator-maintained timeline inspected; linked Adobe artifact failed retrieval in current environment"
    "Kitzerow Documented Timeline, 27 Nov 2023 entry"
    "A public originator record links to a purported supporting email screenshot for the claimed Stanford contact."
    "message contents, sender/recipient metadata, authenticity, completeness, institutional attribution, derivation/use and plagiarism"
    "public originator page only; linked artifact remains uninspected"
    false refl false refl

canonicalAcquiredEvidencePayments : List AcquiredEvidencePayment
canonicalAcquiredEvidencePayments =
  pah4aOxygenLineagePayment
  ∷ pahHumanPhenylalanineKmPayment
  ∷ pahHuman7BH4KmPayment
  ∷ pbCaFluorescenceCaEC50Payment
  ∷ pbCaFluorescencePbEC50Payment
  ∷ pbCaPdeCaEC50Payment
  ∷ pbCaPdePbEC50Payment
  ∷ pbCaNnosTargetRecognitionPayment
  ∷ siliconBiocatalysisPayment
  ∷ stanfordPublicArtifactDiscoveryPayment
  ∷ []

record AcquiredEvidenceBoundary : Set where
  constructor acquiredEvidenceBoundary
  field
    partialAtomMapPromotedToCompleteAtomMap : Bool
    partialAtomMapPromotedToCompleteAtomMapIsFalse : partialAtomMapPromotedToCompleteAtomMap ≡ false
    inVitroKineticsPromotedToInVivoFlux : Bool
    inVitroKineticsPromotedToInVivoFluxIsFalse : inVitroKineticsPromotedToInVivoFlux ≡ false
    oneTargetPbCaResultPromotedToUniversalSubstitution : Bool
    oneTargetPbCaResultPromotedToUniversalSubstitutionIsFalse : oneTargetPbCaResultPromotedToUniversalSubstitution ≡ false
    biologicalCSiBondFormationProvesSiliconLifeViability : Bool
    biologicalCSiBondFormationProvesSiliconLifeViabilityIsFalse : biologicalCSiBondFormationProvesSiliconLifeViability ≡ false
    publicArtifactLinkCountsAsAuthenticatedContents : Bool
    publicArtifactLinkCountsAsAuthenticatedContentsIsFalse : publicArtifactLinkCountsAsAuthenticatedContents ≡ false
    acquiredPaymentCreatesPriority : Bool
    acquiredPaymentCreatesPriorityIsFalse : acquiredPaymentCreatesPriority ≡ false

open AcquiredEvidenceBoundary public

canonicalAcquiredEvidenceBoundary : AcquiredEvidenceBoundary
canonicalAcquiredEvidenceBoundary =
  acquiredEvidenceBoundary false refl false refl false refl false refl false refl false refl
