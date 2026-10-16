module DASHI.Biology.KitzerowBH4TransportCarrierProbeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.KitzerowBH4NeuralContextSourceAtlasExact as NeuralSources
import DASHI.Biology.KitzerowBH4RedoxSpatialDiscriminatorExact as Topology

------------------------------------------------------------------------
-- TRANSPORT/CARRIER/INTERCELLULAR-TRANSFER TEST
--
-- The previous neural passive-diffusion result is not generalized into a
-- universal transport theorem. Later experiments identify transporter-mediated
-- pterin/BH4 transport in other cell/tissue contexts and quantify transcellular
-- BH4 movement. The still-unpaid coordinate is the target-relevant neural
-- donor-to-recipient molecular flux, not transport existence in general.
------------------------------------------------------------------------

choiJangKimHwang2000Release : Source.AttributedSource
choiJangKimHwang2000Release =
  Source.mkDOISource
    "Hyun Jin Choi; Yeon Joo Jang; Hyo Jung Kim; Onyou Hwang"
    "Tetrahydrobiopterin Is Released from and Causes Preferential Death of Catecholaminergic Cells by Oxidative Stress"
    "Molecular Pharmacology 58(3):633-640"
    "2000"
    "10.1124/mol.58.3.633"
    "https://pubmed.ncbi.nlm.nih.gov/10953058/"
    Source.academicArticleSource
    "Primary catecholaminergic-cell study. Pays spontaneous extracellular BH4 release from cells of BH4 synthesis and source-conditioned extracellular BH4 effects; release was not further enhanced by calcium influx. It does not quantify physiological donor-to-recipient neural BH4 flux."
    Source.publicAttribution

ohashiEtAl2009CacoTransport : Source.AttributedSource
ohashiEtAl2009CacoTransport =
  Source.mkDOISource
    "Akiko Ohashi; M. Fukumuro; K. Sawabe; Kaori Mamada; Yuko Sugawara; Hiroshi Matsuoka; Hiroyuki Hasegawa"
    "Transcellular relocation of tetrahydrobiopterin across Caco-2 cells: a model study of tetrahydrobiopterin absorption through epithelial cells of intestinal mucosa"
    "Journal of Inherited Metabolic Disease 32(1):73-78"
    "2009"
    "10.1007/s10545-008-0961-3"
    "https://pubmed.ncbi.nlm.nih.gov/18979179/"
    Source.academicArticleSource
    "Primary polarized Caco-2 Transwell experiment. Pays apical-to-basolateral BH4 movement at about 150 pmol/h per well for 100 micromol/L apical BH4 and strong inhibition by benzbromarone, supporting transporter-driven transcellular movement in this epithelial model. It is not a neural donor-to-recipient rate."
    Source.publicAttribution

ohashiEtAl2011ENT : Source.AttributedSource
ohashiEtAl2011ENT =
  Source.mkDOISource
    "Akiko Ohashi; Yuko Sugawara; Kaori Mamada; Yoshinori Harada; Tomomi Sumi; Naohiko Anzai; Shin Aizawa; Hiroyuki Hasegawa"
    "Membrane transport of sepiapterin and dihydrobiopterin by equilibrative nucleoside transporters: a plausible gateway for the salvage pathway of tetrahydrobiopterin biosynthesis"
    "Molecular Genetics and Metabolism 102(1):18-28"
    "2011"
    "10.1016/j.ymgme.2010.09.005"
    "https://pubmed.ncbi.nlm.nih.gov/20956085/"
    Source.academicArticleSource
    "Primary HeLa/Xenopus-oocyte/endothelial transport study. Pays hENT2 transport of sepiapterin, BH2 and BH4 with SP>BH2>BH4 efficiency and weaker hENT1 transport, plus ENT-sensitive precursor distribution under exogenous supplementation. It does not establish ENT2 as the unique physiological neural BH4 carrier."
    Source.publicAttribution

ohashiEtAl2017OAT : Source.AttributedSource
ohashiEtAl2017OAT =
  Source.mkDOISource
    "Akiko Ohashi; Kaori Mamada; Tomonori Harada; Masako Naito; Tomihisa Takahashi; Shin Aizawa; Hiroyuki Hasegawa"
    "Organic anion transporters, OAT1 and OAT3, are crucial biopterin transporters involved in bodily distribution of tetrahydrobiopterin and exclusion of its excess"
    "Molecular and Cellular Biochemistry 435(1):97-108"
    "2017"
    "10.1007/s11010-017-3060-7"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC5632347/"
    Source.academicArticleSource
    "Primary rat-kidney-slice, transporter-expressing cell and Xenopus-oocyte study. Pays probenecid-sensitive OAT1/OAT3 transport of BH4/BH2-related biopterins in renal/body-distribution contexts. It does not establish a universal neural transporter or a donor-to-recipient synaptic BH4 flux."
    Source.publicAttribution

canonicalTransportProbeSources : List Source.AttributedSource
canonicalTransportProbeSources =
  NeuralSources.anastasiadisKuhnLevine1994Uptake
  ∷ choiJangKimHwang2000Release
  ∷ NeuralSources.choiEtAl2003HumanNnosUptake
  ∷ ohashiEtAl2009CacoTransport
  ∷ ohashiEtAl2011ENT
  ∷ ohashiEtAl2017OAT
  ∷ []

record TransportMeasurement : Set where
  constructor transportMeasurement
  field
    key : String
    system : String
    transportedSpecies : String
    route : String
    numericRate : String
    mechanism : String
    sourceReference : String
    sameObjectNeuralDonorRecipient : Bool

open TransportMeasurement public

neuralPassiveUptakeMeasurement : TransportMeasurement
neuralPassiveUptakeMeasurement =
  transportMeasurement
    "1994 neural/PC12 BH4 uptake"
    "rat synaptosomes + PC12 + rat striatum"
    "BH4"
    "extracellular to intracellular"
    "concentration-dependent accumulation; no single donor-to-recipient flux coefficient paid"
    "non-saturable, sodium/glucose-independent; interpreted as passive diffusion in the tested neural/PC12 systems"
    "Anastasiadis/Kuhn/Levine 1994"
    false

cacoQuantitativeTranscellularMeasurement : TransportMeasurement
cacoQuantitativeTranscellularMeasurement =
  transportMeasurement
    "2009 Caco-2 quantitative transcellular BH4 movement"
    "polarized Caco-2 Transwell epithelial monolayer"
    "BH4"
    "apical -> cell interior -> basolateral"
    "about 150 pmol/h per well at 100 micromol/L apical BH4"
    "benzbromarone-sensitive transporter-driven transcellular movement"
    "Ohashi et al. 2009 DOI 10.1007/s10545-008-0961-3"
    false

entTransportMeasurement : TransportMeasurement
entTransportMeasurement =
  transportMeasurement
    "2011 ENT pterin transport"
    "hENT1/hENT2 expression systems + HeLa/endothelial cells"
    "sepiapterin, BH2, BH4"
    "plasma-membrane pterin transport / salvage gateway"
    "relative efficiency SP > BH2 > BH4 for hENT2; no target-neural absolute donor-recipient rate paid"
    "ENT2 transporter-mediated, ENT1 weaker"
    "Ohashi et al. 2011 DOI 10.1016/j.ymgme.2010.09.005"
    false

oatTransportMeasurement : TransportMeasurement
oatTransportMeasurement =
  transportMeasurement
    "2017 OAT1/OAT3 biopterin transport"
    "rat kidney slices + OAT-expressing LLC-PK1/Xenopus systems"
    "BH4/BH2-related biopterins"
    "renal uptake/body-distribution and exclusion"
    "source-specific uptake/inhibition measurements; no neural donor-recipient rate paid"
    "OAT1/OAT3 probenecid-sensitive transport"
    "Ohashi et al. 2017 DOI 10.1007/s11010-017-3060-7"
    false

record IntercellularTransferEvidence : Set where
  constructor intercellularTransferEvidence
  field
    donorReleaseObserved : Bool
    donorReleaseObservedIsTrue : donorReleaseObserved ≡ true
    recipientUptakeObserved : Bool
    recipientUptakeObservedIsTrue : recipientUptakeObserved ≡ true
    cocultureFunctionalEffectObserved : Bool
    cocultureFunctionalEffectObservedIsTrue : cocultureFunctionalEffectObserved ≡ true
    epithelialTranscellularRateMeasured : Bool
    epithelialTranscellularRateMeasuredIsTrue : epithelialTranscellularRateMeasured ≡ true
    donorLabeledMolecularFluxIntoRecipientMeasured : Bool
    donorLabeledMolecularFluxIntoRecipientMeasuredIsFalse : donorLabeledMolecularFluxIntoRecipientMeasured ≡ false
    neuralInVivoTransferRateMeasured : Bool
    neuralInVivoTransferRateMeasuredIsFalse : neuralInVivoTransferRateMeasured ≡ false

open IntercellularTransferEvidence public

canonicalIntercellularTransferEvidence : IntercellularTransferEvidence
canonicalIntercellularTransferEvidence =
  intercellularTransferEvidence
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl

record TransportCarrierBoundary : Set where
  constructor transportCarrierBoundary
  field
    specificTransportersExistInSomeContexts : Bool
    specificTransportersExistInSomeContextsIsTrue : specificTransportersExistInSomeContexts ≡ true
    singleUniversalNeuralBH4CarrierEstablished : Bool
    singleUniversalNeuralBH4CarrierEstablishedIsFalse : singleUniversalNeuralBH4CarrierEstablished ≡ false
    neuralPassiveDiffusionResultUniversalizesToAllTissues : Bool
    neuralPassiveDiffusionResultUniversalizesToAllTissuesIsFalse :
      neuralPassiveDiffusionResultUniversalizesToAllTissues ≡ false
    transporterDependenceIsTissueSpeciesSubstrateSpecific : Bool
    transporterDependenceIsTissueSpeciesSubstrateSpecificIsTrue :
      transporterDependenceIsTissueSpeciesSubstrateSpecific ≡ true
    quantitativeTranscellularBH4RatePaid : Bool
    quantitativeTranscellularBH4RatePaidIsTrue : quantitativeTranscellularBH4RatePaid ≡ true
    quantitativeNeuralDonorRecipientFluxPaid : Bool
    quantitativeNeuralDonorRecipientFluxPaidIsFalse : quantitativeNeuralDonorRecipientFluxPaid ≡ false
    catecholaminergicBH4ReleaseObserved : Bool
    catecholaminergicBH4ReleaseObservedIsTrue : catecholaminergicBH4ReleaseObserved ≡ true
    recipientBH4UptakeObserved : Bool
    recipientBH4UptakeObservedIsTrue : recipientBH4UptakeObserved ≡ true
    functionalCocultureCrossTalkObserved : Bool
    functionalCocultureCrossTalkObservedIsTrue : functionalCocultureCrossTalkObserved ≡ true
    releaseUptakeCocultureSufficesForQuantitativeTransfer : Bool
    releaseUptakeCocultureSufficesForQuantitativeTransferIsFalse :
      releaseUptakeCocultureSufficesForQuantitativeTransfer ≡ false
    transportProbeClosesWholeAllocator : Bool
    transportProbeClosesWholeAllocatorIsFalse : transportProbeClosesWholeAllocator ≡ false

open TransportCarrierBoundary public

canonicalTransportCarrierBoundary : TransportCarrierBoundary
canonicalTransportCarrierBoundary =
  transportCarrierBoundary
    true refl
    false refl
    false refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Updated topology interpretation.
------------------------------------------------------------------------

record TransportTopologyUpgrade : Set where
  constructor transportTopologyUpgrade
  field
    priorTopology : Topology.TopologyResolvedPoolBalance
    carrierStateReference : String
    quantitativeTransportReference : String
    unresolvedNeuralFluxReference : String
    allocatorInterpretation : String

open TransportTopologyUpgrade public

canonicalTransportTopologyUpgrade : TransportTopologyUpgrade
canonicalTransportTopologyUpgrade =
  transportTopologyUpgrade
    Topology.canonicalTopologyResolvedPoolBalance
    "carrier mechanism is a node/edge attribute, not a global constant: passive-like neural/PC12 BH4 uptake coexists with ENT- and OAT-mediated pterin transport and transporter-sensitive epithelial BH4 translocation"
    "Caco-2 pays a context-specific transcellular BH4 rate (~150 pmol/h/well), proving that at least one topology edge can be numerically calibrated without paying the target neural donor-recipient edge"
    "acquire isotope/labeled-pterin donor->recipient time series in target-relevant neural coculture/organoid/in-vivo systems together with donor release, recipient intracellular BH4/BH2 and functional branch readouts"
    "adaptive allocator models must now specify which transport mechanism, substrate redox form, tissue/cell context and transfer edge carries supply; neither universal passive diffusion nor a universal dedicated carrier is admissible"
