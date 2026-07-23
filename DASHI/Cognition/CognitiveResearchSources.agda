module DASHI.Cognition.CognitiveResearchSources where

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Bibliographic receipts used by the cognition modules.
--
-- These values are documentation/authority receipts, not theorem inputs.
-- The mathematical modules prove finite structural statements; citations
-- identify the empirical or modelling work that motivates each interface.
------------------------------------------------------------------------

record ResearchSource : Set where
  constructor researchSource
  field
    authors : String
    year    : Nat
    title   : String
    venue   : String
    doi     : String
    archive : String

open ResearchSource public

-- Discrete and masked diffusion language modelling.  Conference/arXiv
-- sources without a registered DOI retain an empty DOI field.

austinDiscreteDiffusion : ResearchSource
austinDiscreteDiffusion = researchSource
  "Jacob Austin; Daniel D. Johnson; Jonathan Ho; Daniel Tarlow; Rianne van den Berg"
  2021
  "Structured Denoising Diffusion Models in Discrete State-Spaces"
  "NeurIPS 2021"
  ""
  "arXiv:2107.03006"

liDiffusionLM : ResearchSource
liDiffusionLM = researchSource
  "Xiang Lisa Li; John Thickstun; Ishaan Gulrajani; Percy Liang; Tatsunori B. Hashimoto"
  2022
  "Diffusion-LM Improves Controllable Text Generation"
  "NeurIPS 2022"
  ""
  "arXiv:2205.14217"

sahooMaskedDiffusionLM : ResearchSource
sahooMaskedDiffusionLM = researchSource
  "Subham Sekhar Sahoo; Marianne Arriola; Yair Schiff; Aaron Gokaslan; Edgar Marroquin; Justin T. Chiu; Alexander Rush; Volodymyr Kuleshov"
  2024
  "Simple and Effective Masked Diffusion Language Models"
  "NeurIPS 2024"
  ""
  "arXiv:2406.07524"

shiGeneralizedMaskedDiffusion : ResearchSource
shiGeneralizedMaskedDiffusion = researchSource
  "Jiaxin Shi; Kehang Han; Zhe Wang; Arnaud Doucet; Michalis K. Titsias"
  2024
  "Simplified and Generalized Masked Diffusion for Discrete Data"
  "NeurIPS 2024"
  ""
  "arXiv:2406.04329"

-- Connectivity and neurochemical communication.

fristonConnectivityReview : ResearchSource
fristonConnectivityReview = researchSource
  "Karl J. Friston"
  2011
  "Functional and Effective Connectivity: A Review"
  "Brain Connectivity 1(1):13-36"
  "10.1089/brain.2011.0008"
  "PMID:22432952"

friesCommunicationThroughCoherence : ResearchSource
friesCommunicationThroughCoherence = researchSource
  "Pascal Fries"
  2005
  "A mechanism for cognitive dynamics: neuronal communication through neuronal coherence"
  "Trends in Cognitive Sciences 9(10):474-480"
  "10.1016/j.tics.2005.08.011"
  "PMID:16150631"

fuxeWiredAndVolumeTransmission : ResearchSource
fuxeWiredAndVolumeTransmission = researchSource
  "Kjell Fuxe; Annica B. Dahlstrom; Gosta Jonsson; Daniel Marcellino; Michele Guescini; Mauro Dam; Paul Manger; Luigi Agnati"
  2010
  "The discovery of central monoamine neurons gave volume transmission to the wired brain"
  "Progress in Neurobiology 90(2):82-100"
  "10.1016/j.pneurobio.2009.10.012"
  "PMID:19853007"

borrotoEscuelaVolumeTransmission : ResearchSource
borrotoEscuelaVolumeTransmission = researchSource
  "Dasiel O. Borroto-Escuela; Luigi F. Agnati; Karl Bechter; Anders Jansson; Alexander O. Tarakanov; Kjell Fuxe"
  2015
  "The role of transmitter diffusion and flow versus extracellular vesicles in volume transmission in the brain neural-glial networks"
  "Philosophical Transactions of the Royal Society B 370:20140183"
  "10.1098/rstb.2014.0183"
  "PMID:26009762"

-- Psychedelic network dynamics and visual cortex.

carhartHarrisLSDNeuroimaging : ResearchSource
carhartHarrisLSDNeuroimaging = researchSource
  "Robin L. Carhart-Harris; Suresh Muthukumaraswamy; Leor Roseman; Mendel Kaelen; Wouter Droog; Kevin Murphy; Enzo Tagliazucchi; et al."
  2016
  "Neural correlates of the LSD experience revealed by multimodal neuroimaging"
  "Proceedings of the National Academy of Sciences 113(17):4853-4858"
  "10.1073/pnas.1518377113"
  "PMID:27071089"

luppiLSDIntegrationSegregation : ResearchSource
luppiLSDIntegrationSegregation = researchSource
  "Andrea I. Luppi; Robin L. Carhart-Harris; Leor Roseman; Ioannis Pappas; David K. Menon; Emmanuel A. Stamatakis"
  2021
  "LSD alters dynamic integration and segregation in the human brain"
  "NeuroImage 227:117653"
  "10.1016/j.neuroimage.2020.117653"
  "PMID:33338615"

singletonControlLandscape : ResearchSource
singletonControlLandscape = researchSource
  "S. Parker Singleton; Andrea I. Luppi; Robin L. Carhart-Harris; Josephine Cruzat; Leor Roseman; David J. Nutt; Gustavo Deco; Morten L. Kringelbach; Emmanuel A. Stamatakis; Amy Kuceyeski"
  2022
  "Receptor-informed network control theory links LSD and psilocybin to a flattening of the brain's control energy landscape"
  "Nature Communications 13:5812"
  "10.1038/s41467-022-33578-1"
  ""

girnMegaAnalysis : ResearchSource
girnMegaAnalysis = researchSource
  "Manesh Girn; Manoj K. Doss; Leor Roseman; Katrin H. Preller; Fernanda Palhano-Fontes; Lorenzo Pasquini; Frederick S. Barrett; et al."
  2026
  "An international mega-analysis of psychedelic drug effects on brain circuit function"
  "Nature Medicine 32:1543-1554"
  "10.1038/s41591-026-04287-9"
  "PMID:41942645"

-- Neural-field and contextuality foundations.

ermentroutCowanHallucinationPatterns : ResearchSource
ermentroutCowanHallucinationPatterns = researchSource
  "G. Bard Ermentrout; Jack D. Cowan"
  1979
  "A mathematical theory of visual hallucination patterns"
  "Biological Cybernetics 34:137-150"
  "10.1007/BF00336965"
  "PMID:486593"

bressloffGeometricHallucinations : ResearchSource
bressloffGeometricHallucinations = researchSource
  "Paul C. Bressloff; Jack D. Cowan; Martin Golubitsky; Peter J. Thomas; Matthew C. Wiener"
  2001
  "Geometric visual hallucinations, Euclidean symmetry and the functional architecture of striate cortex"
  "Philosophical Transactions of the Royal Society B 356:299-330"
  "10.1098/rstb.2000.0769"
  "PMCID:PMC1088430"

abramskyBrandenburgerContextuality : ResearchSource
abramskyBrandenburgerContextuality = researchSource
  "Samson Abramsky; Adam Brandenburger"
  2011
  "The sheaf-theoretic structure of non-locality and contextuality"
  "New Journal of Physics 13:113036"
  "10.1088/1367-2630/13/11/113036"
  "arXiv:1102.0264"

allCognitionSources : List ResearchSource
allCognitionSources =
  austinDiscreteDiffusion ∷
  liDiffusionLM ∷
  sahooMaskedDiffusionLM ∷
  shiGeneralizedMaskedDiffusion ∷
  fristonConnectivityReview ∷
  friesCommunicationThroughCoherence ∷
  fuxeWiredAndVolumeTransmission ∷
  borrotoEscuelaVolumeTransmission ∷
  carhartHarrisLSDNeuroimaging ∷
  luppiLSDIntegrationSegregation ∷
  singletonControlLandscape ∷
  girnMegaAnalysis ∷
  ermentroutCowanHallucinationPatterns ∷
  bressloffGeometricHallucinations ∷
  abramskyBrandenburgerContextuality ∷ []
