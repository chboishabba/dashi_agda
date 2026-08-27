module DASHI.Governance.EnvironmentalAuthoritySourceRegistryRound2Exact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Governance.IndigenousEnvironmentalJusticeSourceRegistryExact as Existing

------------------------------------------------------------------------
-- ROUND-TWO ENVIRONMENTAL / INDIGENOUS AUTHORITY SOURCES
--
-- This registry extends the existing source surface without changing the
-- authority of earlier entries.  Source class and bounded role are explicit;
-- a citation never promotes all claims made by an author or institution.
------------------------------------------------------------------------

SourceReference : Set
SourceReference = Existing.SourceReference

sourceReference :
  String → String → String → Nat → String → String → String → String → SourceReference
sourceReference = Existing.sourceReference

leahThomas2022 : SourceReference
leahThomas2022 = sourceReference
  "Leah Thomas"
  "The Intersectional Environmentalist: How to Dismantle Systems of Oppression to Protect People + Planet"
  "Voracious / Little, Brown and Company"
  2022
  "ISBN-13"
  "9780316279291"
  "authorial primary book / movement vocabulary source"
  "source for Thomas's intersectional-environmentalism framing and activist programme; not a controlled causal study or a replacement for Crenshaw's intersectionality scholarship"

goldmanCaceres2015 : SourceReference
goldmanCaceres2015 = sourceReference
  "Goldman Environmental Prize"
  "Berta Caceres: 2015 Goldman Environmental Prize recipient"
  "Goldman Environmental Prize"
  2015
  "institutional recipient record"
  "Goldman Environmental Prize 2015 Berta Caceres"
  "independent environmental institution record"
  "source for prize recognition and the documented campaign that pressured Sinohydro to withdraw from Agua Zarca; not judicial proof of every causal or responsibility claim"

globalWitness2025 : SourceReference
globalWitness2025 = sourceReference
  "Global Witness"
  "Roots of Resistance / Land and Environmental Defenders 2024 data"
  "Global Witness"
  2025
  "institutional annual-report series"
  "2253 defenders killed or disappeared 2012-2024; 146 cases in 2024"
  "systematic civil-society monitoring dataset"
  "source for a documented global pattern of lethal attacks/disappearances against land and environmental defenders; does not turn every recorded case into the same legal mechanism"

escazu2018 : SourceReference
escazu2018 = sourceReference
  "United Nations ECLAC / States of Latin America and the Caribbean"
  "Regional Agreement on Access to Information, Public Participation and Justice in Environmental Matters in Latin America and the Caribbean"
  "Escazu Agreement"
  2018
  "treaty"
  "Article 9"
  "regional environmental treaty"
  "source for party obligations to provide a safe enabling environment and appropriate effective timely measures to prevent investigate and punish attacks on environmental human-rights defenders"

iucnEscazuGap2025 : SourceReference
iucnEscazuGap2025 = sourceReference
  "IUCN Netherlands"
  "146 environmental and land defenders killed or disappeared in 2024"
  "IUCN NL"
  2025
  "institutional synthesis"
  "Escazu implementation gap note"
  "conservation-institution synthesis of Global Witness data"
  "source for the observation that almost 1000 defenders were murdered or disappeared in Latin America and the Caribbean after Escazu adoption; not a causal evaluation of treaty effect"

gruereSengupta2011 : SourceReference
gruereSengupta2011 = sourceReference
  "Guillaume Gruere and Debdatta Sengupta"
  "Bt Cotton and Farmer Suicides in India: An Evidence-based Assessment"
  "The Journal of Development Studies 47(2):316-337"
  2011
  "DOI"
  "10.1080/00220388.2010.492863"
  "peer-reviewed evidence review"
  "source against a naive direct/resurgence causal attribution of Indian farmer suicide to Bt cotton while retaining context-specific indirect possibilities"

natureGMCrops2013 : SourceReference
natureGMCrops2013 = sourceReference
  "Natasha Gilbert"
  "Case studies: A hard look at GM crops"
  "Nature 497:24-26"
  2013
  "DOI"
  "10.1038/497024a"
  "scientific news feature / evidence synthesis"
  "secondary corroborating source surveying Bt-cotton suicide evidence; not a primary epidemiological study"

unescoBudjBim2019 : SourceReference
unescoBudjBim2019 = sourceReference
  "UNESCO World Heritage Committee"
  "Budj Bim Cultural Landscape"
  "World Heritage List 1577"
  2019
  "World Heritage property"
  "1577"
  "international institutional heritage assessment"
  "source for Gunditjmara deliberate hydrological engineering, extensive kooyang aquaculture, at least 6600 years of management, continuing knowledge, and six-millennia economic/social base"

mithakaAntiquity2021 : SourceReference
mithakaAntiquity2021 = sourceReference
  "Michael Westaway et al. with Mithaka Aboriginal Corporation authors"
  "Hidden in plain sight: the archaeological landscape of Mithaka Country, south-west Queensland"
  "Antiquity"
  2021
  "stable journal article"
  "Cambridge Core 9661E7F90EB7ED535012484DC35FB01A"
  "peer-reviewed collaborative Mithaka-initiated archaeological research"
  "source for numerous large quarries, grindstone production, substantial dwellings and intensive regional economic practices; does not settle continent-wide agriculture terminology or all village-settlement claims"

record Round2SourceBoundary : Set where
  constructor round2SourceBoundary
  field
    prizeRecognitionEqualsJudicialFinding : Bool
    prizeRecognitionEqualsJudicialFindingIsFalse : prizeRecognitionEqualsJudicialFinding ≡ false
    treatyTextEqualsEffectiveImplementation : Bool
    treatyTextEqualsEffectiveImplementationIsFalse : treatyTextEqualsEffectiveImplementation ≡ false
    validatedLocalPracticeEqualsContinentWideGeneralization : Bool
    validatedLocalPracticeEqualsContinentWideGeneralizationIsFalse : validatedLocalPracticeEqualsContinentWideGeneralization ≡ false
    authorialFrameworkEqualsEmpiricalCausalLaw : Bool
    authorialFrameworkEqualsEmpiricalCausalLawIsFalse : authorialFrameworkEqualsEmpiricalCausalLaw ≡ false

canonicalRound2SourceBoundary : Round2SourceBoundary
canonicalRound2SourceBoundary = round2SourceBoundary false refl false refl false refl false refl
