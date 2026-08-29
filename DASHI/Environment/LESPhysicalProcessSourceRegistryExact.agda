module DASHI.Environment.LESPhysicalProcessSourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- TYPED SOURCE REGISTRY FOR THE LES PHYSICAL / BIOGEOCHEMICAL TRANCHE
--
-- Repository policy requires external-source claims to remain distinguishable
-- from DASHI reconstruction, cross-module inference and promotion.  This file
-- centralises the source identities that are structurally reused across the
-- SI, U(1)/PNP, root/fungal, soil C/N, whole-plant and SPAC modules.
------------------------------------------------------------------------

data SourceKind : Set where
  standard journalArticle scholarlyBook : SourceKind

data SourceRole : Set where
  siMetrology
  electrodiffusionArchitecture
  rootWaterArchitecture
  rootNutrientArchitecture
  mycorrhizalNutritionArchitecture
  soilCNArchitecture
  xylemHydraulicArchitecture
  c3PhotosynthesisArchitecture
  stomatalWaterEconomyArchitecture
  spacArchitecture
  unsaturatedFlowEquation
  unsaturatedConductivityModel
  soilRetentionConductivityModel
  stomatalConductanceModel
  : SourceRole

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifier : String
    kind : SourceKind
    role : SourceRole
    boundedReading : String
    excludedPromotion : String

open SourceReference public

bipmSI : SourceReference
bipmSI = sourceReference
  "Bureau International des Poids et Mesures"
  "The International System of Units (SI), 9th edition; revision 4.01"
  "BIPM"
  2026
  "DOI 10.59161/AUEZ1291"
  standard siMetrology
  "Authority for SI base quantities, units and derived-unit relations reused by DASHI.Physics.Units.SI."
  "Does not supply DASHI's type-indexed Agda representation or any LES constitutive law."

jasielec2021 : SourceReference
jasielec2021 = sourceReference
  "Jerzy J. Jasielec"
  "Electrodiffusion Phenomena in Neuroscience and the Nernst-Planck-Poisson Equations"
  "Electrochem 2(2), 197-215"
  2021
  "DOI 10.3390/electrochem2020014"
  journalArticle electrodiffusionArchitecture
  "Source calibration for coupled Nernst-Planck / Poisson electrodiffusion and its neuroscience application context."
  "Does not state DASHI's generic cross-domain application socket, same-object charge-density weld or Stage-7 promotion rules."

steudle2000 : SourceReference
steudle2000 = sourceReference
  "Ernst Steudle"
  "Water uptake by plant roots: an integration of views"
  "Plant and Soil 226, 45-56"
  2000
  "DOI 10.1023/A:1026439226716"
  journalArticle rootWaterArchitecture
  "Source calibration for composite root-water transport and root hydraulic properties."
  "Does not provide a universal root hydraulic parameterisation or DASHI's SI/state-weld architecture."

barberonGeldner2014 : SourceReference
barberonGeldner2014 = sourceReference
  "Marie Barberon and Niko Geldner"
  "Radial transport of nutrients: the plant root as a polarized epithelium"
  "Plant Physiology 166(2), 528-537"
  2014
  "DOI 10.1104/pp.114.246124"
  journalArticle rootNutrientArchitecture
  "Source calibration for apoplastic, symplastic and trans-cellular nutrient routes and endodermal barrier structure."
  "Does not identify a universal transporter set, ion parameterisation or PNP boundary condition."

smithSmith2011 : SourceReference
smithSmith2011 = sourceReference
  "Sally E. Smith and F. Andrew Smith"
  "Roles of Arbuscular Mycorrhizas in Plant Nutrition and Growth: New Paradigms from Cellular to Ecosystem Scales"
  "Annual Review of Plant Biology 62, 227-250"
  2011
  "DOI 10.1146/annurev-arplant-042110-103846"
  journalArticle mycorrhizalNutritionArchitecture
  "Source calibration for distinct direct-root and arbuscular-mycorrhizal nutrient-acquisition pathways and their interaction."
  "Does not imply that compatibility proves nutrient benefit or that one fungal parameterisation transfers among hosts and soils."

manzoniPorporato2009 : SourceReference
manzoniPorporato2009 = sourceReference
  "Stefano Manzoni and Amilcare Porporato"
  "Soil carbon and nitrogen mineralization: Theory and models across scales"
  "Soil Biology and Biochemistry 41(7), 1355-1379"
  2009
  "DOI 10.1016/j.soilbio.2009.02.031"
  journalArticle soilCNArchitecture
  "Source calibration for soil C/N decomposition, microbial assimilation, mineralisation, immobilisation, respiration and scale-sensitive modelling."
  "Does not choose one universal pool structure, kinetic law or cross-scale parameterisation."

tyreeZimmermann2002 : SourceReference
tyreeZimmermann2002 = sourceReference
  "Melvin T. Tyree and Martin H. Zimmermann"
  "Xylem Structure and the Ascent of Sap, 2nd edition"
  "Springer"
  2002
  "DOI 10.1007/978-3-662-04931-0"
  scholarlyBook xylemHydraulicArchitecture
  "Source calibration for xylem hydraulic architecture, cohesion-tension transport, conductance, storage and hydraulic failure concepts."
  "Does not provide a universal species-level vulnerability, capacitance or whole-plant calibration."

farquharVonCaemmererBerry1980 : SourceReference
farquharVonCaemmererBerry1980 = sourceReference
  "G. D. Farquhar, S. von Caemmerer and J. A. Berry"
  "A biochemical model of photosynthetic CO2 assimilation in leaves of C3 species"
  "Planta 149, 78-90"
  1980
  "DOI 10.1007/BF00386231"
  journalArticle c3PhotosynthesisArchitecture
  "Source calibration for the C3 biochemical assimilation model."
  "Does not define universal photosynthesis across C3/C4/CAM plants or DASHI's cross-domain coupling architecture."

buckleySackFarquhar2017 : SourceReference
buckleySackFarquhar2017 = sourceReference
  "Thomas N. Buckley, Lawren Sack and Graham D. Farquhar"
  "Optimal plant water economy"
  "Plant, Cell & Environment 40, 881-896"
  2017
  "DOI 10.1111/pce.12823"
  journalArticle stomatalWaterEconomyArchitecture
  "Source calibration for coupled carbon gain, water loss and stomatal water-economy reasoning."
  "Does not establish one universal stomatal dynamic law or parameterisation."

sperryStillerHacke2003 : SourceReference
sperryStillerHacke2003 = sourceReference
  "John S. Sperry, Volker Stiller and Uwe G. Hacke"
  "Xylem Hydraulics and the Soil-Plant-Atmosphere Continuum: Opportunities and Unresolved Issues"
  "Agronomy Journal 95(6), 1362-1370"
  2003
  "DOI 10.2134/agronj2003.1362"
  journalArticle spacArchitecture
  "Source calibration for mechanistic linking of soil hydraulic availability, xylem vulnerability, stomatal regulation and canopy water use."
  "Does not identify soil conductivity with xylem vulnerability or eliminate storage, hysteresis and calibration requirements."

richards1931 : SourceReference
richards1931 = sourceReference
  "L. A. Richards"
  "Capillary Conduction of Liquids Through Porous Mediums"
  "Physics 1(5), 318-333"
  1931
  "DOI 10.1063/1.1745010"
  journalArticle unsaturatedFlowEquation
  "Source calibration for gravity/pressure-gradient driven unsaturated porous-medium flow using a Darcy-law conductivity and storage relation."
  "Does not imply that every LES hydrological compartment satisfies the same reduction, parameters or boundary conditions."

mualem1976 : SourceReference
mualem1976 = sourceReference
  "Yechezkel Mualem"
  "A new model for predicting the hydraulic conductivity of unsaturated porous media"
  "Water Resources Research 12(3), 513-522"
  1976
  "DOI 10.1029/WR012i003p00513"
  journalArticle unsaturatedConductivityModel
  "Source calibration for predicting unsaturated hydraulic conductivity from moisture-content/capillary-head information and saturated conductivity."
  "Does not make the Mualem parameterisation universal or remove calibration/validation obligations."

vanGenuchten1980 : SourceReference
vanGenuchten1980 = sourceReference
  "M. Th. van Genuchten"
  "A Closed-form Equation for Predicting the Hydraulic Conductivity of Unsaturated Soils"
  "Soil Science Society of America Journal 44(5), 892-898"
  1980
  "DOI 10.2136/sssaj1980.03615995004400050002x"
  journalArticle soilRetentionConductivityModel
  "Source calibration for a soil-water retention relation yielding closed-form relative-conductivity expressions when combined with predictive conductivity models such as Mualem's."
  "Does not license parameter transfer between soils or equate fitted retention with independently validated conductivity."

medlynEtAl2011 : SourceReference
medlynEtAl2011 = sourceReference
  "Belinda E. Medlyn, Remko A. Duursma, Derek Eamus, David S. Ellsworth, I. Colin Prentice, Craig V. M. Barton, Kristine Y. Crous, Paolo de Angelis, Michael Freeman and Lisa Wingate"
  "Reconciling the optimal and empirical approaches to modelling stomatal conductance"
  "Global Change Biology 17(6), 2134-2144"
  2011
  "DOI 10.1111/j.1365-2486.2010.02375.x"
  journalArticle stomatalConductanceModel
  "Source calibration for an optimality-motivated stomatal conductance model related to assimilation and atmospheric demand."
  "Does not make one parameter set universal across species, climates or experimental conditions."

lesPhysicalProcessSources : List SourceReference
lesPhysicalProcessSources =
  bipmSI ∷ jasielec2021 ∷ steudle2000 ∷ barberonGeldner2014 ∷
  smithSmith2011 ∷ manzoniPorporato2009 ∷ tyreeZimmermann2002 ∷
  farquharVonCaemmererBerry1980 ∷ buckleySackFarquhar2017 ∷
  sperryStillerHacke2003 ∷ richards1931 ∷ mualem1976 ∷
  vanGenuchten1980 ∷ medlynEtAl2011 ∷ []

record LESPhysicalProcessAttributionBoundary : Set where
  constructor lesPhysicalProcessAttributionBoundary
  field
    externalSourceIsDASHIFormalProof : Bool
    externalSourceIsDASHIFormalProofIsFalse : externalSourceIsDASHIFormalProof ≡ false
    sourceModelIsUniversalApplicationParameterisation : Bool
    sourceModelIsUniversalApplicationParameterisationIsFalse : sourceModelIsUniversalApplicationParameterisation ≡ false
    typedReconstructionIsExternalPromotion : Bool
    typedReconstructionIsExternalPromotionIsFalse : typedReconstructionIsExternalPromotion ≡ false
    typedRegistryMakesClaimBoundaryExplicit : Bool
    typedRegistryMakesClaimBoundaryExplicitIsTrue : typedRegistryMakesClaimBoundaryExplicit ≡ true

canonicalLESPhysicalProcessAttributionBoundary : LESPhysicalProcessAttributionBoundary
canonicalLESPhysicalProcessAttributionBoundary =
  lesPhysicalProcessAttributionBoundary false refl false refl false refl true refl
