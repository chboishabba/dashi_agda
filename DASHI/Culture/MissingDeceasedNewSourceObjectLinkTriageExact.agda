module DASHI.Culture.MissingDeceasedNewSourceObjectLinkTriageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- NEW-SOURCE OBJECT-LINK TRIAGE
--
-- Sources supplied in the current investigation round are classified by the
-- role they can actually pay. Science adjacency and speculative synthesis do
-- not promote common-programme or targeting hypotheses.
------------------------------------------------------------------------

data SourceObjectRole : Set where
  primaryRetainedScience
  primaryRetainedApplicationObject
  primaryInstitutionalProgrammeObject
  retainedEventLead
  secondaryCaseAggregation
  nonRosterScienceControl
  speculativeSynthesis
  identityCollisionControl : SourceObjectRole

record SourceObjectReceipt : Set where
  constructor source-object-receipt
  field
    title : String
    role : SourceObjectRole
    retainedPerson : String
    objectOrIdentifier : String
    sourceReference : String
    sourceBackedDelta : String
    sameProgrammePaid : Bool
    operationalLinkPaid : Bool
    boundary : String

open SourceObjectReceipt public

rezaMondaloyPatentObject : SourceObjectReceipt
rezaMondaloyPatentObject = source-object-receipt
  "Burn-resistant and high tensile strength metal alloys"
  primaryRetainedScience
  "Monica Jacinto / Monica Reza"
  "US20100266442A1"
  "Google Patents; inventors Monica A. Jacinto and Dallis Ann Hardwick; priority 2001-09-18"
  "Pays a literal nickel-based burn-resistant/high-strength alloy object for oxygen-enriched rocket-engine structural applications, including preburner/turbomachinery motivation."
  false false
  "Patent identity pays Reza science/object identity, not McCasland participation, later programme custody, disappearance cause or targeting."

rezaHydrocarbonBoostApplicationObject : SourceObjectReceipt
rezaHydrocarbonBoostApplicationObject = source-object-receipt
  "AFRL Hydrocarbon Boost Mondaloy 200 preburner demonstration"
  primaryInstitutionalProgrammeObject
  "Monica Jacinto / Monica Reza science lineage"
  "Hydrocarbon Boost / Booster Propulsion Technology Maturation / Test Stand 2A"
  "U.S. Air Force / AFRL Propulsion Directorate, May 2016"
  "Pays downstream Mondaloy 200 application in an oxygen-rich staged-combustion preburner and a documented AFRL + Aerojet Rocketdyne technology-maturation programme lineage."
  false false
  "Downstream use of the alloy does not by itself identify the original inventor as participant in every later test and does not establish McCasland involvement."

maiwaldSURPObject : SourceObjectReceipt
maiwaldSURPObject = source-object-receipt
  "Unambiguous Detection of Biosignatures by Action Spectroscopy"
  primaryRetainedScience
  "Frank W. Maiwald"
  "FY23 SURP SP23012; RPC#sp23012; CL#23-5018"
  "NASA/JPL FY23 SURP poster"
  "Pays a literal JPL task/poster/clearance object with PI Maiwald, named co-investigators, cryogenic trap apparatus, IR photodissociation chain, and planetary life-detection application table."
  false false
  "A strong JPL object identifier does not create a Hicks same-project edge unless Hicks appears on the same task/instrument/work-package chain."

grillmairStreamScienceObject : SourceObjectReceipt
grillmairStreamScienceObject = source-object-receipt
  "At a Crossroads: Stellar Streams in the South Galactic Cap"
  primaryRetainedScience
  "Carl J. Grillmair"
  "DOI 10.3847/1538-4357/aa8872"
  "Astrophysical Journal 847(2):119; arXiv:1708.09029"
  "Pays a specific Pan-STARRS matched-filter/stellar-stream science object including Murrumbidgee, Molonglo, Orinoco and Kwando stream candidates."
  false false
  "Science object strengthens Grillmair's technical fibre only; it does not pay a shared programme with other retained scientists."

chenHardwareVerificationObject : SourceObjectReceipt
chenHardwareVerificationObject = source-object-receipt
  "Simulation-Based Hardware Verification with a Graph-Based Specification"
  primaryRetainedScience
  "Chen Shuming"
  "DOI 10.1155/2018/6398616"
  "Wiley/Hindawi 2018"
  "Pays Chen's graph-based hardware-verification science object independent of broader NUDT institutional history."
  false false
  "Publication co-location at NUDT does not identify the Galaxy/Feiteng object with Feng or Zhang Daibing programmes."

trinityClathrateControl : SourceObjectReceipt
trinityClathrateControl = source-object-receipt
  "Extreme nonequilibrium synthesis of a Ca-Cu-Si clathrate during the Trinity nuclear test"
  nonRosterScienceControl
  "none of retained twenty"
  "DOI 10.1073/pnas.2604165123; CCDC 2493087"
  "PNAS 2026"
  "Pays a real extreme-environment materials result: a crystallographically confirmed Ca-Cu-Si type-I clathrate in Trinity trinitite, with deposited crystallographic data."
  false false
  "A real nuclear-test material object is a useful extreme-materials/nuclear-forensics control; it does not link the retained scientists or establish exotic technology provenance."

wormholeTheoryControl : SourceObjectReceipt
wormholeTheoryControl = source-object-receipt
  "A new understanding of Einstein-Rosen bridges / wormhole commentary"
  nonRosterScienceControl
  "none of retained twenty"
  "DOI 10.1088/1361-6382/ae3044"
  "Classical and Quantum Gravity 2026; The Conversation/University of Portsmouth commentary"
  "Pays a theoretical reinterpretation of Einstein-Rosen bridges and explicitly states no observational evidence for macroscopic traversable wormholes."
  false false
  "Theoretical spacetime work does not create an engineering interface, propulsion device, roster link or disappearance cause."

chavezPoliceLead : SourceObjectReceipt
chavezPoliceLead = source-object-receipt
  "Anthony Chavez quantum-physics tip in police-file reporting"
  retainedEventLead
  "Anthony Chavez"
  "police-record tip: unidentified scientist / 'Quantum Physics' / matter in two places simultaneously"
  "Los Angeles Magazine reporting on obtained Los Alamos police records, 2026-06-28"
  "Pays an investigative lead that a friend reportedly told police Chavez had been working with an unidentified scientist on a quantum-physics topic."
  false false
  "A tip recorded by police is not proof the project existed, not identity of the scientist, not a LANL programme receipt, and not a cause of disappearance."

dbeConsultingIdentityCollision : SourceObjectReceipt
dbeConsultingIdentityCollision = source-object-receipt
  "DBE Consulting name collision"
  identityCollisionControl
  "William Neil McCasland / James Tegnelia"
  "DBE Consulting LLC / DBE Consulting"
  "Kirtland Partnership Committee McCasland profile; AFO Research James Tegnelia profile"
  "One public profile calls McCasland founder/owner/president of DBE Consulting, while another says James Tegnelia founded a DBE Consulting LLC in 2009. This nominates an entity-identity reconciliation problem."
  false false
  "Same business name does not establish same legal entity, partnership, ownership chain or common programme; registry/EIN/state filing identity is required."

primarySciencePaysCommonProgramme : Bool
primarySciencePaysCommonProgramme = false

secondaryEventAggregationPaysOperationalLink : Bool
secondaryEventAggregationPaysOperationalLink = false

sameBusinessNamePaysSameEntity : Bool
sameBusinessNamePaysSameEntity = false

nonRosterAdvancedSciencePaysRosterLink : Bool
nonRosterAdvancedSciencePaysRosterLink = false

speculativeSynthesisPaysMechanism : Bool
speculativeSynthesisPaysMechanism = false

rezaMondaloyApplicationChainPaid : Bool
rezaMondaloyApplicationChainPaid = true

rezaMcCaslandSameProgrammeStillPaid : Bool
rezaMcCaslandSameProgrammeStillPaid = false

maiwaldLiteralJPLTaskObjectPaid : Bool
maiwaldLiteralJPLTaskObjectPaid = true

maiwaldHicksSameTaskStillPaid : Bool
maiwaldHicksSameTaskStillPaid = false

nextHighestAlphaSourceObjectLeaf : String
nextHighestAlphaSourceObjectLeaf =
  "Use Mondaloy/Hydrocarbon Boost identifiers to search pre-2013 AFRL tasking and named participants; use SP23012/CL#23-5018/RPC#sp23012 to search JPL task ancestry and any Hicks overlap; reconcile DBE Consulting legal-entity identity before treating Tegnelia/McCasland as one consulting object; acquire primary Chavez police record before promoting the reported quantum-project tip."
