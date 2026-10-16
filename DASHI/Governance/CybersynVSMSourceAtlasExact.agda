module DASHI.Governance.CybersynVSMSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID

------------------------------------------------------------------------
-- CYBERSYN / VIABLE SYSTEM MODEL SOURCE ATLAS
--
-- Source propositions remain source-owned. DASHI owns only the typed source
-- roles and the non-promotion boundaries below.
------------------------------------------------------------------------

data CyberneticSourceRole : Set where
  beerVSMPrimary : CyberneticSourceRole
  beerBookSourceLineage : CyberneticSourceRole
  cybersynHistoricalReconstruction : CyberneticSourceRole
  contemporaryCriticalSynthesis : CyberneticSourceRole

record CyberneticSource : Set where
  constructor cybernetic-source
  field
    author : String
    title : String
    venue : String
    year : Nat
    identifier : String
    role : CyberneticSourceRole
    sourceSupports : String
    sourceDoesNotByItselfSupport : String

open CyberneticSource public

beer1984VSM : CyberneticSource
beer1984VSM =
  cybernetic-source
    "Stafford Beer"
    "The Viable System Model: Its Provenance, Development, Methodology and Pathology"
    "Journal of the Operational Research Society 35(1):7-25"
    1984
    "doi:10.1057/jors.1984.2"
    beerVSMPrimary
    "Beer's own synopsis of the Viable System Model, its methodology and five-system viability framework"
    "political legitimacy, empirical superiority of one political order, or a theorem that VSM implementation guarantees non-domination"

beerBooks : CyberneticSource
beerBooks =
  cybernetic-source
    "Stafford Beer"
    "Brain of the Firm; The Heart of Enterprise; Diagnosing the System for Organizations"
    "book lineage"
    1972
    "1972/1979/1985 VSM book lineage"
    beerBookSourceLineage
    "the historical development of recursive viable-system diagnosis, autonomy/coordination/control, outside-and-future intelligence and identity/policy functions"
    "a unique constitutional interpretation of Systems 1-5 or a proof that System 5 should be a sovereign executive"

medinaCybersyn : CyberneticSource
medinaCybersyn =
  cybernetic-source
    "Eden Medina"
    "Cybernetic Revolutionaries: Technology and Politics in Allende's Chile"
    "MIT Press"
    2011
    "historical monograph; Project Cybersyn archival reconstruction"
    cybersynHistoricalReconstruction
    "historical reconstruction of Project Cybersyn's telex network, Cyberstride statistical processing, CHECO modelling, operations room, institutional context and incomplete/prototypical implementation"
    "a claim that every planned Cybersyn component was fully deployed, politically neutral, or sufficient for democratic/non-dominating governance"

contemporaryCybersynCritical : CyberneticSource
contemporaryCybersynCritical =
  cybernetic-source
    "contemporary Cybersyn/VSM scholarship"
    "Designing freedom: Allende, Pinochet and the twin experiments in cyber-socialism and neoliberalism"
    "Economy and Society"
    2025
    "doi:10.1080/03085147.2025.2513800"
    contemporaryCriticalSynthesis
    "a recent critical account of Cybersyn's layered VSM organisation, four sub-projects and political-economic context"
    "a primary-source replacement, a universal evaluation of socialism, or proof that vertical VSM layers are identical to legitimate authority"

canonicalCyberneticSources : List CyberneticSource
canonicalCyberneticSources =
  beer1984VSM
  ∷ beerBooks
  ∷ medinaCybersyn
  ∷ contemporaryCybersynCritical
  ∷ []

------------------------------------------------------------------------
-- POSIWID is already source-bounded elsewhere; retain that exact owner rather
-- than restating the heuristic as a DASHI-authored proposition.
------------------------------------------------------------------------

posiwidSourceAnchor : POSIWID.POSIWIDSourceBoundary
posiwidSourceAnchor = POSIWID.canonicalPOSIWIDSourceBoundary

record CybersynVSMSourceBoundary : Set where
  constructor cybersyn-vsm-source-boundary
  field
    vsmFiveSystemSourcePresent : Bool
    recursiveViabilitySourcePresent : Bool
    autonomyCoordinationTensionSourcePresent : Bool
    outsideFutureIntelligenceSourcePresent : Bool
    identityPolicyFunctionSourcePresent : Bool
    cybersynOperationalComponentsSourcePresent : Bool
    cybersynIncompletePrototypeBoundaryPresent : Bool
    posiwidObservedOperationBoundaryPresent : Bool

    vsmCreatesPoliticalLegitimacy : Bool
    vsmCreatesNonDomination : Bool
    systemFiveMeansSovereignExecutive : Bool
    cybersynWasFullyImplemented : Bool
    cyberstrideObservationCreatesActionAuthority : Bool
    declaredSocialistPurposeProvesRealizedEgalitarianEffect : Bool
    contemporarySynthesisReplacesPrimaryHistory : Bool

open CybersynVSMSourceBoundary public

canonicalCybersynVSMSourceBoundary : CybersynVSMSourceBoundary
canonicalCybersynVSMSourceBoundary =
  cybersyn-vsm-source-boundary
    true true true true true true true true
    false false false false false false false

canonicalCybersynVSMSourceReceipt : GenericReceipt.GenericReceipt
canonicalCybersynVSMSourceReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Cybersyn / VSM source atlas"
    "DASHI.Governance.CybersynVSMSourceAtlasExact"
    "canonicalCybersynVSMSourceBoundary"
    "retains Beer's primary VSM lineage, Medina's archival Cybersyn reconstruction, a recent critical synthesis and the existing POSIWID source boundary as separately owned propositions"
    "VSM structure does not itself create legitimacy or non-domination; System 5 is not promoted to sovereign authority; Cybersyn is not represented as fully implemented; observation/forecasting does not automatically authorise intervention"
    "agda -i . DASHI/Governance/DeliberativeViableNonDominationLoopRegression.agda"
