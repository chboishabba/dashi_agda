module DASHI.Biology.Protein.AlliumThiolSituatedProteinWitnessExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Biology.Protein.ProteinSituatedHyperfabricExact as Situated
import DASHI.Biology.Protein.AlliumThiolProteinInteractionExact as Allium
import DASHI.Biology.Protein.AlliumThiolSourceAttributionEnvelopeExact as Source

------------------------------------------------------------------------
-- ALLIUM / ALLICIN THIRD SITUATED-PROTEIN WITNESS
--
-- The existing Allium protein-thiol owner and its literature anchors distinguish
-- accessible cysteine thiols from merely present/inaccessible cysteine sites.
-- The finite carrier below is DASHI synthesis of that information-loss shape:
-- cysteine presence alone is too coarse for the declared modification query.
--
-- No paper is attributed with this generic FactorsThrough theorem, and no
-- finite witness is promoted to a universal cysteine-reactivity law.
------------------------------------------------------------------------

data ThiolWorld : Set where
  accessibleCysteineWorld : ThiolWorld
  inaccessibleCysteineWorld : ThiolWorld

data CysteinePresenceObservation : Set where
  cysteinePresent : CysteinePresenceObservation

data ThiolModificationQuery : Set where
  allicinModificationQuery : ThiolModificationQuery

data ThiolModificationAnswer : Set where
  modificationCompatible : ThiolModificationAnswer
  modificationBlockedByAccessibility : ThiolModificationAnswer

cysteinePresenceProjection : ThiolWorld → CysteinePresenceObservation
cysteinePresenceProjection accessibleCysteineWorld = cysteinePresent
cysteinePresenceProjection inaccessibleCysteineWorld = cysteinePresent

modificationAnswer :
  ThiolModificationQuery → ThiolWorld → ThiolModificationAnswer
modificationAnswer allicinModificationQuery accessibleCysteineWorld =
  modificationCompatible
modificationAnswer allicinModificationQuery inaccessibleCysteineWorld =
  modificationBlockedByAccessibility

modificationSemantics :
  Query.QuerySemantics ThiolWorld ThiolModificationQuery ThiolModificationAnswer
modificationSemantics = Query.querySemantics modificationAnswer

cysteinePresenceDefect :
  Query.QueryAdequacyDefect
    cysteinePresenceProjection
    modificationSemantics
    allicinModificationQuery
cysteinePresenceDefect =
  Query.queryAdequacyDefect
    accessibleCysteineWorld
    inaccessibleCysteineWorld
    refl
    (λ ())

alliumSituatedQueryWitness : Situated.SituatedProteinQueryWitness
alliumSituatedQueryWitness = Situated.situated-protein-query-witness
  ThiolWorld
  CysteinePresenceObservation
  ThiolModificationQuery
  ThiolModificationAnswer
  cysteinePresenceProjection
  modificationSemantics
  allicinModificationQuery
  cysteinePresenceDefect
  Situated.contextual
  "cysteine presence is retained in both worlds while solvent accessibility/local thiol context separates modification compatibility"
  "Rabinkov 1998 and Borlinghaus 2014/2021 retain the source-bounded thiol-protein chemistry/accessibility premises; DOI/PMID/PMCID identities remain provenance only and article QIDs remain unresolved unless verified"
  "DASHI owns the finite collision, query-indexed non-factorability theorem and situated-protein instantiation"

cysteinePresenceNotAdequateForModificationQuery :
  Query.AdequateFor
    cysteinePresenceProjection
    modificationSemantics
    allicinModificationQuery →
  ⊥
cysteinePresenceNotAdequateForModificationQuery =
  Situated.witnessBlocksCoarseAdequacy alliumSituatedQueryWitness

------------------------------------------------------------------------
-- Constructive repair: retain accessibility/local context.
------------------------------------------------------------------------

data AccessibilityState : Set where
  accessibleSite : AccessibilityState
  inaccessibleSite : AccessibilityState

record AccessibilityAwareObservation : Set where
  constructor accessibility-aware-observation
  field
    cysteine : CysteinePresenceObservation
    accessibility : AccessibilityState
    localContext : String
open AccessibilityAwareObservation public

accessibilityAwareProjection : ThiolWorld → AccessibilityAwareObservation
accessibilityAwareProjection accessibleCysteineWorld =
  accessibility-aware-observation
    cysteinePresent accessibleSite
    "accessible cysteine thiol in an allicin-exposed local chemical context"
accessibilityAwareProjection inaccessibleCysteineWorld =
  accessibility-aware-observation
    cysteinePresent inaccessibleSite
    "cysteine present but inaccessible to the declared allicin modification event"

answerFromAccessibility : AccessibilityAwareObservation → ThiolModificationAnswer
answerFromAccessibility
  (accessibility-aware-observation cysteinePresent accessibleSite context) =
  modificationCompatible
answerFromAccessibility
  (accessibility-aware-observation cysteinePresent inaccessibleSite context) =
  modificationBlockedByAccessibility

accessibilityAwareRepair :
  Query.AdequateFor
    accessibilityAwareProjection
    modificationSemantics
    allicinModificationQuery
accessibilityAwareRepair =
  Query.factorsForQuery
    answerFromAccessibility
    (λ { accessibleCysteineWorld → refl ; inaccessibleCysteineWorld → refl })

------------------------------------------------------------------------
-- Source/identity donors and authority boundaries.
------------------------------------------------------------------------

thiolInteractionBoundary = Allium.canonicalThiolProteinBoundary
sourceAttributionBoundary = Source.canonicalAlliumThiolSourceAttributionBoundary

attributionRule : String
attributionRule =
  "The Allium literature owns only its source-bounded allicin/thiol-protein accessibility and chemistry propositions. The finite accessible/inaccessible collision, query-indexed defect and repair are DASHI synthesis. DOI/PMID/PMCID/QID identify sources only; they do not create modification outcomes or cross-protein mechanisms."

------------------------------------------------------------------------
-- Cross-domain firewalls.
------------------------------------------------------------------------

data AlliumWitnessCreatesTRPA1ThermalMechanism : Set where
data AlliumWitnessCreatesAdKRateKernel : Set where
data SourceIdentifiersCreateModification : Set where
data CysteinePresenceCreatesUniversalModificationLaw : Set where
data CrossDomainMechanismTransfer : Set where

alliumDoesNotCreateTRPA1ThermalMechanism :
  AlliumWitnessCreatesTRPA1ThermalMechanism → ⊥
alliumDoesNotCreateTRPA1ThermalMechanism ()

alliumDoesNotCreateAdKRateKernel : AlliumWitnessCreatesAdKRateKernel → ⊥
alliumDoesNotCreateAdKRateKernel ()

sourceIdentifiersDoNotCreateModification : SourceIdentifiersCreateModification → ⊥
sourceIdentifiersDoNotCreateModification ()

cysteinePresenceDoesNotCreateUniversalModificationLaw :
  CysteinePresenceCreatesUniversalModificationLaw → ⊥
cysteinePresenceDoesNotCreateUniversalModificationLaw ()

crossDomainMechanismDoesNotTransfer : CrossDomainMechanismTransfer → ⊥
crossDomainMechanismDoesNotTransfer ()

record AlliumThiolSituatedBoundary : Set where
  constructor allium-thiol-situated-boundary
  field
    usesGenericSituatedWitness : Bool
    cysteinePresenceProjectionInadequate : Bool
    accessibilityAwareRepairRetained : Bool
    alliumSourceRoleRetained : Bool
    doiPmidPmcidRetainedAsProvenance : Bool
    articleQidMayRemainUnresolved : Bool
    sourceIdentifiersCreateModification : Bool
    cysteinePresenceCreatesUniversalModificationLaw : Bool
    crossDomainMechanismTransfer : Bool
open AlliumThiolSituatedBoundary public

canonicalAlliumThiolSituatedBoundary : AlliumThiolSituatedBoundary
canonicalAlliumThiolSituatedBoundary = allium-thiol-situated-boundary
  true true true true true true
  false false false
