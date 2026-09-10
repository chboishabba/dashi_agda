module DASHI.Wikimedia.IbrahimEnglishPhoneticsPhonologyTraversalExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- IBRAHIM-STYLE CURRENT ENGLISH PHONETICS / PHONOLOGY TRAVERSAL PROBE
--
-- Method source:
-- Mark Ibrahim; Christopher M. Danforth; Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's First
-- Link Network", Journal of Computational Science 19 (2017), 21-30.
-- DOI: 10.1016/j.jocs.2016.12.001
--
-- Ibrahim et al. construct one outgoing edge per article from the first link
-- in the main body, then study paths, accumulation, cycles, depth and traversal
-- funnels. Their published graph is the November 2014 English snapshot.
--
-- This module does NOT rewrite that historical graph. It records current-EN
-- first-body-link probes observed 2026-09-10 as revision-sensitive navigation
-- priors for DASHI coverage auditing.
------------------------------------------------------------------------

data TraversalProbeStatus : Set where
  currentObservedHistoricalUnresolved : TraversalProbeStatus
  currentObservedDashiParentStrong : TraversalProbeStatus
  currentObservedDashiLeafMissing : TraversalProbeStatus

record CurrentEnglishFirstLinkProbe : Set where
  constructor current-english-first-link-probe
  field
    article : String
    firstBodyLink : String
    observationDate : String
    parserPolicy : String
    status : TraversalProbeStatus
    repositoryInterpretation : String
open CurrentEnglishFirstLinkProbe public

phoneticsToLinguistics : CurrentEnglishFirstLinkProbe
phoneticsToLinguistics =
  current-english-first-link-probe
    "Phonetics"
    "Linguistics"
    "2026-09-10"
    "main body; disambiguation/hatnote links excluded, matching Ibrahim-style intent"
    currentObservedDashiLeafMissing
    "Linguistics parent/use substrate exists, but focused repo search found no prior canonical phonetics/IPA feature owner before this tranche"

phonologyToLinguistics : CurrentEnglishFirstLinkProbe
phonologyToLinguistics =
  current-english-first-link-probe
    "Phonology"
    "Linguistics"
    "2026-09-10"
    "main body; maintenance/hatnote links excluded"
    currentObservedDashiLeafMissing
    "phoneme/language-specific contrast layer remains distinct from the new source-bound IPA phonetics lattice"

------------------------------------------------------------------------
-- Coverage consequence: both current probes converge immediately on the same
-- broad parent, so Ibrahim-style navigation identifies a compact sibling gap:
-- phonetics/IPA and phonology/phoneme contrast should share Linguistics as an
-- external navigation parent while remaining formally non-equivalent.
------------------------------------------------------------------------

record PhoneticsPhonologyCoverageQuotient : Set where
  constructor phonetics-phonology-coverage-quotient
  field
    sharedCurrentParent : String
    phoneticsSourceArchitecturePaid : Bool
    phoneticFeatureLatticePaid : Bool
    phonologyLanguageContrastOwnerPaid : Bool
    concreteLanguagePhonemeInventoryPaid : Bool
    currentTraversalCanPrioritiseMissingSibling : Bool
    currentTraversalEqualsIbrahim2014Edge : Bool
open PhoneticsPhonologyCoverageQuotient public

currentPhoneticsPhonologyCoverage : PhoneticsPhonologyCoverageQuotient
currentPhoneticsPhonologyCoverage =
  phonetics-phonology-coverage-quotient
    "Linguistics"
    true
    true
    false
    false
    true
    false

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data CurrentFirstLinkCreatesHistoricalEdge : Set where
data SharedFirstLinkParentCreatesSemanticEquivalence : Set where
data NavigationParentCreatesFormalDependency : Set where
data PhoneticsCreatesPhonology : Set where

currentProbeDoesNotBackdateHistoricalEdge : CurrentFirstLinkCreatesHistoricalEdge → ⊥
currentProbeDoesNotBackdateHistoricalEdge ()

sharedParentDoesNotMakeSiblingsEquivalent : SharedFirstLinkParentCreatesSemanticEquivalence → ⊥
sharedParentDoesNotMakeSiblingsEquivalent ()

navigationParentDoesNotCreateFormalDependency : NavigationParentCreatesFormalDependency → ⊥
navigationParentDoesNotCreateFormalDependency ()

phoneticsDoesNotCreatePhonology : PhoneticsCreatesPhonology → ⊥
phoneticsDoesNotCreatePhonology ()

record IbrahimPhoneticsPhonologyBoundary : Set where
  constructor ibrahim-phonetics-phonology-boundary
  field
    historicalMethodRetained : Bool
    currentRevisionExplicit : Bool
    hatnotesExcludedFromFirstBodyLink : Bool
    currentEdgesUsedAsNavigationPrior : Bool
    historicalIdentityNotAssumed : Bool
    sharedParentDoesNotCollapseSiblings : Bool
open IbrahimPhoneticsPhonologyBoundary public

canonicalIbrahimPhoneticsPhonologyBoundary : IbrahimPhoneticsPhonologyBoundary
canonicalIbrahimPhoneticsPhonologyBoundary =
  ibrahim-phonetics-phonology-boundary true true true true true true
