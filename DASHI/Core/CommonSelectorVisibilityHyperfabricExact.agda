module DASHI.Core.CommonSelectorVisibilityHyperfabricExact where

------------------------------------------------------------------------
-- COMMON-SELECTOR / VISIBILITY HYPERFABRIC
--
-- A set of people need not know one another or share one programme in order to
-- be jointly visible to some observer/selector.  Visibility, selection, common
-- selector, and common adversary are kept as distinct theorem layers.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.ScientificSourceCitationExact as Citation

------------------------------------------------------------------------
-- Visibility coordinates.
------------------------------------------------------------------------

data VisibilityAxis : Set where
  publicScientificWork
  publicInstitutionalRole
  programmeOrContractVisibility
  personnelSystemVisibility
  facilityAccessVisibility
  securityOrClearanceVisibility
  professionalNetworkVisibility
  conferenceOrPublicationVisibility
  publicMediaVisibility
  unresolvedVisibilityAxis
  : VisibilityAxis

data VisibilityStrength : Set where
  primaryPublicReceipt
  primaryInstitutionalReceipt
  primaryProgrammeReceipt
  boundedSecondaryReceipt
  unresolvedReceipt
  : VisibilityStrength

record VisibilityReceipt : Set where
  constructor visibility-receipt
  field
    personName : String
    axis : VisibilityAxis
    visibleObject : String
    strength : VisibilityStrength
    source : Citation.ScientificCitation
    boundedReading : String

open VisibilityReceipt public

------------------------------------------------------------------------
-- Selector candidates.
------------------------------------------------------------------------

data SelectorClass : Set where
  publicInternetObserver
  institutionalPersonnelObserver
  programmeManagementObserver
  contractorOrProcurementObserver
  facilityAccessObserver
  securityAdministrationObserver
  professionalNetworkObserver
  intelligenceCollectionObserver
  unresolvedSelectorClass
  : SelectorClass

record SelectorCapability : Set where
  constructor selector-capability
  field
    selectorClass : SelectorClass
    Sees : VisibilityReceipt → Set
    capabilityReference : String

open SelectorCapability public

record PersonVisibleTo
    (selector : SelectorCapability)
    (receipt : VisibilityReceipt) : Set where
  constructor person-visible-to
  field
    seen : Sees selector receipt

open PersonVisibleTo public

------------------------------------------------------------------------
-- Common selector is existential over one selector capability.  It does NOT
-- mean the selector selected, targeted, harmed, or even noticed the people.
------------------------------------------------------------------------

record CommonVisibilityPair
    (left right : VisibilityReceipt) : Set₁ where
  constructor common-visibility-pair
  field
    selector : SelectorCapability
    leftVisible : PersonVisibleTo selector left
    rightVisible : PersonVisibleTo selector right
    commonVisibilityReference : String

open CommonVisibilityPair public

------------------------------------------------------------------------
-- Selection is a stronger object than visibility.
------------------------------------------------------------------------

record SelectorPredicate
    (selector : SelectorCapability) : Set₁ where
  constructor selector-predicate
  field
    Selected : VisibilityReceipt → Set
    predicateReference : String

open SelectorPredicate public

record CommonSelectionPair
    {selector : SelectorCapability}
    (predicate : SelectorPredicate selector)
    (left right : VisibilityReceipt) : Set where
  constructor common-selection-pair
  field
    leftSelected : Selected predicate left
    rightSelected : Selected predicate right

open CommonSelectionPair public

------------------------------------------------------------------------
-- Minimality is source-relative: among declared source-backed selector models,
-- choose one whose observed axes are no finer than required to retain the
-- roster members.  This is not a probability or causality claim.
------------------------------------------------------------------------

record SourceBackedSelectorCandidate : Set₁ where
  constructor source-backed-selector-candidate
  field
    selector : SelectorCapability
    observedAxes : List VisibilityAxis
    supportReference : String

open SourceBackedSelectorCandidate public

record MinimalCommonSelector
    (RosterReceipt : Set)
    (receiptOf : RosterReceipt → VisibilityReceipt)
    (Declared : SourceBackedSelectorCandidate → Set) : Set₁ where
  constructor minimal-common-selector
  field
    selected : SourceBackedSelectorCandidate
    selectedDeclared : Declared selected
    seesRoster :
      (r : RosterReceipt) →
      PersonVisibleTo (selector selected) (receiptOf r)
    noDeclaredProperlyCoarserWitness :
      (alternative : SourceBackedSelectorCandidate) →
      Declared alternative →
      ((r : RosterReceipt) →
       PersonVisibleTo (selector alternative) (receiptOf r)) →
      Set
    minimalityReference : String

------------------------------------------------------------------------
-- Critical firewalls.
------------------------------------------------------------------------

record CommonSelectorBoundary : Set where
  constructor common-selector-boundary
  field
    peopleMustKnowEachOtherForCommonVisibility : Bool
    peopleMustKnowEachOtherForCommonVisibilityIsFalse :
      peopleMustKnowEachOtherForCommonVisibility ≡ false

    peopleMustShareProgrammeForCommonVisibility : Bool
    peopleMustShareProgrammeForCommonVisibilityIsFalse :
      peopleMustShareProgrammeForCommonVisibility ≡ false

    commonVisibilityImpliesCommonSelection : Bool
    commonVisibilityImpliesCommonSelectionIsFalse :
      commonVisibilityImpliesCommonSelection ≡ false

    commonSelectionImpliesCommonAdversary : Bool
    commonSelectionImpliesCommonAdversaryIsFalse :
      commonSelectionImpliesCommonAdversary ≡ false

    publicVisibilityImpliesClassifiedVisibility : Bool
    publicVisibilityImpliesClassifiedVisibilityIsFalse :
      publicVisibilityImpliesClassifiedVisibility ≡ false

    absenceOfVictimVictimEdgeRefutesCommonSelector : Bool
    absenceOfVictimVictimEdgeRefutesCommonSelectorIsFalse :
      absenceOfVictimVictimEdgeRefutesCommonSelector ≡ false

    selectorMustBeOneNaturalPerson : Bool
    selectorMustBeOneNaturalPersonIsFalse :
      selectorMustBeOneNaturalPerson ≡ false

canonicalCommonSelectorBoundary : CommonSelectorBoundary
canonicalCommonSelectorBoundary =
  common-selector-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
