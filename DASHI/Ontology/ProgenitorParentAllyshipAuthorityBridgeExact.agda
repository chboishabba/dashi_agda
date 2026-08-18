module DASHI.Ontology.ProgenitorParentAllyshipAuthorityBridgeExact where

open import DASHI.Core.Prelude using (Bool; true; false; _≡_; refl)

import DASHI.Biology.ParentAllyshipMultiObserverBridge as Allyship
import DASHI.Governance.DiachronicDelegatedAuthorityBoundary as Diachronic

------------------------------------------------------------------------
-- Cross-pollination: parent/family expertise is a legitimate observer fibre,
-- not a sovereignty theorem.
--
-- ParentAllyshipMultiObserverBridge already says parent expertise may be
-- evidence while child voice remains distinct and no observer equals the whole
-- system. DiachronicDelegatedAuthorityBoundary independently says a supporter
-- cannot self-authorise override. Their conjunction gives the exact boundary
-- required by the family-agency != parental-sovereignty synthesis.
------------------------------------------------------------------------

parentExpertiseMayBeEvidence :
  Allyship.parentExpertiseMayBeEvidence
    Allyship.canonicalParentAllyshipMultiObserverBridge ≡ true
parentExpertiseMayBeEvidence = refl

childVoiceRemainsDistinct :
  Allyship.childVoiceRemainsDistinct
    Allyship.canonicalParentAllyshipMultiObserverBridge ≡ true
childVoiceRemainsDistinct = refl

parentObserverIsNotWholeSystem :
  Allyship.noObserverProjectionEqualsWhole
    Allyship.canonicalParentAllyshipMultiObserverBridge ≡ true
parentObserverIsNotWholeSystem = refl

supporterCannotSelfAuthoriseOverride :
  Diachronic.supporterCannotSelfAuthoriseOverride
    Diachronic.canonicalSupportedDecisionConditions ≡ true
supporterCannotSelfAuthoriseOverride = refl

record FamilyAgencyAuthorityBoundary : Set where
  constructor familyAgencyAuthorityBoundary
  field
    familyExpertiseCountsAsEvidence : Bool
    familyExpertiseCountsAsEvidenceIsTrue :
      familyExpertiseCountsAsEvidence ≡ true
    childVoiceIsIndependentObserverFibre : Bool
    childVoiceIsIndependentObserverFibreIsTrue :
      childVoiceIsIndependentObserverFibre ≡ true
    parentObserverIsCanonicalWhole : Bool
    parentObserverIsCanonicalWholeIsFalse :
      parentObserverIsCanonicalWhole ≡ false
    familySupportRoleSelfAuthorisesOverride : Bool
    familySupportRoleSelfAuthorisesOverrideIsFalse :
      familySupportRoleSelfAuthorisesOverride ≡ false

canonicalFamilyAgencyAuthorityBoundary : FamilyAgencyAuthorityBoundary
canonicalFamilyAgencyAuthorityBoundary =
  familyAgencyAuthorityBoundary true refl true refl false refl false refl

familyAgencyDoesNotImplyParentalSovereignty :
  parentObserverIsCanonicalWhole canonicalFamilyAgencyAuthorityBoundary ≡ false
  × familySupportRoleSelfAuthorisesOverride canonicalFamilyAgencyAuthorityBoundary ≡ false
familyAgencyDoesNotImplyParentalSovereignty = refl , refl
