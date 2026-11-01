module DASHI.Culture.RezaPatentBoundaryTransitionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.KnowledgeBoundaryTransitionBidiExact as T
import DASHI.Core.KnowledgeBoundaryKindBidiExact as K

------------------------------------------------------------------------
-- MONICA JACINTO / DALLIS HARDWICK PATENT APPLICATION
--
-- US09/954,835 was filed 2001-09-18 and published as US20030053926A1 on
-- 2003-03-20. 35 U.S.C. 122(a) / USPTO MPEP preserve unpublished patent
-- applications in confidence; section 122(b) then provides for publication.
-- This closes a same-application confidentiality->publication transition.
-- It does NOT establish classification, export-control release, discretionary
-- disclosure, or release of all underlying test/process know-how.
------------------------------------------------------------------------

rezaPatentPrivate : T.BoundaryStateReceipt
rezaPatentPrivate = T.boundary-state-receipt
  "Monica Jacinto and Dallis Hardwick"
  "US patent application 09/954,835, Burn-resistant and high tensile strength metal alloys"
  T.boundedPrivate
  T.primaryInstitutional
  "USPTO 35 U.S.C. 122(a); MPEP 1120/1128; application filed 2001-09-18"
  "The USPTO application record was within the statutory confidentiality regime before publication. This is a claim about the application record, not every underlying laboratory datum or tacit process detail."

rezaPatentPublic : T.BoundaryStateReceipt
rezaPatentPublic = T.boundary-state-receipt
  "Monica Jacinto and Dallis Hardwick"
  "US patent application 09/954,835 published as US20030053926A1"
  T.releasedPublicly
  T.primaryInstitutional
  "USPTO/Google Patents US20030053926A1; publication date 2003-03-20"
  "The same patent application was publicly published as US20030053926A1."

rezaPatentSameObject : T.SameBoundaryObject rezaPatentPrivate rezaPatentPublic
rezaPatentSameObject = T.same-boundary-object
  "Application number US09/954,835 is the application published as US20030053926A1"
  "The bounded and public receipts refer to the same USPTO application record."

rezaPatentCompletedTransition : T.CompletedBoundaryTransition rezaPatentPrivate rezaPatentPublic
rezaPatentCompletedTransition = T.completed-boundary-transition
  refl
  refl
  rezaPatentSameObject
  "Statutory USPTO confidentiality followed by publication of the same application."

rezaPatentTypedTransition : K.TypedBoundaryTransition
rezaPatentTypedTransition = K.typed-boundary-transition
  "Monica Jacinto and Dallis Hardwick"
  "US09/954,835 / US20030053926A1"
  K.ordinaryPatentConfidentiality
  rezaPatentPrivate
  rezaPatentPublic
  rezaPatentSameObject
  refl
  refl
  "35 U.S.C. 122; USPTO MPEP 1120/1128; US20030053926A1"
  "This is an exact routine patent-confidentiality -> statutory-publication boundary crossing. It must not be pooled with classified declassification, export-control release, or discretionary technical disclosure."

record CurrentRezaPatentBoundaryAssessment : Set where
  constructor current-reza-patent-boundary-assessment
  field
    sameApplicationBoundaryClosed : Bool
    sameApplicationBoundaryClosedIsTrue : sameApplicationBoundaryClosed ≡ true
    boundaryKindIsOrdinaryPatentConfidentiality : Bool
    boundaryKindIsOrdinaryPatentConfidentialityIsTrue :
      boundaryKindIsOrdinaryPatentConfidentiality ≡ true
    classificationReleaseEstablished : Bool
    classificationReleaseEstablishedIsFalse : classificationReleaseEstablished ≡ false
    exportControlReleaseEstablished : Bool
    exportControlReleaseEstablishedIsFalse : exportControlReleaseEstablished ≡ false
    allUnderlyingTestDataPublicEstablished : Bool
    allUnderlyingTestDataPublicEstablishedIsFalse :
      allUnderlyingTestDataPublicEstablished ≡ false
    personSpecificDiscretionaryDisclosureEstablished : Bool
    personSpecificDiscretionaryDisclosureEstablishedIsFalse :
      personSpecificDiscretionaryDisclosureEstablished ≡ false

canonicalCurrentRezaPatentBoundaryAssessment : CurrentRezaPatentBoundaryAssessment
canonicalCurrentRezaPatentBoundaryAssessment = current-reza-patent-boundary-assessment
  true refl
  true refl
  false refl
  false refl
  false refl
  false refl
