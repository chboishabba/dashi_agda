module ClaimReconciliationObjectLattice where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Agda.Primitive using (Setω)

import LoomRelationAlgebra as Relation

------------------------------------------------------------------------
-- Claim-reconciliation object lattice.
--
-- This is the minimal DASHI-side carrier for the SensibLaw affidavit
-- reconciliation formalism. It classifies claim atoms, response relations,
-- typed-object assertions, and Wikidata-style statement rows. It does not
-- decide legal sufficiency, global truth, or theorem promotion.

data ClaimPolarity : Set where
  positivePolarity : ClaimPolarity
  negativePolarity : ClaimPolarity
  qualifiedPolarity : ClaimPolarity
  neutralPolarity : ClaimPolarity
  unknownPolarity : ClaimPolarity

data ClaimSourceKind : Set where
  affidavitSource : ClaimSourceKind
  responseSource : ClaimSourceKind
  sourceReceiptSource : ClaimSourceKind
  wikidataStatementSource : ClaimSourceKind
  typedObjectAssertionSource : ClaimSourceKind

data PropositionType : Set where
  factualEvent : PropositionType
  subjectiveFeeling : PropositionType
  allegation : PropositionType
  denial : PropositionType
  proceduralFact : PropositionType
  legalClaim : PropositionType
  relationshipState : PropositionType
  capabilityStatement : PropositionType
  careOrRolePerformance : PropositionType
  typedObjectClaim : PropositionType

data ReviewStatus : Set where
  reviewRequired : ReviewStatus
  reviewedCarrier : ReviewStatus
  witnessPending : ReviewStatus
  witnessBlocked : ReviewStatus

data ResponseAct : Set where
  confirmResponse : ResponseAct
  denyResponse : ResponseAct
  explainResponse : ResponseAct
  qualifyResponse : ResponseAct
  redirectResponse : ResponseAct
  substituteResponse : ResponseAct
  adjacentNarrativeResponse : ResponseAct
  proceduralFrameResponse : ResponseAct
  nonResponse : ResponseAct

data AuthorityReading : Set where
  sourceLocalAssertion : AuthorityReading
  sharedTextDuplicate : AuthorityReading
  proceduralRecord : AuthorityReading
  laterContextualAddition : AuthorityReading

record ClaimAtom : Set where
  constructor claimAtom
  field
    propositionId :
      String

    span :
      String

    propositionType :
      PropositionType

    subject :
      String

    subjectRole :
      String

    actionLemma :
      String

    object :
      String

    objectRole :
      String

    timeExpression :
      String

    locationExpression :
      String

    modality :
      String

    polarity :
      ClaimPolarity

    domain :
      String

    sourceKind :
      ClaimSourceKind

    reviewStatus :
      ReviewStatus

    provenanceNote :
      String

    claimPromotionState :
      Relation.LoomPromotionState

    claimPromotionStateIsFalse :
      claimPromotionState ≡ Relation.promotionFalse

record ResponseUnit : Set where
  constructor responseUnit
  field
    responseUnitId :
      String

    span :
      String

    responseAct :
      ResponseAct

    subject :
      String

    subjectRole :
      String

    actionLemma :
      String

    object :
      String

    timeExpression :
      String

    modality :
      String

    polarity :
      ClaimPolarity

    explicitDisputeFlag :
      Bool

    explicitSupportFlag :
      Bool

    proceduralFrameFlag :
      Bool

    reviewStatus :
      ReviewStatus

    provenanceNote :
      String

    responsePromotionState :
      Relation.LoomPromotionState

    responsePromotionStateIsFalse :
      responsePromotionState ≡ Relation.promotionFalse

record ClaimRoot : Set where
  constructor claimRoot
  field
    claimRootId :
      String

    claimRootText :
      String

    claimRootBasis :
      String

    authorityReading :
      AuthorityReading

    rootPromotionState :
      Relation.LoomPromotionState

    rootPromotionStateIsFalse :
      rootPromotionState ≡ Relation.promotionFalse

record ClaimRelationAssessment : Set where
  constructor claimRelationAssessment
  field
    leftClaim :
      ClaimAtom

    rightClaim :
      ClaimAtom

    typedRelation :
      Relation.LoomTypedRelation

    dominantRelation :
      Relation.LoomRelationType

    dominantRelationIsRelationType :
      dominantRelation ≡ Relation.relationType typedRelation

    assessmentNote :
      String

data TypedObjectWitnessStatus : Set where
  typingContextMissing : TypedObjectWitnessStatus
  typingContextNamed : TypedObjectWitnessStatus
  typingWitnessPending : TypedObjectWitnessStatus
  typingWitnessed : TypedObjectWitnessStatus
  typingBlocked : TypedObjectWitnessStatus

record TypedObjectAssertion : Set where
  constructor typedObjectAssertion
  field
    assertionId :
      String

    objectToken :
      String

    claimedType :
      String

    typingContext :
      String

    witnessStatus :
      TypedObjectWitnessStatus

    sourceClaim :
      ClaimAtom

    reviewStatus :
      ReviewStatus

    assertionPromotionState :
      Relation.LoomPromotionState

    assertionPromotionStateIsFalse :
      assertionPromotionState ≡ Relation.promotionFalse

    assertionNote :
      String

record WikidataQualifier : Set where
  constructor wikidataQualifier
  field
    qualifierPropertyPid :
      String

    qualifierValue :
      String

    qualifierWindow :
      String

    qualifierReviewNote :
      String

record WikidataReference : Set where
  constructor wikidataReference
  field
    referenceToken :
      String

    referenceHandle :
      String

    referenceWindow :
      String

    referenceNote :
      String

record WikidataRevisionWindow : Set where
  constructor wikidataRevisionWindow
  field
    revisionId :
      String

    windowId :
      String

    windowNote :
      String

record WikidataStatementRow : Set where
  constructor wikidataStatementRow
  field
    statementId :
      String

    entityQid :
      String

    propertyPid :
      String

    valueToken :
      String

    qualifier :
      WikidataQualifier

    reference :
      WikidataReference

    revisionWindow :
      WikidataRevisionWindow

    sourceClaim :
      ClaimAtom

    reviewStatus :
      ReviewStatus

    truthClaimed :
      Bool

    truthClaimedIsFalse :
      truthClaimed ≡ false

    liveEditAuthority :
      Bool

    liveEditAuthorityIsFalse :
      liveEditAuthority ≡ false

    wikidataPromotionState :
      Relation.LoomPromotionState

    wikidataPromotionStateIsFalse :
      wikidataPromotionState ≡ Relation.promotionFalse

    statementNote :
      String

open ClaimAtom public
open ResponseUnit public
open ClaimRoot public
open ClaimRelationAssessment public
open TypedObjectAssertion public
open WikidataQualifier public
open WikidataReference public
open WikidataRevisionWindow public
open WikidataStatementRow public
open ClaimPolarity public
open ClaimSourceKind public
open PropositionType public
open ReviewStatus public
open ResponseAct public
open AuthorityReading public
open TypedObjectWitnessStatus public

canonicalDogWalkedClaim : ClaimAtom
canonicalDogWalkedClaim =
  claimAtom
    "dog-walked-positive"
    "X walked the dog."
    factualEvent
    "X"
    "actor"
    "walk"
    "dog"
    "patient"
    "unspecified"
    "unspecified"
    "asserted"
    positivePolarity
    "affidavit-demo"
    affidavitSource
    reviewedCarrier
    "Canonical minimal proposition atom for the walked-dog support/dispute fixture."
    Relation.promotionFalse
    refl

canonicalDogNotWalkedClaim : ClaimAtom
canonicalDogNotWalkedClaim =
  claimAtom
    "dog-walked-negative"
    "X did not walk the dog."
    denial
    "X"
    "actor"
    "walk"
    "dog"
    "patient"
    "unspecified"
    "unspecified"
    "denied"
    negativePolarity
    "affidavit-demo"
    responseSource
    reviewedCarrier
    "Canonical minimal response atom that directly disputes the walked-dog proposition."
    Relation.promotionFalse
    refl

canonicalDogNotWalkedResponseUnit : ResponseUnit
canonicalDogNotWalkedResponseUnit =
  responseUnit
    "dog-walked-negative-response"
    "X did not walk the dog."
    denyResponse
    "X"
    "actor"
    "walk"
    "dog"
    "unspecified"
    "denied"
    negativePolarity
    true
    false
    false
    reviewedCarrier
    "Canonical response unit for the explicit dog-walk denial."
    Relation.promotionFalse
    refl

canonicalDogIncidentRoot : ClaimRoot
canonicalDogIncidentRoot =
  claimRoot
    "dog-walk-incident-root"
    "Whether X walked the dog."
    "same subject, action lemma, object, and event family"
    sourceLocalAssertion
    Relation.promotionFalse
    refl

canonicalDogExplicitDisputeRelation :
  ClaimRelationAssessment
canonicalDogExplicitDisputeRelation =
  claimRelationAssessment
    canonicalDogWalkedClaim
    canonicalDogNotWalkedClaim
    ( Relation.loomTypedRelation
        Relation.explicitDispute
        Relation.invalidates
        refl
        Relation.disputedBucket
        refl
        Relation.witnessed
        Relation.promotionFalse
        "Positive and negative same-action/same-object claims form an explicit dispute." )
    Relation.explicitDispute
    refl
    "This classifies the relation between claim atoms; it does not decide which side is true."

canonicalSixIsOneMorphismClaim : ClaimAtom
canonicalSixIsOneMorphismClaim =
  claimAtom
    "six-is-one-morphism"
    "6 is a 1-morphism."
    typedObjectClaim
    "6"
    "object-token"
    "has-type"
    "1-morphism"
    "claimed-type"
    "unspecified"
    "unspecified"
    "asserted"
    positivePolarity
    "typed-object-demo"
    typedObjectAssertionSource
    witnessPending
    "A typed-object assertion requires an explicit category/context and typing witness."
    Relation.promotionFalse
    refl

canonicalSixOneMorphismAssertion : TypedObjectAssertion
canonicalSixOneMorphismAssertion =
  typedObjectAssertion
    "six-one-morphism-assertion"
    "6"
    "1-morphism"
    "context-missing"
    typingContextMissing
    canonicalSixIsOneMorphismClaim
    witnessPending
    Relation.promotionFalse
    refl
    "Without a named category or bicategory and a typing rule, this remains a non-promoting witness-pending assertion."

canonicalWikidataDogStatementClaim : ClaimAtom
canonicalWikidataDogStatementClaim =
  claimAtom
    "wikidata-dog-row-carrier"
    "QID/PID row about a dog-related statement."
    factualEvent
    "Q-demo"
    "wikidata-entity"
    "P-demo"
    "dog-related-value"
    "wikidata-value"
    "unspecified"
    "unspecified"
    "statement-row"
    unknownPolarity
    "wikidata-demo"
    wikidataStatementSource
    reviewRequired
    "Wikidata-style rows are structured evidence carriers, not automatic truth."
    Relation.promotionFalse
    refl

canonicalWikidataQualifier : WikidataQualifier
canonicalWikidataQualifier =
  wikidataQualifier
    "P-qualifier-demo"
    "qualifier-value-demo"
    "window-demo"
    "Qualifier scope is retained for drift/review; it is not treated as truth promotion."

canonicalWikidataReference : WikidataReference
canonicalWikidataReference =
  wikidataReference
    "reference-demo"
    "reference-handle-demo"
    "window-demo"
    "Reference handles witness row provenance only, not real-world truth."

canonicalWikidataRevisionWindow : WikidataRevisionWindow
canonicalWikidataRevisionWindow =
  wikidataRevisionWindow
    "revision-demo"
    "window-demo"
    "Revision/window anchoring keeps this row bounded and deterministic."

canonicalWikidataStatementRow : WikidataStatementRow
canonicalWikidataStatementRow =
  wikidataStatementRow
    "statement-demo-0"
    "Q-demo"
    "P-demo"
    "dog-related-value"
    canonicalWikidataQualifier
    canonicalWikidataReference
    canonicalWikidataRevisionWindow
    canonicalWikidataDogStatementClaim
    reviewRequired
    false
    refl
    false
    refl
    Relation.promotionFalse
    refl
    "QID/PID/value/qualifier/reference structure is retained as provenance; live Wikidata authority is outside this module."

record ClaimReconciliationObjectLattice : Setω where
  field
    claimAtoms :
      List ClaimAtom

    canonicalDogClaims :
      List ClaimAtom

    dogClaimsAreCanonical :
      canonicalDogClaims
      ≡
      canonicalDogWalkedClaim
      ∷ canonicalDogNotWalkedClaim
      ∷ []

    claimRelations :
      List ClaimRelationAssessment

    canonicalDogRelation :
      ClaimRelationAssessment

    responseUnits :
      List ResponseUnit

    claimRoots :
      List ClaimRoot

    typedObjectAssertions :
      List TypedObjectAssertion

    wikidataStatementRows :
      List WikidataStatementRow

    relationAlgebra :
      Relation.LoomRelationAlgebra

    promotionSeparated :
      Bool

    promotionSeparatedIsTrue :
      promotionSeparated ≡ true

    latticeBoundary :
      List String

open ClaimReconciliationObjectLattice public

canonicalClaimReconciliationObjectLattice :
  ClaimReconciliationObjectLattice
canonicalClaimReconciliationObjectLattice =
  record
    { claimAtoms =
        canonicalDogWalkedClaim
        ∷ canonicalDogNotWalkedClaim
        ∷ canonicalSixIsOneMorphismClaim
        ∷ canonicalWikidataDogStatementClaim
        ∷ []
    ; canonicalDogClaims =
        canonicalDogWalkedClaim
        ∷ canonicalDogNotWalkedClaim
        ∷ []
    ; dogClaimsAreCanonical =
        refl
    ; claimRelations =
        canonicalDogExplicitDisputeRelation
        ∷ []
    ; canonicalDogRelation =
        canonicalDogExplicitDisputeRelation
    ; responseUnits =
        canonicalDogNotWalkedResponseUnit
        ∷ []
    ; claimRoots =
        canonicalDogIncidentRoot
        ∷ []
    ; typedObjectAssertions =
        canonicalSixOneMorphismAssertion
        ∷ []
    ; wikidataStatementRows =
        canonicalWikidataStatementRow
        ∷ []
    ; relationAlgebra =
        Relation.canonicalLoomRelationAlgebra
    ; promotionSeparated =
        true
    ; promotionSeparatedIsTrue =
        refl
    ; latticeBoundary =
        "Dog walked / did not walk the dog is classified as an explicit dispute relation, not as a truth decision."
        ∷ "Typed-object assertions require context and witnesses before any stronger typing claim."
        ∷ "Wikidata rows are QID/PID/value/qualifier/reference evidence carriers, not live truth or edit authority."
        ∷ "Claim relation classification remains separate from legal sufficiency and theorem promotion."
        ∷ []
    }
