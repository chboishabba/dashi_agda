module DASHI.Applications.CounterUASNoveltyPromotionExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy

------------------------------------------------------------------------
-- NOVELTY CHARACTERIZATION / PROMOTION ELIGIBILITY
--
-- High-alpha boundary:
--   repeated agreement != independent evidence
--   pseudo-label != external corroboration
--   self-generated reference != semantic identity authority
--   reference match != promotion eligibility
--
-- The owner formalises evidentiary promotion only.  It contains no offensive
-- counter-UAS procedure or emitter-defeat recipe.
------------------------------------------------------------------------

agreementCountCreatesIndependentEvidence : Bool
agreementCountCreatesIndependentEvidence = false

pseudoLabelCreatesExternalCorroboration : Bool
pseudoLabelCreatesExternalCorroboration = false

selfGeneratedReferenceCreatesSemanticIdentity : Bool
selfGeneratedReferenceCreatesSemanticIdentity = false

promotionRequiresSameObjectLink : Bool
promotionRequiresSameObjectLink = true

promotionRequiresNonCircularEvidence : Bool
promotionRequiresNonCircularEvidence = true

contaminatedReferencePaysPromotion : Bool
contaminatedReferencePaysPromotion = false

------------------------------------------------------------------------
-- Promotion receipt.
------------------------------------------------------------------------

data GenealogyStatus : Set where
  selfDerivedGenealogy : GenealogyStatus
  externallyPaidGenealogy : GenealogyStatus
  genealogyUnresolved : GenealogyStatus

data ReferenceIntegrity : Set where
  cleanReference : ReferenceIntegrity
  contaminatedReference : ReferenceIntegrity
  integrityUnresolved : ReferenceIntegrity

data PromotionStatus : Set where
  characterizationOnly : PromotionStatus
  promotionEligible : PromotionStatus
  promotionBlocked : PromotionStatus

record NoveltyPromotionReceipt : Set where
  constructor noveltyPromotionReceipt
  field
    sameObjectLinkPaid : Bool
    sourceGenealogy : GenealogyStatus
    referenceIntegrity : ReferenceIntegrity
    externalLabelPayment : Bool
    contradictionChecked : Bool
    earlierUnknownStateRetained : Bool
    earlierUnknownStateRetainedIsTrue : earlierUnknownStateRetained ≡ true
    createsOperationalAuthority : Bool
    createsOperationalAuthorityIsFalse : createsOperationalAuthority ≡ false

open NoveltyPromotionReceipt public

selfEchoReceipt : NoveltyPromotionReceipt
selfEchoReceipt =
  noveltyPromotionReceipt
    true
    selfDerivedGenealogy
    integrityUnresolved
    false
    false
    true refl
    false refl

externallyPaidReceipt : NoveltyPromotionReceipt
externallyPaidReceipt =
  noveltyPromotionReceipt
    true
    externallyPaidGenealogy
    cleanReference
    true
    true
    true refl
    false refl

------------------------------------------------------------------------
-- I. Agreement count is inadequate for promotion eligibility.
--
-- Both worlds expose the same visible agreement surface.  In one, the second
-- agreement descends from the first (self-training/pseudo-label echo).  In the
-- other, an independently sourced label/reference pays the promotion debt.
------------------------------------------------------------------------

data PromotionWorld : Set where
  selfEchoWorld : PromotionWorld
  externallyPaidWorld : PromotionWorld

data AgreementSurface : Set where
  sameAgreementCount : AgreementSurface

data GenealogySurface : Set where
  selfEchoSurface : GenealogySurface
  externalPaymentSurface : GenealogySurface

data PromotionQuery : Set where
  agreementQuery : PromotionQuery
  promotionEligibilityQuery : PromotionQuery

data PromotionAnswer : Set where
  agreementObserved : PromotionAnswer
  promotionNotEligible : PromotionAnswer
  promotionEligibleAnswer : PromotionAnswer

agreementOnlyProjection : PromotionWorld → AgreementSurface
agreementOnlyProjection world = sameAgreementCount

genealogyProjection : PromotionWorld → GenealogySurface
genealogyProjection selfEchoWorld = selfEchoSurface
genealogyProjection externallyPaidWorld = externalPaymentSurface

promotionAnswer : PromotionQuery → PromotionWorld → PromotionAnswer
promotionAnswer agreementQuery world = agreementObserved
promotionAnswer promotionEligibilityQuery selfEchoWorld = promotionNotEligible
promotionAnswer promotionEligibilityQuery externallyPaidWorld = promotionEligibleAnswer

promotionSemantics :
  Adequacy.QuerySemantics PromotionWorld PromotionQuery PromotionAnswer
promotionSemantics = Adequacy.querySemantics promotionAnswer

agreementOnlyPromotionAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    agreementOnlyProjection
    promotionSemantics
    promotionEligibilityQuery
agreementOnlyPromotionAdequacyDefect =
  Adequacy.queryAdequacyDefect
    selfEchoWorld
    externallyPaidWorld
    refl
    (λ ())

agreementCountCannotDeterminePromotion :
  Adequacy.AdequateFor
    agreementOnlyProjection
    promotionSemantics
    promotionEligibilityQuery →
  ⊥
agreementCountCannotDeterminePromotion =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    agreementOnlyPromotionAdequacyDefect

agreementAndGenealogyProjection :
  PromotionWorld → AgreementSurface × GenealogySurface
agreementAndGenealogyProjection =
  Observer.pairObserver agreementOnlyProjection genealogyProjection

joinedPromotionAnswer :
  AgreementSurface × GenealogySurface → PromotionAnswer
joinedPromotionAnswer (sameAgreementCount , selfEchoSurface) = promotionNotEligible
joinedPromotionAnswer (sameAgreementCount , externalPaymentSurface) = promotionEligibleAnswer

agreementAndGenealogyDeterminePromotion :
  Adequacy.AdequateFor
    agreementAndGenealogyProjection
    promotionSemantics
    promotionEligibilityQuery
agreementAndGenealogyDeterminePromotion =
  Adequacy.factorsForQuery
    joinedPromotionAnswer
    (λ { selfEchoWorld → refl
       ; externallyPaidWorld → refl
       })

------------------------------------------------------------------------
-- II. A matching library/reference surface is inadequate for semantic-identity
-- promotion when provenance integrity differs.
------------------------------------------------------------------------

data IdentityWorld : Set where
  cleanExternallyPaidMatch : IdentityWorld
  contaminatedSelfGeneratedMatch : IdentityWorld

data ReferenceMatchSurface : Set where
  sameReferenceMatch : ReferenceMatchSurface

data IntegritySurface : Set where
  cleanIntegritySurface : IntegritySurface
  contaminatedIntegritySurface : IntegritySurface

data IdentityQuery : Set where
  referenceMatchQuery : IdentityQuery
  semanticIdentityQuery : IdentityQuery

data IdentityAnswer : Set where
  referenceMatched : IdentityAnswer
  identityPromotionEligible : IdentityAnswer
  identityPromotionBlocked : IdentityAnswer

referenceMatchProjection : IdentityWorld → ReferenceMatchSurface
referenceMatchProjection world = sameReferenceMatch

integrityProjection : IdentityWorld → IntegritySurface
integrityProjection cleanExternallyPaidMatch = cleanIntegritySurface
integrityProjection contaminatedSelfGeneratedMatch = contaminatedIntegritySurface

identityAnswer : IdentityQuery → IdentityWorld → IdentityAnswer
identityAnswer referenceMatchQuery world = referenceMatched
identityAnswer semanticIdentityQuery cleanExternallyPaidMatch = identityPromotionEligible
identityAnswer semanticIdentityQuery contaminatedSelfGeneratedMatch = identityPromotionBlocked

identitySemantics :
  Adequacy.QuerySemantics IdentityWorld IdentityQuery IdentityAnswer
identitySemantics = Adequacy.querySemantics identityAnswer

referenceMatchOnlyIdentityAdequacyDefect :
  Adequacy.QueryAdequacyDefect
    referenceMatchProjection
    identitySemantics
    semanticIdentityQuery
referenceMatchOnlyIdentityAdequacyDefect =
  Adequacy.queryAdequacyDefect
    cleanExternallyPaidMatch
    contaminatedSelfGeneratedMatch
    refl
    (λ ())

referenceMatchCannotDetermineIdentityPromotion :
  Adequacy.AdequateFor
    referenceMatchProjection
    identitySemantics
    semanticIdentityQuery →
  ⊥
referenceMatchCannotDetermineIdentityPromotion =
  Adequacy.queryAdequacyDefectBlocksFactorisation
    referenceMatchOnlyIdentityAdequacyDefect

referenceAndIntegrityProjection :
  IdentityWorld → ReferenceMatchSurface × IntegritySurface
referenceAndIntegrityProjection =
  Observer.pairObserver referenceMatchProjection integrityProjection

joinedIdentityAnswer :
  ReferenceMatchSurface × IntegritySurface → IdentityAnswer
joinedIdentityAnswer (sameReferenceMatch , cleanIntegritySurface) =
  identityPromotionEligible
joinedIdentityAnswer (sameReferenceMatch , contaminatedIntegritySurface) =
  identityPromotionBlocked

referenceAndIntegrityDetermineIdentityPromotion :
  Adequacy.AdequateFor
    referenceAndIntegrityProjection
    identitySemantics
    semanticIdentityQuery
referenceAndIntegrityDetermineIdentityPromotion =
  Adequacy.factorsForQuery
    joinedIdentityAnswer
    (λ { cleanExternallyPaidMatch → refl
       ; contaminatedSelfGeneratedMatch → refl
       })

------------------------------------------------------------------------
-- Pareto eligibility gate.  This is intentionally stricter than "the model
-- agreed with itself twice" and weaker than a claim that any particular source
-- proves ground-truth identity.
------------------------------------------------------------------------

promotionStatus : NoveltyPromotionReceipt → PromotionStatus
promotionStatus receipt with
  sameObjectLinkPaid receipt |
  sourceGenealogy receipt |
  referenceIntegrity receipt |
  externalLabelPayment receipt |
  contradictionChecked receipt
... | true | externallyPaidGenealogy | cleanReference | true | true = promotionEligible
... | true | selfDerivedGenealogy | _ | _ | _ = promotionBlocked
... | _ | _ | contaminatedReference | _ | _ = promotionBlocked
... | _ | _ | _ | _ | _ = characterizationOnly

selfEchoPromotionBlocked : promotionStatus selfEchoReceipt ≡ promotionBlocked
selfEchoPromotionBlocked = refl

externalPaymentPromotionEligible :
  promotionStatus externallyPaidReceipt ≡ promotionEligible
externalPaymentPromotionEligible = refl

record NoveltyPromotionBoundary : Set where
  constructor noveltyPromotionBoundary
  field
    repeatedAgreementEqualsIndependentEvidence : Bool
    repeatedAgreementEqualsIndependentEvidenceIsFalse :
      repeatedAgreementEqualsIndependentEvidence ≡ false
    selfReferenceEqualsExternalCorroboration : Bool
    selfReferenceEqualsExternalCorroborationIsFalse :
      selfReferenceEqualsExternalCorroboration ≡ false
    libraryMatchEqualsSemanticIdentity : Bool
    libraryMatchEqualsSemanticIdentityIsFalse :
      libraryMatchEqualsSemanticIdentity ≡ false
    promotionCreatesOperationalAuthority : Bool
    promotionCreatesOperationalAuthorityIsFalse :
      promotionCreatesOperationalAuthority ≡ false

canonicalNoveltyPromotionBoundary : NoveltyPromotionBoundary
canonicalNoveltyPromotionBoundary =
  noveltyPromotionBoundary false refl false refl false refl false refl
