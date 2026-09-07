module DASHI.Cognition.PNF.SensibLawCountryRelationalLossGenocideBoundaryExact where

------------------------------------------------------------------------
-- COUNTRY RELATIONAL LOSS / GENOCIDE BOUNDARY
--
-- This owner keeps four distinct proposition kinds:
--   1. source-specific findings of permanent/intergenerational relational loss;
--   2. source-specific genocide findings (e.g. Bringing Them Home on forcible
--      child removal);
--   3. the legal Genocide Convention element structure;
--   4. DASHI/decolonial critical classification of cultural destruction.
--
-- Relational destruction may be morally, culturally and politically genocidal
-- without automatically satisfying the narrower Convention definition.  In the
-- Stolen Generations source lane, however, the national inquiry itself made a
-- genocide finding tied to forcible child transfer and eliminatory purpose.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Environment.LESCountryRelationalTransmissionIrreversibilityExact as Relation
import DASHI.Core.OperationalSystemBehaviourSemanticsExact as POSIWID

------------------------------------------------------------------------
-- Legal element carrier for the Genocide Convention.
------------------------------------------------------------------------

data ProtectedGroupKind : Set where
  nationalGroup ethnicalGroup racialGroup religiousGroup : ProtectedGroupKind

data ConventionAct : Set where
  killingMembers
  seriousBodilyOrMentalHarm
  destructiveConditionsOfLife
  preventBirths
  forciblyTransferChildren
  : ConventionAct

data GroupDestructionIntent : Set where
  specificIntentToDestroyGroupInWholeOrPart
  intentNotEstablished
  intentUnresolved
  : GroupDestructionIntent

data GenocideLegalStatus : Set where
  conventionGenocideElementsClosed
  conventionGenocideElementsOpen
  conventionGenocideNotDetermined
  : GenocideLegalStatus

record GenocideConventionElementReceipt : Set where
  constructor genocide-convention-element-receipt
  field
    protectedGroup : ProtectedGroupKind
    enumeratedAct : ConventionAct
    intent : GroupDestructionIntent
    sourceReference : String
    sourceAuthorityKind : String
    status : GenocideLegalStatus
    thisReceiptIsJudicialCriminalConviction : Bool
    sourceSaysThisExactClassification : Bool

open GenocideConventionElementReceipt public

------------------------------------------------------------------------
-- Bringing Them Home is an institutional inquiry finding, not a criminal
-- conviction.  The report expressly classified forcible removal policies aimed
-- at eliminating Indigenous cultures as genocide under international law.
------------------------------------------------------------------------

bringingThemHomeGenocideFinding : GenocideConventionElementReceipt
bringingThemHomeGenocideFinding = genocide-convention-element-receipt
  racialGroup
  forciblyTransferChildren
  specificIntentToDestroyGroupInWholeOrPart
  "Bringing them Home, Chapter 13/14: HREOC inquiry conclusion on forcible child removal and purpose of eliminating Indigenous cultures as distinct entities"
  "Human Rights and Equal Opportunity Commission institutional inquiry finding"
  conventionGenocideElementsClosed
  false
  true

------------------------------------------------------------------------
-- Permanent/intergenerational cultural loss is a different source proposition.
------------------------------------------------------------------------

data RelationalDestructionStatus : Set where
  sourceAcceptedPermanentIntergenerationalLoss
  sourceAcceptedCulturalLinkDestruction
  decolonialCulturalGenocideClassification
  legalGenocideNotYetClassified
  : RelationalDestructionStatus

record RelationalDestructionReceipt : Set where
  constructor relational-destruction-receipt
  field
    status : RelationalDestructionStatus
    relationLost : String
    sourceReference : String
    sourceAuthorityKind : String
    legalConventionGenocideAutomaticallyFollows : Bool
    legalConventionGenocideAutomaticallyFollowsIsFalse :
      legalConventionGenocideAutomaticallyFollows ≡ false

open RelationalDestructionReceipt public

griffithsRelationalLossReceipt : RelationalDestructionReceipt
griffithsRelationalLossReceipt = relational-destruction-receipt
  sourceAcceptedPermanentIntergenerationalLoss
  "cultural/spiritual connection to Country; responsibility under traditional laws/customs; incremental and cumulative loss accepted as permanent and intergenerational"
  "Northern Territory v Griffiths [2019] HCA 7, especially [180]-[206], [230]"
  "High Court accepted findings in native-title compensation litigation"
  false refl

bringingThemHomeCulturalDestructionReceipt : RelationalDestructionReceipt
bringingThemHomeCulturalDestructionReceipt = relational-destruction-receipt
  sourceAcceptedCulturalLinkDestruction
  "language, cultural knowledge, kinship, land connection, traditional responsibilities and intergenerational transmission disrupted through forcible removal"
  "Bringing them Home (1997), especially Chapters 11, 13 and 14"
  "Human Rights and Equal Opportunity Commission institutional inquiry"
  false refl

------------------------------------------------------------------------
-- Decolonial classification is explicit DASHI interpretation.  It can name
-- destruction of group-constitutive relational/transmission structures as
-- cultural-genocidal without pretending the Genocide Convention has a free-
-- standing cultural-destruction limb.
------------------------------------------------------------------------

record DecolonialGenocideLens : Set where
  constructor decolonial-genocide-lens
  field
    relationOrTransmissionTarget : String
    groupContinuityFunction : String
    destructionClassification : String
    classificationAuthor : String
    conventionStatusStillNeedsEnumeratedActAndSpecificIntent : Bool
    conventionStatusStillNeedsEnumeratedActAndSpecificIntentIsTrue :
      conventionStatusStillNeedsEnumeratedActAndSpecificIntent ≡ true
    lensAutomaticallyBackAttributedToCourtOrCommunity : Bool
    lensAutomaticallyBackAttributedToCourtOrCommunityIsFalse :
      lensAutomaticallyBackAttributedToCourtOrCommunity ≡ false

open DecolonialGenocideLens public

countryRelationalCulturalGenocideLens : DecolonialGenocideLens
countryRelationalCulturalGenocideLens = decolonial-genocide-lens
  "destruction of intergenerational transmission, Country relation, story/law/language, kinship, ceremony, custodial authority and future-generation responsibility"
  "these relations can constitute the continuity of a people as a distinct cultural/political community rather than a detachable private preference"
  "DASHI decolonial critical classification: targeted destruction of group-constitutive relation/transmission can be classified as cultural-genocidal; Convention genocide remains a separately elemented legal conclusion"
  "DASHI/SensibLaw synthesis"
  true refl
  false refl

------------------------------------------------------------------------
-- POSIWID cross-pollination: realised cultural destruction and genocidal intent
-- are different coordinates.  A benevolent mission statement does not erase
-- repeated realised harm; but realised harm alone does not manufacture mens rea.
------------------------------------------------------------------------

posiwidBoundary : POSIWID.OperationalDescriptionBoundary
posiwidBoundary = POSIWID.canonicalOperationalDescriptionBoundary

declaredPurposeDoesNotOverrideRealisedRelationalDestruction :
  POSIWID.declaredPurposeOverridesRepeatedRealizedEffect posiwidBoundary ≡ false
declaredPurposeDoesNotOverrideRealisedRelationalDestruction = refl

realisedOperationMayClassifySystemBehaviour :
  POSIWID.observedOperationMayClassifyWhatSystemDoes posiwidBoundary ≡ true
realisedOperationMayClassifySystemBehaviour = refl

------------------------------------------------------------------------
-- Exact temporal point: reparation can support future reconstitution but cannot
-- make a historically missed transmission event have occurred at the original
-- time.  This is not a claim that Indigenous cultures are static or incapable
-- of renewal.
------------------------------------------------------------------------

historicalLossCannotBeRetroactivelyUndone :
  Relation.historicalOccurrence Relation.transmissionMissedAtHistoricalMoment
  ≡ Relation.historicalOccurrence Relation.laterReconstitutionOccurred
historicalLossCannotBeRetroactivelyUndone = refl

futureReconstitutionRemainsOpen :
  Relation.futureCapacity Relation.transmissionMissedAtHistoricalMoment
  ≡ Relation.futureReconstitutionOpen
futureReconstitutionRemainsOpen = refl

------------------------------------------------------------------------
-- No-collapse laws.
------------------------------------------------------------------------

data PermanentCulturalLossAloneEqualsConventionGenocide : Set where
data ConventionGenocideRequiresOnlyBadOutcomeWithoutIntent : Set where
data BringingThemHomeFindingIsCriminalConviction : Set where
data FutureCulturalReconstitutionErasesHistoricalGenocideOrLoss : Set where
data POSIWIDOutcomeClassificationProvesSpecificGenocidalIntent : Set where

aPermanentLossDoesNotByItselfCloseConventionGenocide :
  PermanentCulturalLossAloneEqualsConventionGenocide → ⊥
aPermanentLossDoesNotByItselfCloseConventionGenocide ()

badOutcomeAloneDoesNotPayConventionIntent :
  ConventionGenocideRequiresOnlyBadOutcomeWithoutIntent → ⊥
badOutcomeAloneDoesNotPayConventionIntent ()

inquiryFindingIsNotCriminalConviction : BringingThemHomeFindingIsCriminalConviction → ⊥
inquiryFindingIsNotCriminalConviction ()

futureReconstitutionDoesNotRewriteHistoricalLoss :
  FutureCulturalReconstitutionErasesHistoricalGenocideOrLoss → ⊥
futureReconstitutionDoesNotRewriteHistoricalGenocideOrLoss ()

posiwidDoesNotManufactureMensRea :
  POSIWIDOutcomeClassificationProvesSpecificGenocidalIntent → ⊥
posiwidDoesNotManufactureMensRea ()
