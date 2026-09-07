module DASHI.Law.QueenslandWrongTypeCausationDeclarationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Interop.SensibLawOntologyTopology as Ontology
import DASHI.Law.QueenslandButForSourceBoundaryExact as Source
import DASHI.Law.QueenslandCausationApplicabilitySourceExact as Applicability
import DASHI.Law.SensibLawWrongTypeCausationElementExact as Element
import DASHI.Law.SensibLawCausationQualifiedLiabilityBridgeExact as Qualified

------------------------------------------------------------------------
-- QUEENSLAND PRIMARY SOURCE -> EXACT WRONGTYPE ELEMENT DECLARATION
--
-- DASHI-original source-to-ontology weld.
--
-- The Queensland Act owns the statutory propositions.  SensibLaw owns the
-- WrongType carrier.  DASHI owns only this typed weld.  No declaration is
-- produced from the word "negligent", from parser syntax, or from source
-- authority alone: applicability and same-source/same-system receipts are
-- explicit prerequisites.
------------------------------------------------------------------------

record QueenslandWrongTypeSourceWeld : Set₁ where
  constructor queenslandWrongTypeSourceWeld
  field
    wrongType : Ontology.WrongType
    queenslandSourceId : Ontology.StableId
    queenslandLegalSystemId : Ontology.StableId

    sourceIdBelongsToWrongTypeReceipt : Set
    definingSystemIsQueenslandReceipt :
      Ontology.WrongType.definingSystem wrongType ≡ queenslandLegalSystemId

    applicability : Applicability.QueenslandCausationApplicabilityReceipt
    sourceAuthorityReceipt : Set
    sourceValidityReceipt : Set
    weldReference : String

open QueenslandWrongTypeSourceWeld public

------------------------------------------------------------------------
-- Statutory element declarations.
--
-- Element identifiers remain caller/ontology supplied because this module does
-- not invent database identities.  The source proposition determines the kind
-- and requirement; the existing WrongType supplies identity.
------------------------------------------------------------------------

ordinaryFactualCausationDeclaration :
  (weld : QueenslandWrongTypeSourceWeld) →
  String →
  Element.WrongTypeCausationElementDeclaration
ordinaryFactualCausationDeclaration weld elementId =
  Element.wrongTypeCausationElementDeclaration
    (wrongType weld)
    elementId
    Element.ordinaryFactualCausationElement
    Qualified.causationRequired
    "Civil Liability Act 2003 (Qld) s 11(1)(a): necessary-condition factual causation"
    (queenslandSourceId weld)
    (sourceAuthorityReceipt weld)
    "Queensland primary-source declaration; DASHI compiler"

scopeOfLiabilityDeclaration :
  (weld : QueenslandWrongTypeSourceWeld) →
  String →
  Element.WrongTypeCausationElementDeclaration
scopeOfLiabilityDeclaration weld elementId =
  Element.wrongTypeCausationElementDeclaration
    (wrongType weld)
    elementId
    Element.scopeOfLiabilityElement
    Qualified.causationRequired
    "Civil Liability Act 2003 (Qld) s 11(1)(b), s 11(4): scope of liability"
    (queenslandSourceId weld)
    (sourceAuthorityReceipt weld)
    "Queensland primary-source declaration; DASHI compiler"

record ExceptionalRouteAvailability : Set where
  constructor exceptionalRouteAvailability
  field
    ordinaryNecessaryConditionCannotBeEstablishedReceipt : Set
    establishedPrinciplesReceipt : Set
    responsibilityInquiryReceipt : Set
    routeAuthorityReceipt : Set
    routeReference : String

open ExceptionalRouteAvailability public

exceptionalFactualCausationDeclaration :
  (weld : QueenslandWrongTypeSourceWeld) →
  ExceptionalRouteAvailability →
  String →
  Element.WrongTypeCausationElementDeclaration
exceptionalFactualCausationDeclaration weld exceptional elementId =
  Element.wrongTypeCausationElementDeclaration
    (wrongType weld)
    elementId
    Element.exceptionalFactualCausationElement
    Qualified.causationRequired
    "Civil Liability Act 2003 (Qld) s 11(2): exceptional established-principles route"
    (queenslandSourceId weld)
    (routeAuthorityReceipt exceptional)
    (routeReference exceptional)

------------------------------------------------------------------------
-- Primary-source ownership receipts.
------------------------------------------------------------------------

record QueenslandCausationSourceOwnership : Set where
  constructor queenslandCausationSourceOwnership
  field
    statuteOwnsNecessaryConditionRule : Bool
    statuteOwnsNecessaryConditionRuleIsTrue :
      statuteOwnsNecessaryConditionRule ≡ true
    statuteOwnsScopeSeparation : Bool
    statuteOwnsScopeSeparationIsTrue : statuteOwnsScopeSeparation ≡ true
    statuteOwnsExceptionalRouteAvailability : Bool
    statuteOwnsExceptionalRouteAvailabilityIsTrue :
      statuteOwnsExceptionalRouteAvailability ≡ true
    dashiOwnsWrongTypeCompiler : Bool
    dashiOwnsWrongTypeCompilerIsTrue : dashiOwnsWrongTypeCompiler ≡ true
    highCourtCalibrationOwnsQueenslandText : Bool
    highCourtCalibrationOwnsQueenslandTextIsFalse :
      highCourtCalibrationOwnsQueenslandText ≡ false

canonicalQueenslandCausationSourceOwnership : QueenslandCausationSourceOwnership
canonicalQueenslandCausationSourceOwnership =
  queenslandCausationSourceOwnership
    true refl true refl true refl true refl false refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data QueenslandSourceAuthorityAutomaticallyAppliesToWrongType : Set where
data NegligentCulpabilityAutomaticallyGetsQueenslandSection11 : Set where
data ParserMentionOfButForDeclaresStatutoryElement : Set where
data HighCourtCalibrationCanReplaceQueenslandPrimarySource : Set where

authorityDoesNotAutoApplyToWrongType :
  QueenslandSourceAuthorityAutomaticallyAppliesToWrongType → ⊥
authorityDoesNotAutoApplyToWrongType ()

negligentCulpabilityDoesNotAutoSelectQueenslandStatute :
  NegligentCulpabilityAutomaticallyGetsQueenslandSection11 → ⊥
negligentCulpabilityDoesNotAutoSelectQueenslandStatute ()

parserMentionDoesNotDeclareLegalElement :
  ParserMentionOfButForDeclaresStatutoryElement → ⊥
parserMentionDoesNotDeclareLegalElement ()

highCourtCalibrationDoesNotReplacePrimarySource :
  HighCourtCalibrationCanReplaceQueenslandPrimarySource → ⊥
highCourtCalibrationDoesNotReplacePrimarySource ()
