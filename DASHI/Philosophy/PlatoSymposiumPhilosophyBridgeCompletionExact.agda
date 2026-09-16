module DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Ontology.EpistemicTrit as Trit
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Bridge
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source

------------------------------------------------------------------------
-- COMPLETION SEAMS FOR THE JMD PLATO PHILOSOPHY BRIDGE
--
-- The parent bridge already owns the finite non-collapse results for:
--   lack -> seeking,
--   knowledge Boolean -> rich epistemic state,
--   complementarity -> relational adequacy,
--   surface appearance -> interior significance,
--   consensus -> plural dialectical state.
--
-- This file adds only the two missing theorem-bearing cross-pollinations from
-- the supplied design:
--   * same ascent-shaped carrier != same semantic grammar;
--   * same ruling role/authority != same service orientation.
--
-- It also records explicitly that Diotima's right opinion and DASHI's
-- `unresolved` epistemic trit are structural analogues, not definitionally or
-- historically identical concepts.
------------------------------------------------------------------------

existingBridgeRetained : Bool
existingBridgeRetained = true

sourceArchiveHash : String
sourceArchiveHash = Source.archiveSha256

ascentSourceContract : Bridge.LeanPhilosophyTheoremContract
ascentSourceContract = Bridge.diotimaAscentContract

craftSourceContract : Bridge.LeanPhilosophyTheoremContract
craftSourceContract = Bridge.republicCraftContract

rightOpinionSourceContract : Bridge.LeanPhilosophyTheoremContract
rightOpinionSourceContract = Bridge.rightOpinionContract

------------------------------------------------------------------------
-- 1. Shared ascent-shaped carrier does not identify semantics.
------------------------------------------------------------------------

data AscentReadingWorld : Set where
  jmdPlatonicAscentReading : AscentReadingWorld
  dashiRefinementReading : AscentReadingWorld

data SharedAscentCarrier : Set where
  localToGeneralAscentShape : SharedAscentCarrier

data AscentSemanticQuery : Set where
  ascentSemanticQuestion : AscentSemanticQuery

data AscentSemanticAnswer : Set where
  erosBeautyFormSemantics : AscentSemanticAnswer
  consumerRefinementSemantics : AscentSemanticAnswer

sharedAscentProjection : AscentReadingWorld → SharedAscentCarrier
sharedAscentProjection jmdPlatonicAscentReading = localToGeneralAscentShape
sharedAscentProjection dashiRefinementReading = localToGeneralAscentShape

AscentAnswerFor : AscentSemanticQuery → Set
AscentAnswerFor ascentSemanticQuestion = AscentSemanticAnswer

askAscentSemantics :
  (query : AscentSemanticQuery) →
  AscentReadingWorld →
  AscentAnswerFor query
askAscentSemantics ascentSemanticQuestion jmdPlatonicAscentReading =
  erosBeautyFormSemantics
askAscentSemantics ascentSemanticQuestion dashiRefinementReading =
  consumerRefinementSemantics

ascentQuestions : Query.InquiryQuestionFamily AscentReadingWorld AscentSemanticQuery
ascentQuestions = Query.inquiryQuestionFamily AscentAnswerFor askAscentSemantics

sharedAscentCarrierDoesNotDetermineSemantics :
  Query.FactorsThrough
    ascentQuestions
    sharedAscentProjection
    ascentSemanticQuestion → ⊥
sharedAscentCarrierDoesNotDetermineSemantics factor = helper first second
  where
    first :
      erosBeautyFormSemantics
      ≡ Query.quotientAnswer factor localToGeneralAscentShape
    first = Query.factorisation factor jmdPlatonicAscentReading

    second :
      consumerRefinementSemantics
      ≡ Query.quotientAnswer factor localToGeneralAscentShape
    second = Query.factorisation factor dashiRefinementReading

    helper :
      erosBeautyFormSemantics
      ≡ Query.quotientAnswer factor localToGeneralAscentShape →
      consumerRefinementSemantics
      ≡ Query.quotientAnswer factor localToGeneralAscentShape →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- 2. Same role authority does not determine who the practice serves.
------------------------------------------------------------------------

data RulingPracticeWorld : Set where
  subjectServingRuling : RulingPracticeWorld
  operatorServingRuling : RulingPracticeWorld

data RoleAuthoritySurface : Set where
  sameRulerRole : RoleAuthoritySurface

data ServiceOrientationQuery : Set where
  serviceOrientationQuestion : ServiceOrientationQuery

data ServiceOrientationAnswer : Set where
  servesRuledOrSubject : ServiceOrientationAnswer
  servesOperatorOrRuler : ServiceOrientationAnswer

roleAuthorityProjection : RulingPracticeWorld → RoleAuthoritySurface
roleAuthorityProjection subjectServingRuling = sameRulerRole
roleAuthorityProjection operatorServingRuling = sameRulerRole

ServiceOrientationAnswerFor : ServiceOrientationQuery → Set
ServiceOrientationAnswerFor serviceOrientationQuestion = ServiceOrientationAnswer

askServiceOrientation :
  (query : ServiceOrientationQuery) →
  RulingPracticeWorld →
  ServiceOrientationAnswerFor query
askServiceOrientation serviceOrientationQuestion subjectServingRuling =
  servesRuledOrSubject
askServiceOrientation serviceOrientationQuestion operatorServingRuling =
  servesOperatorOrRuler

serviceOrientationQuestions :
  Query.InquiryQuestionFamily RulingPracticeWorld ServiceOrientationQuery
serviceOrientationQuestions =
  Query.inquiryQuestionFamily ServiceOrientationAnswerFor askServiceOrientation

roleAuthorityDoesNotDetermineServiceOrientation :
  Query.FactorsThrough
    serviceOrientationQuestions
    roleAuthorityProjection
    serviceOrientationQuestion → ⊥
roleAuthorityDoesNotDetermineServiceOrientation factor = helper first second
  where
    first :
      servesRuledOrSubject
      ≡ Query.quotientAnswer factor sameRulerRole
    first = Query.factorisation factor subjectServingRuling

    second :
      servesOperatorOrRuler
      ≡ Query.quotientAnswer factor sameRulerRole
    second = Query.factorisation factor operatorServingRuling

    helper :
      servesRuledOrSubject
      ≡ Query.quotientAnswer factor sameRulerRole →
      servesOperatorOrRuler
      ≡ Query.quotientAnswer factor sameRulerRole →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- 3. Diotima middle-state / DASHI epistemic-trit calibration without identity.
------------------------------------------------------------------------

record EpistemicMiddleCrosswalk : Set where
  constructor epistemic-middle-crosswalk
  field
    sourceContract : Bridge.LeanPhilosophyTheoremContract
    dashiAnalogue : Trit.EpistemicTrit
    sharedStructuralRole : String
    semanticIdentityClaimed : Bool

open EpistemicMiddleCrosswalk public

canonicalEpistemicMiddleCrosswalk : EpistemicMiddleCrosswalk
canonicalEpistemicMiddleCrosswalk =
  epistemic-middle-crosswalk
    rightOpinionSourceContract
    Trit.unresolved
    "both preserve room between two determinate endpoints; Diotima right opinion concerns a source-specific epistemic category, while DASHI unresolved is an evidence-state constructor"
    false

------------------------------------------------------------------------
-- Attribution / semantic-firewall boundary.
------------------------------------------------------------------------

record PlatoSymposiumCompletionBoundary : Set where
  constructor plato-symposium-completion-boundary
  field
    sameAscentCarrierMeansSameSemantics : Bool
    roleAuthorityDeterminesServiceOrientation : Bool
    rightOpinionEqualsDashiUnresolvedEvidence : Bool
    jmdLeanOwnsDashiFactorisationTheorems : Bool
    jmdCraftArgumentProvesModernInstitutionalDesign : Bool
    dashiRefinementIsPlatonicAscent : Bool
    structuralCrossPollinationRetainsSourceGrammar : Bool

open PlatoSymposiumCompletionBoundary public

canonicalPlatoSymposiumCompletionBoundary : PlatoSymposiumCompletionBoundary
canonicalPlatoSymposiumCompletionBoundary =
  plato-symposium-completion-boundary
    false
    false
    false
    false
    false
    false
    true
