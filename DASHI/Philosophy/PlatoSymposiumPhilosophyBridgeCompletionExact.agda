module DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeCompletionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Ontology.EpistemicTrit as Trit
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Bridge
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.PlatoSymposiumDialecticBraidHyperformalExact as Hyperformal

------------------------------------------------------------------------
-- COMPLETION SEAMS FOR THE JMD PLATO PHILOSOPHY BRIDGE
--
-- Parent owners already pay:
--   * Bridge: lack/seeking, right-opinion/ignorance, complementarity/relation,
--     appearance/interior and consensus/plural-state non-collapse;
--   * Hyperformal: same ascent shape != same semantic grammar, plus the
--     Aristophanes/DASHI involution-shape semantic firewall.
--
-- Therefore this file does NOT re-prove the ascent theorem.  It imports that
-- exact owner and adds only the remaining Republic role/service-orientation
-- theorem plus an explicit Diotima-middle <-> DASHI epistemic-trit calibration
-- that refuses semantic identity.
------------------------------------------------------------------------

existingBridgeRetained : Bool
existingBridgeRetained = true

sourceArchiveHash : String
sourceArchiveHash = Source.archiveSha256

craftSourceContract : Bridge.LeanPhilosophyTheoremContract
craftSourceContract = Bridge.republicCraftContract

rightOpinionSourceContract : Bridge.LeanPhilosophyTheoremContract
rightOpinionSourceContract = Bridge.rightOpinionContract

------------------------------------------------------------------------
-- 1. Reuse the already-owned ascent semantic-separation theorem.
------------------------------------------------------------------------

ascentSemanticSeparationReuse :
  Query.FactorsThrough
    Hyperformal.ascentMeaningQuestions
    Hyperformal.ascentShapeProjection
    Hyperformal.ascentMeaningQuestion → ⊥
ascentSemanticSeparationReuse =
  Hyperformal.sharedAscentShapeDoesNotDetermineSemantics

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
    "both preserve room between two determinate endpoints; Diotima right opinion is a source-specific epistemic category, while DASHI unresolved is a scoped evidence-state constructor"
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
    ascentTheoremWasReprovedInsteadOfReused : Bool
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
    false
    true
