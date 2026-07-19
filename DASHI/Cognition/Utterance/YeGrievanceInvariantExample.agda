module DASHI.Cognition.Utterance.YeGrievanceInvariantExample where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (refl)
open import Data.List.Base using ([]; _∷_)

open import DASHI.Cognition.Utterance.LayeredMeaningCore
open import DASHI.Cognition.Utterance.AdmissibilityGate

------------------------------------------------------------------------
-- Bounded worked example.  This module formalizes only the visible surface,
-- typed referent candidates, promotion boundaries, and a candidate invariant.
-- It makes no clinical diagnosis and no itemwise betrayal claim.
------------------------------------------------------------------------

postSurface : SourceSurface
postSurface =
  sourceSurface
    "screenshot_of_post"
    "Ye"
    ("I AM IN PAIN THAT NO ONE PERSON CAN FIX"
      ∷ "THE BETRAYAL"
      ∷ "heterogeneous enumeration follows"
      ∷ [])
    emptyEvidenceChain

painAtom : TextAtom postSurface
painAtom = textAtom "I AM IN PAIN THAT NO ONE PERSON CAN FIX"

betrayalFrameAtom : TextAtom postSurface
betrayalFrameAtom = textAtom "THE BETRAYAL"

rawEnumeration : EnumerationAtom postSurface
rawEnumeration =
  enumerationAtom
    ("Kim Kardashian"
      ∷ "North West"
      ∷ "Diddy"
      ∷ "Ty$"
      ∷ "Harriet Tubman"
      ∷ "Curious George"
      ∷ "Patrick Star"
      ∷ [])

ye : TypedReferent
ye = typedReferent "Ye" "Q36153" "Q5" liveHuman "self"
  (collaboratorRupture ∷ industryRupture ∷ [])

kim : TypedReferent
kim = typedReferent "Kim Kardashian" "Q1863044" "Q5" liveHuman
  "former spouse" (familyRupture ∷ [])

north : TypedReferent
north = typedReferent "North West" "Q16237278" "Q5" minorHuman
  "child" (familyRupture ∷ [])

diddy : TypedReferent
diddy = typedReferent "Diddy" "Q193138" "Q5" liveHuman
  "music-industry peer" (industryRupture ∷ [])

tyDollar : TypedReferent
tyDollar = typedReferent "Ty$" "Q15258596" "Q5" liveHuman
  "collaborator" (collaboratorRupture ∷ [])

harriet : TypedReferent
harriet = typedReferent "Harriet Tubman" "Q102049" "Q5" historicalPersonDeceased
  "no direct relation encoded" (racialHistoricalRupture ∷ [])

curiousGeorge : TypedReferent
curiousGeorge = typedReferent "Curious George" "candidate-only" "Q15773347"
  fictionalCharacter "no direct relation" (childhoodSymbolRupture ∷ memeRupture ∷ [])

patrickStar : TypedReferent
patrickStar = typedReferent "Patrick Star" "Q170363" "Q15773347"
  fictionalCharacter "no direct relation" (absurdityRupture ∷ memeRupture ∷ [])

painCandidate : DerivedCandidate postSurface
painCandidate =
  derivedCandidate
    "self-pain-expression"
    (painAtom ∷ [])
    explicitGrammar
    true
    refl

betrayalFrameCandidate : DerivedCandidate postSurface
betrayalFrameCandidate =
  derivedCandidate
    "betrayal-frame-over-adjacent-enumeration"
    (betrayalFrameAtom ∷ [])
    layoutAdjacency
    true
    refl

postQualifiers : QualifierState
postQualifiers =
  qualifierState "asserted_surface" "observed_text_only" "present_surface" "positive_assertion"

postWrapper : WrapperState
postWrapper =
  wrapperState
    emptyEvidenceChain
    literalBlocked
    symbolicAdmissible
    false
    refl

postPNF : PredicatePNF postSurface
postPNF =
  predicatePNF
    "EXPRESS_SURFACE"
    ye
    postSurface
    betrayalFrameCandidate
    (kim ∷ north ∷ diddy ∷ tyDollar ∷ harriet ∷ curiousGeorge ∷ patrickStar ∷ [])
    postQualifiers
    postWrapper

curiousGeorgeLiteralAttempt : LiteralPromotionAttempt
curiousGeorgeLiteralAttempt =
  literalPromotionAttempt
    "betrayed"
    curiousGeorge
    ye
    canonicalLiteralBlockingGrounds
    literalBlocked
    refl

curiousGeorgeSymbolicAnchor : SymbolicAnchor
curiousGeorgeSymbolicAnchor =
  admitSymbolicAnchor curiousGeorge
    (symbolicAdmissionProof memeRupture alienation "typed childhood/meme referent under pain and betrayal frame")

kimRupture : RuptureAnchor
kimRupture = ruptureAnchor ye kim "former spouse" familyRupture betrayal

northRupture : RuptureAnchor
northRupture = ruptureAnchor ye north "child" familyRupture pain

diddyRupture : RuptureAnchor
diddyRupture = ruptureAnchor ye diddy "industry peer" industryRupture betrayal

tyRupture : RuptureAnchor
tyRupture = ruptureAnchor ye tyDollar "collaborator" collaboratorRupture betrayal

harrietRupture : RuptureAnchor
harrietRupture = ruptureAnchor ye harriet "historical-symbolic reference" racialHistoricalRupture alienation

curiousRupture : RuptureAnchor
curiousRupture = ruptureAnchor ye curiousGeorge "childhood/meme reference" memeRupture alienation

patrickRupture : RuptureAnchor
patrickRupture = ruptureAnchor ye patrickStar "absurdity/meme reference" absurdityRupture alienation

integratedSelfWorldRuptureCandidate : InvariantExtraction postSurface
integratedSelfWorldRuptureCandidate =
  invariantExtraction
    postPNF
    (kimRupture ∷ northRupture ∷ diddyRupture ∷ tyRupture ∷ harrietRupture ∷ curiousRupture ∷ patrickRupture ∷ [])
    "IntegratedSelfWorldRupture / loss_of_integrated_world"
    "For each anchor, recover the world-supporting relation it represented; compare historically evidenced rupture-to-form transformations without treating the candidate as diagnosis or instruction."
    true
    refl
    false
    refl
