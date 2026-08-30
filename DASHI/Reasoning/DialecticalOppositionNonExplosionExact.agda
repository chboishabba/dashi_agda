module DASHI.Reasoning.DialecticalOppositionNonExplosionExact where

------------------------------------------------------------------------
-- DIALECTICAL OPPOSITION / NON-EXPLOSION BOUNDARY
--
-- This module makes precise three distinctions already present elsewhere in
-- the repository:
--
--   * an observation is indexed by its representation context;
--   * binary forcing of EpistemicTrit loses the unresolved/contradicted
--     distinction;
--   * a dialectical counterposition is a construction, not definitionally
--     the same thing as logical negation, orientation reversal, or inverse.
--
-- The point is NOT to disable ordinary constructive explosion.  If a genuine
-- contradiction P × ¬ P is available, ⊥-elimination remains valid.  The point
-- is that context difference, non-support, unresolved construction, or an
-- invalid opposite-construction do not manufacture that contradiction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Ontology.EpistemicTrit as Epistemic

------------------------------------------------------------------------
-- 1. Context-indexed observation: true(here) need not be true(there).
------------------------------------------------------------------------

data ObservationContext : Set where
  here there : ObservationContext

data ScopedClaim : Set where
  focalClaim : ScopedClaim

contextualTruth : ObservationContext → ScopedClaim → Bool
contextualTruth here  focalClaim = true
contextualTruth there focalClaim = false

true≢false : ¬ (true ≡ false)
true≢false ()

sameClaimDifferentContext :
  ¬ (contextualTruth here focalClaim ≡ contextualTruth there focalClaim)
sameClaimDifferentContext = true≢false

record ContextualEpistemicReport : Set where
  constructor report
  field
    context : ObservationContext
    claim : ScopedClaim
    state : Epistemic.EpistemicTrit

open ContextualEpistemicReport public

canonicalHereReport : ContextualEpistemicReport
canonicalHereReport = report here focalClaim Epistemic.supported

canonicalThereReport : ContextualEpistemicReport
canonicalThereReport = report there focalClaim Epistemic.unresolved

sameClaimAcrossReports :
  claim canonicalHereReport ≡ claim canonicalThereReport
sameClaimAcrossReports = refl

differentContextsAcrossReports :
  ¬ (context canonicalHereReport ≡ context canonicalThereReport)
differentContextsAcrossReports ()

------------------------------------------------------------------------
-- 2. Binary forcing is a quotient, not a falsity certificate.
------------------------------------------------------------------------

unresolvedAndContradictedCollapseUnderRejectForcing :
  Epistemic.forceUnresolvedToReject Epistemic.unresolved ≡
  Epistemic.forceUnresolvedToReject Epistemic.contradicted
unresolvedAndContradictedCollapseUnderRejectForcing =
  Epistemic.rejectPolicyCollision

unresolvedAndSupportedCollapseUnderAcceptForcing :
  Epistemic.forceUnresolvedToAccept Epistemic.unresolved ≡
  Epistemic.forceUnresolvedToAccept Epistemic.supported
unresolvedAndSupportedCollapseUnderAcceptForcing =
  Epistemic.acceptPolicyCollision

------------------------------------------------------------------------
-- 3. Different notions of "opposite" remain differently typed/tagged.
------------------------------------------------------------------------

data OppositionMode : Set where
  logicalNegation : OppositionMode
  constructedCounterposition : OppositionMode
  orientationReversal : OppositionMode
  algebraicInverse : OppositionMode

counterposition≢negation :
  ¬ (constructedCounterposition ≡ logicalNegation)
counterposition≢negation ()

reversal≢negation :
  ¬ (orientationReversal ≡ logicalNegation)
reversal≢negation ()

inverse≢negation :
  ¬ (algebraicInverse ≡ logicalNegation)
inverse≢negation ()

counterposition≢reversal :
  ¬ (constructedCounterposition ≡ orientationReversal)
counterposition≢reversal ()

counterposition≢inverse :
  ¬ (constructedCounterposition ≡ algebraicInverse)
counterposition≢inverse ()

------------------------------------------------------------------------
-- 4. Opposition is partial at the construction layer.
------------------------------------------------------------------------

data ConstructionResult (A : Set) : Set where
  constructed : A → ConstructionResult A
  unresolvedConstruction : ConstructionResult A
  invalidConstruction : ConstructionResult A

data HasConstructedWitness {A : Set} : ConstructionResult A → Set where
  witness : (x : A) → HasConstructedWitness (constructed x)

unresolvedHasNoConstructedWitness :
  {A : Set} →
  ¬ HasConstructedWitness {A} unresolvedConstruction
unresolvedHasNoConstructedWitness ()

invalidHasNoConstructedWitness :
  {A : Set} →
  ¬ HasConstructedWitness {A} invalidConstruction
invalidHasNoConstructedWitness ()

data DialecticalPosition : Set where
  thesis : DialecticalPosition
  nontrivialCounterposition : DialecticalPosition

canonicalConstructedCounterposition : ConstructionResult DialecticalPosition
canonicalConstructedCounterposition = constructed nontrivialCounterposition

canonicalUnresolvedOpposition : ConstructionResult DialecticalPosition
canonicalUnresolvedOpposition = unresolvedConstruction

canonicalInvalidOpposition : ConstructionResult DialecticalPosition
canonicalInvalidOpposition = invalidConstruction

------------------------------------------------------------------------
-- 5. Ordinary explosion remains available only after a genuine same-frame
--    contradiction has actually been constructed.
------------------------------------------------------------------------

Contradiction : Set → Set
Contradiction P = P × ¬ P

explode : {P Q : Set} → Contradiction P → Q
explode (_ , notP) = ⊥-elim (notP _)

-- A concrete inhabited proposition witnesses why arbitrary context-indexed
-- reports cannot generically be re-read as a logical contradiction.
-- If such a generic extractor existed, applying it to the canonical pair of
-- reports would produce ⊤ × ¬ ⊤ and hence bottom.

record HereThereReports : Set where
  constructor hereThereReports
  field
    hereSide : ContextualEpistemicReport
    thereSide : ContextualEpistemicReport

canonicalHereThereReports : HereThereReports
canonicalHereThereReports =
  hereThereReports canonicalHereReport canonicalThereReport

noGenericContradictionFromContextReports :
  ¬ (HereThereReports → Contradiction ⊤)
noGenericContradictionFromContextReports extractContradiction =
  let contradiction = extractContradiction canonicalHereThereReports
  in proj₂ contradiction tt

------------------------------------------------------------------------
-- 6. A small boundary receipt summarises what this theorem layer certifies.
------------------------------------------------------------------------

record DialecticalOppositionBoundary : Set where
  constructor dialecticalOppositionBoundary
  field
    contextDifferenceIsLogicalContradiction : Bool
    unresolvedIsRefutation : Bool
    counterpositionDefinitionallyIsNegation : Bool
    reversalDefinitionallyIsNegation : Bool
    inverseDefinitionallyIsNegation : Bool
    invalidConstructionProducesCounterposition : Bool
    genuineContradictionStillExplodes : Bool

canonicalDialecticalOppositionBoundary : DialecticalOppositionBoundary
canonicalDialecticalOppositionBoundary =
  dialecticalOppositionBoundary
    false
    false
    false
    false
    false
    false
    true
