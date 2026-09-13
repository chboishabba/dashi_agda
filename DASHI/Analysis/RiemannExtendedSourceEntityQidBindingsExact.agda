module DASHI.Analysis.RiemannExtendedSourceEntityQidBindingsExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Wikimedia.ScientificReferenceEntityAtlasExact as Atlas

------------------------------------------------------------------------
-- EXTENDED RIEMANN SOURCE IDENTITIES
--
-- These cover source owners outside the de Bruijn-Newman DBNSource enum.
-- Publication identities remain their literal bibliographic/official-source
-- references; QIDs annotate related people only.
------------------------------------------------------------------------

enricoBombieri : Atlas.ScientificReferenceEntity
enricoBombieri = Atlas.verified "Enrico Bombieri" Atlas.personEntity "Q333538" "Wikidata lookup 2026-09-08"

leventAlpoge : Atlas.ScientificReferenceEntity
leventAlpoge = Atlas.verified "Levent Alpoge" Atlas.personEntity "Q102078476" "Wikidata lookup 2026-09-08"

ralphFurman : Atlas.ScientificReferenceEntity
ralphFurman = Atlas.unresolved "Ralph Furman" Atlas.personEntity "no trustworthy Wikidata item resolved in 2026-09-08 audit"

andreWeil : Atlas.ScientificReferenceEntity
andreWeil = Atlas.verified "Andre Weil" Atlas.personEntity "Q323232" "Wikidata lookup 2026-09-08"

richardBorcherds : Atlas.ScientificReferenceEntity
richardBorcherds = Atlas.verified "Richard Borcherds" Atlas.personEntity "Q334010" "Wikidata lookup 2026-09-08"

record ExtendedRiemannSourceBinding : Set where
  constructor extended-riemann-source-binding
  field
    sourceKey : String
    bibliographicIdentity : String
    relatedEntities : List Atlas.ScientificReferenceEntity
    sourceRole : String
open ExtendedRiemannSourceBinding public

riemann1859 : ExtendedRiemannSourceBinding
riemann1859 = extended-riemann-source-binding
  "Riemann1859"
  "Bernhard Riemann, Ueber die Anzahl der Primzahlen unter einer gegebenen Groesse (1859)"
  (Atlas.bernhardRiemann ∷ Atlas.riemannHypothesis ∷ [])
  "foundational source/context"

bombieriClayRH : ExtendedRiemannSourceBinding
bombieriClayRH = extended-riemann-source-binding
  "BombieriClayRH"
  "Clay Mathematics Institute, Problems of the Millennium: The Riemann Hypothesis"
  (enricoBombieri ∷ Atlas.millenniumPrizeProblems ∷ Atlas.riemannHypothesis ∷ [])
  "official problem exposition; no DOI assigned"

alpogeFurmanSimpleZeros : ExtendedRiemannSourceBinding
alpogeFurmanSimpleZeros = extended-riemann-source-binding
  "AlpogeFurmanSimpleZeros"
  "Levent Alpoge and Ralph Furman, More than two thirds of the zeta zeros are simple"
  (leventAlpoge ∷ ralphFurman ∷ Atlas.riemannHypothesis ∷ [])
  "analytic calibration; unresolved coauthor QID remains explicit"

weilExplicitFormula : ExtendedRiemannSourceBinding
weilExplicitFormula = extended-riemann-source-binding
  "WeilExplicitFormula"
  "Andre Weil explicit-formula / positivity source family as cited by the consuming Riemann modules"
  (andreWeil ∷ Atlas.riemannHypothesis ∷ [])
  "source-family identity, not a replacement for each exact paper locator"

borcherdsMoonshine : ExtendedRiemannSourceBinding
borcherdsMoonshine = extended-riemann-source-binding
  "BorcherdsMoonshine"
  "doi:10.1007/BF01232032"
  (richardBorcherds ∷ [])
  "cross-domain Moonshine context; DOI remains publication identity"

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RelatedQidClosesHilbertPolyaBridge : Set where
data BombieriQidIsClayProblemStatement : Set where

qidDoesNotCloseHilbertPolyaBridge : RelatedQidClosesHilbertPolyaBridge → ⊥
qidDoesNotCloseHilbertPolyaBridge ()
bombieriQidDoesNotReplaceClayStatement : BombieriQidIsClayProblemStatement → ⊥
bombieriQidDoesNotReplaceClayStatement ()
