module DASHI.Interop.ZelphFiniteQueryWordClosureExact where

-- A2 constructive finite word theorem: one-hop equalities along the actually
-- reached source frontiers imply equality of full relation-word answers.
-- Caller MUST construct those equalities from original/selected physical
-- source rows. This theorem alone does not authenticate the HF graph.

open import DASHI.Core.Prelude

data QueryDirection : Set where
  left right : QueryDirection

-- State is a frontier (e.g. a finite set of numeric Zelph nodes), not a
-- single node: adjacency may be multivalued.
runRelationWord :
  {State : Set} →
  (QueryDirection → State → State) →
  State → List QueryDirection → State
runRelationWord transition state [] = state
runRelationWord transition state (direction ∷ rest) =
  runRelationWord transition (transition direction state) rest

-- Only source-reachable transitions need to be checked. A static list of
-- property names does not constitute a dependent boundary certificate.
data SourceReachableBoundary
  {State : Set}
  (original selected : QueryDirection → State → State) :
  State → List QueryDirection → Set where
  emptyWordBoundary :
    (state : State) →
    SourceReachableBoundary original selected state []
  nextWordBoundary :
    (state : State) (direction : QueryDirection)
    (rest : List QueryDirection) →
    original direction state ≡ selected direction state →
    SourceReachableBoundary original selected (original direction state) rest →
    SourceReachableBoundary original selected state (direction ∷ rest)

zelphSelectedWordAnswerEqualsOriginal :
  {State : Set}
  {original selected : QueryDirection → State → State} →
  {state : State} {word : List QueryDirection} →
  SourceReachableBoundary original selected state word →
  runRelationWord original state word ≡ runRelationWord selected state word
zelphSelectedWordAnswerEqualsOriginal (emptyWordBoundary state) = refl
zelphSelectedWordAnswerEqualsOriginal
  {selected = selected}
  (nextWordBoundary state direction rest same nextBoundary) =
  trans (zelphSelectedWordAnswerEqualsOriginal nextBoundary)
        (cong (λ frontier → runRelationWord selected frontier rest) same)

-- Unlike QueryFamilyClosure.edgeClosure, this theorem asks for local
-- source-reachable *one-step* equality certificates, then constructs
-- equality of the complete declared query word inductively.
zelphFiniteQueryFamilyBoundaryClosed :
  {State Query : Set}
  {original selected : QueryDirection → State → State} →
  (root : Query → State) →
  (word : Query → List QueryDirection) →
  (InFamily : Query → Set) →
  ((query : Query) → InFamily query →
    SourceReachableBoundary original selected (root query) (word query)) →
  (query : Query) → InFamily query →
  runRelationWord original (root query) (word query)
  ≡ runRelationWord selected (root query) (word query)
zelphFiniteQueryFamilyBoundaryClosed root word InFamily boundary query within =
  zelphSelectedWordAnswerEqualsOriginal (boundary query within)
