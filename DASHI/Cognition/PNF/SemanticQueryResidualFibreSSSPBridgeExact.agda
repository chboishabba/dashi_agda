module DASHI.Cognition.PNF.SemanticQueryResidualFibreSSSPBridgeExact where

-- BIDI weld between the SSSP consumer-quotient lane and the existing PNF
-- alternative-fibre semantics.
--
-- A semantic world is not selected merely because the current query cannot
-- distinguish it from another admissible world.  The current observation is
-- a consumer quotient; the unresolved alternatives remain upstairs and may
-- split under a later, finer query.

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl; cong; trans; sym)
open import Agda.Builtin.String using (String)
open import Relation.Nullary using (¬_)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Cognition.PNF.EventAlgebra as PNF
import DASHI.Computation.SSSPConsumerInvariantSymmetryQuotientExact as SSSP

------------------------------------------------------------------------
-- 1. Bridge shape over the existing PNF AlternativeFibre carrier.
------------------------------------------------------------------------

record PNFQueryFibreBridge : Set₁ where
  constructor pnfQueryFibreBridge
  field
    sourceFibre : PNF.AlternativeFibre
    World Query Observation : Set
    worldCandidate : World → PNF.CandidatePNF
    observe : Query → World → Observation

    queryEquivalent : Query → World → World → Set
    queryEquivalentSound :
      (q : Query) (x y : World) →
      queryEquivalent q x y →
      observe q x ≡ observe q y

open PNFQueryFibreBridge public

------------------------------------------------------------------------
-- 2. Query-indexed stabiliser/action.
--
-- The symmetry that is invisible to one query need not remain invisible to a
-- later query.  Consequently the stabiliser is indexed by the query.
------------------------------------------------------------------------

record QueryIndexedSymmetrySystem : Set₁ where
  constructor queryIndexedSymmetrySystem
  field
    World Query Observation : Set
    Symmetry : Query → Set

    identity : (q : Query) → Symmetry q
    compose : (q : Query) → Symmetry q → Symmetry q → Symmetry q
    act : (q : Query) → Symmetry q → World → World
    observe : Query → World → Observation

    identityActs :
      (q : Query) (x : World) → act q (identity q) x ≡ x

    actionComposes :
      (q : Query) (g h : Symmetry q) (x : World) →
      act q (compose q g h) x ≡ act q g (act q h x)

    observerInvariant :
      (q : Query) (g : Symmetry q) (x : World) →
      observe q (act q g x) ≡ observe q x

open QueryIndexedSymmetrySystem public

record SameQueryOrbit
  (S : QueryIndexedSymmetrySystem)
  (q : Query S)
  (x y : World S) : Set where
  constructor sameQueryOrbit
  field
    symmetryWitness : Symmetry S q
    actionWitness : act S q symmetryWitness x ≡ y

open SameQueryOrbit public

sameQueryOrbitIsObservationEquivalent :
  (S : QueryIndexedSymmetrySystem) →
  (q : Query S) →
  (x y : World S) →
  SameQueryOrbit S q x y →
  observe S q x ≡ observe S q y
sameQueryOrbitIsObservationEquivalent S q x y orbit =
  trans
    (sym (observerInvariant S q (symmetryWitness orbit) x))
    (cong (observe S q) (actionWitness orbit))

------------------------------------------------------------------------
-- 3. Exact two-world refinement regression.
--
-- A coarse identity-like query does not distinguish the canonical referent
-- from an impersonator/reference alternative.  A later provenance query does.
-- The underlying worlds do not change; only the query stabiliser shrinks.
------------------------------------------------------------------------

data ExampleWorld : Set where
  canonicalReferent impersonatorReferent : ExampleWorld

data ExampleQuery : Set where
  coarseIdentityQuery provenanceQuery : ExampleQuery

data CoarseSymmetry : Set where
  coarseIdentity coarseSwap : CoarseSymmetry

data ProvenanceSymmetry : Set where
  provenanceIdentity : ProvenanceSymmetry

ExampleSymmetry : ExampleQuery → Set
ExampleSymmetry coarseIdentityQuery = CoarseSymmetry
ExampleSymmetry provenanceQuery = ProvenanceSymmetry

exampleIdentity : (q : ExampleQuery) → ExampleSymmetry q
exampleIdentity coarseIdentityQuery = coarseIdentity
exampleIdentity provenanceQuery = provenanceIdentity

exampleCompose :
  (q : ExampleQuery) → ExampleSymmetry q → ExampleSymmetry q → ExampleSymmetry q
exampleCompose coarseIdentityQuery coarseIdentity h = h
exampleCompose coarseIdentityQuery coarseSwap coarseIdentity = coarseSwap
exampleCompose coarseIdentityQuery coarseSwap coarseSwap = coarseIdentity
exampleCompose provenanceQuery provenanceIdentity provenanceIdentity = provenanceIdentity

exampleAct :
  (q : ExampleQuery) → ExampleSymmetry q → ExampleWorld → ExampleWorld
exampleAct coarseIdentityQuery coarseIdentity x = x
exampleAct coarseIdentityQuery coarseSwap canonicalReferent = impersonatorReferent
exampleAct coarseIdentityQuery coarseSwap impersonatorReferent = canonicalReferent
exampleAct provenanceQuery provenanceIdentity x = x

exampleObserve : ExampleQuery → ExampleWorld → Trit
exampleObserve coarseIdentityQuery canonicalReferent = zer
exampleObserve coarseIdentityQuery impersonatorReferent = zer
exampleObserve provenanceQuery canonicalReferent = pos
exampleObserve provenanceQuery impersonatorReferent = neg

exampleIdentityActs :
  (q : ExampleQuery) (x : ExampleWorld) →
  exampleAct q (exampleIdentity q) x ≡ x
exampleIdentityActs coarseIdentityQuery canonicalReferent = refl
exampleIdentityActs coarseIdentityQuery impersonatorReferent = refl
exampleIdentityActs provenanceQuery canonicalReferent = refl
exampleIdentityActs provenanceQuery impersonatorReferent = refl

exampleActionComposes :
  (q : ExampleQuery) (g h : ExampleSymmetry q) (x : ExampleWorld) →
  exampleAct q (exampleCompose q g h) x ≡
  exampleAct q g (exampleAct q h x)
exampleActionComposes coarseIdentityQuery coarseIdentity coarseIdentity x = refl
exampleActionComposes coarseIdentityQuery coarseIdentity coarseSwap x = refl
exampleActionComposes coarseIdentityQuery coarseSwap coarseIdentity x = refl
exampleActionComposes coarseIdentityQuery coarseSwap coarseSwap canonicalReferent = refl
exampleActionComposes coarseIdentityQuery coarseSwap coarseSwap impersonatorReferent = refl
exampleActionComposes provenanceQuery provenanceIdentity provenanceIdentity x = refl

exampleObserverInvariant :
  (q : ExampleQuery) (g : ExampleSymmetry q) (x : ExampleWorld) →
  exampleObserve q (exampleAct q g x) ≡ exampleObserve q x
exampleObserverInvariant coarseIdentityQuery coarseIdentity x = refl
exampleObserverInvariant coarseIdentityQuery coarseSwap canonicalReferent = refl
exampleObserverInvariant coarseIdentityQuery coarseSwap impersonatorReferent = refl
exampleObserverInvariant provenanceQuery provenanceIdentity x = refl

exampleQuerySystem : QueryIndexedSymmetrySystem
exampleQuerySystem =
  queryIndexedSymmetrySystem
    ExampleWorld
    ExampleQuery
    Trit
    ExampleSymmetry
    exampleIdentity
    exampleCompose
    exampleAct
    exampleObserve
    exampleIdentityActs
    exampleActionComposes
    exampleObserverInvariant

coarseWorldsSameOrbit :
  SameQueryOrbit
    exampleQuerySystem coarseIdentityQuery
    canonicalReferent impersonatorReferent
coarseWorldsSameOrbit = sameQueryOrbit coarseSwap refl

coarseWorldsObservationEqual :
  exampleObserve coarseIdentityQuery canonicalReferent ≡
  exampleObserve coarseIdentityQuery impersonatorReferent
coarseWorldsObservationEqual =
  sameQueryOrbitIsObservationEquivalent
    exampleQuerySystem coarseIdentityQuery
    canonicalReferent impersonatorReferent coarseWorldsSameOrbit

provenanceWorldsSeparate :
  ¬ (exampleObserve provenanceQuery canonicalReferent ≡
     exampleObserve provenanceQuery impersonatorReferent)
provenanceWorldsSeparate ()

------------------------------------------------------------------------
-- 4. SSSP correspondence receipt.
--
-- The imported SSSP theorem has the same abstract law: an action-related pair
-- may share one consumer observation without becoming equal fine states.
------------------------------------------------------------------------

record SemanticSSSPQuotientBoundary : Set where
  constructor semanticSSSPQuotientBoundary
  field
    currentQueryMayCollapseFineWorlds : Bool
    currentQueryMayCollapseFineWorldsIsTrue :
      currentQueryMayCollapseFineWorlds ≡ true

    laterQueryMaySplitResidualFibre : Bool
    laterQueryMaySplitResidualFibreIsTrue :
      laterQueryMaySplitResidualFibre ≡ true

    observationalEqualityImpliesWorldEquality : Bool
    observationalEqualityImpliesWorldEqualityIsFalse :
      observationalEqualityImpliesWorldEquality ≡ false

    querySymmetryIsAutomaticallyPhaseSymmetry : Bool
    querySymmetryIsAutomaticallyPhaseSymmetryIsFalse :
      querySymmetryIsAutomaticallyPhaseSymmetry ≡ false

canonicalSemanticSSSPQuotientBoundary : SemanticSSSPQuotientBoundary
canonicalSemanticSSSPQuotientBoundary =
  semanticSSSPQuotientBoundary
    true refl
    true refl
    false refl
    false refl
