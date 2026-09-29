module DASHI.Core.IndexedRelationalHyperfabricSpineExact where

-- DASHI mathematical owner: B^k indexed carriers, dependent fibres,
-- observer factorisation, collision-driven refinement and guarded gluing.
-- This module is not a legal ontology, nor a claim about any named
-- philosophy, Indigenous authority, or particular normative system.
--
-- B is arbitrary. For B = Fin 3 the site count is 3^k; for a carrier
-- of 3*n distinct elements it is (3*n)^k, NOT 3^(n*k) unless the
-- typed carrier is actually a product with that cardinality.
-- Cartesian growth differs from self-indexing function-space towers.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Indexed
import DASHI.Core.QueryIndexedProjectionSpineAdapterExact as Spine
import DASHI.Core.AdmissibleTransitionHyperfabricExact as Transitions
import DASHI.Biology.TernaryHypercubeHyperfabricExact as Counts

-- Entire ontology supplies the carrier B; no C/T/P baked into core.
Address : (B : Set) → Nat → Set
Address B k = Vec B k

-- A dependent fibre is attached to each *full* hypervoxel address.
record IndexedFabric (B : Set) (k : Nat) : Set₁ where
  field
    Fibre : Address B k → Set
    -- Source history, legal standing and permission are supplied by clients,
    -- never inferred from a naked address.
    originReference : String

  Situated : Set
  Situated = Σ (Address B k) Fibre

open IndexedFabric public

readAddress : ∀ {B k} (fabric : IndexedFabric B k) →
  Situated fabric → Address B k
readAddress fabric (address , fibre) = address

-- Changing address resolution without erasing the previous state:
-- the canonical one-step refinement adds a newly typed coordinate.
prepend : ∀ {B k} → B → Address B k → Address B (suc k)
prepend axis rest = axis ∷ rest

forgetLeading : ∀ {B k} → Address B (suc k) → Address B k
forgetLeading (axis ∷ rest) = rest

retainedSuffix : ∀ {B k} (axis : B) (address : Address B k) →
  forgetLeading (prepend axis address) ≡ address
retainedSuffix axis address = refl

-- This is the existing intersectional / query-indexed adequacy spine,
-- not a new competing factorisation definition.
ConsumerSufficient :
  ∀ {State View Answer : Set} →
  (State → View) → (State → Answer) → Set₁
ConsumerSufficient = NF.FactorsThrough

ConsumerCollision :
  ∀ {State View Answer : Set} →
  (State → View) → (State → Answer) → Set₁
ConsumerCollision = NF.NonFactorabilityWitness

collisionRefutesSufficiency :
  ∀ {State View Answer : Set}
    {observe : State → View} {answer : State → Answer} →
  ConsumerCollision observe answer →
  ConsumerSufficient observe answer → ⊥
collisionRefutesSufficiency =
  NF.witnessRulesOutEveryFlatFactorisation

collisionSurvivesRechart :
  ∀ {State View Rechart Answer : Set}
    {observe : State → View} {answer : State → Answer} →
  (chart : View → Rechart) →
  ConsumerCollision observe answer →
  ConsumerSufficient (λ state → chart (observe state)) answer → ⊥
collisionSurvivesRechart = NF.rechartingCannotRecoverErasedPhenomenon

-- A genuine *family* of queries is provided by the consumer; tests must
-- preserve that exact query, not assert the projection is adequate globally.
AdequateFor :
  ∀ {State View Query Answer : Set} →
  (State → View) → Indexed.QuerySemantics State Query Answer →
  Query → Set₁
AdequateFor = Indexed.AdequateFor

-- Legal and ethical admissibility is a second independent requirement.
record AdmissibleObservation
    {State View Answer : Set}
    (observe : State → View)
    (answer : State → Answer) : Set₁ where
  field
    adequate : ConsumerSufficient observe answer
    AuthorityEvidence : Set
    authorityEvidence : AuthorityEvidence
    SourceEvidence : Set
    sourceEvidence : SourceEvidence

-- A source-sensitive gluing operator must pay compatibility proofs;
-- mere equal/related labels do not imply valid fibre composition.
record GuardedGluing
    {B : Set} {k l : Nat}
    (left : IndexedFabric B k)
    (right : IndexedFabric B l) : Set₁ where
  field
    Interface : Set
    sharedInterface : Interface
    Compatible : Interface → Set
    compatible : Compatible sharedInterface
    glueOutput : Set
    glue : Situated left → Situated right → glueOutput
    traceReference : String

-- Core representation-count provenance: existing generic powNat.
siteCount : Nat → Nat → Nat
siteCount base k = Counts.powNat base k

threeAxis9 : siteCount 3 2 ≡ 9
threeAxis9 = refl

threeAxis27 : siteCount 3 3 ≡ 27
threeAxis27 = refl

threeAxis81 : siteCount 3 4 ≡ 81
threeAxis81 = refl

threeTimesTwoAtDepthTwo : siteCount (3 * 2) 2 ≡ 36
threeTimesTwoAtDepthTwo = refl

-- Function spaces require another constructor; NOT what Address B k is.
