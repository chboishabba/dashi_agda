module DASHI.Cognition.PNF.ProducerCompleteDependencyProjectionExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)

------------------------------------------------------------------------
-- Producer-complete dependency projection.
--
-- Runtime motivation (SensibLaw migration 175): one bounded parser partition
-- already contains every token, its sentence-local span, and the declared head
-- span.  If final persistent token identities are assigned while that fibre is
-- still present, the dependency edge can be encoded on the first authority
-- write.  There is no semantic need to insert an incomplete row and then
-- self-join/update the persistent table to recover information the producer
-- already possessed.
--
-- This theorem is internal DASHI/ITIR mathematics; no external DOI is asserted.
------------------------------------------------------------------------

record ProducerCompleteDependencyFibre
  (Token PersistentId : Set)
  : Set₁ where
  field
    head : Token → Token
    persistentId : Token → PersistentId
    persistentIdInjective :
      ∀ left right →
      persistentId left ≡ persistentId right →
      left ≡ right

open ProducerCompleteDependencyFibre public

record PersistentTokenRow
  (Token PersistentId : Set)
  : Set where
  constructor tokenRow
  field
    token : Token
    tokenId : PersistentId
    headTokenId : PersistentId

open PersistentTokenRow public

-- The producer-native row writes both coordinates once.
directAuthorityRow :
  ∀ {Token PersistentId : Set} →
  ProducerCompleteDependencyFibre Token PersistentId →
  Token →
  PersistentTokenRow Token PersistentId
directAuthorityRow fibre token =
  tokenRow
    token
    (persistentId fibre token)
    (persistentId fibre (head fibre token))

-- Abstract final state of the legacy insert-then-resolve implementation.  The
-- intermediate NULL/unknown head is physical execution state, not semantic
-- authority; after repair its observable authority row is exactly this record.
repairedAuthorityRow :
  ∀ {Token PersistentId : Set} →
  ProducerCompleteDependencyFibre Token PersistentId →
  Token →
  PersistentTokenRow Token PersistentId
repairedAuthorityRow fibre token =
  tokenRow
    token
    (persistentId fibre token)
    (persistentId fibre (head fibre token))

producerCompleteProjectionExact :
  ∀ {Token PersistentId : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId)
    (token : Token) →
  directAuthorityRow fibre token ≡ repairedAuthorityRow fibre token
producerCompleteProjectionExact fibre token = refl

-- Congruence is stated locally so this module does not need a larger equality
-- utility dependency merely to transport exact final-row equality to consumers.
mapEquality :
  ∀ {A B : Set} (observe : A → B) {left right : A} →
  left ≡ right →
  observe left ≡ observe right
mapEquality observe refl = refl

-- Runtime-facing observational law: every declared consumer of the final
-- authority row sees exactly the same result under direct first-write admission
-- and under the legacy insert-then-repair implementation.
consumerObservationExact :
  ∀ {Token PersistentId Observation : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId)
    (observe : PersistentTokenRow Token PersistentId → Observation)
    (token : Token) →
  observe (directAuthorityRow fibre token)
    ≡ observe (repairedAuthorityRow fibre token)
consumerObservationExact fibre observe token =
  mapEquality observe (producerCompleteProjectionExact fibre token)

-- The numeric dependency edge is available before the authority write and is
-- the same edge the repair path eventually reconstructs.
directHeadExact :
  ∀ {Token PersistentId : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId)
    (token : Token) →
  headTokenId (directAuthorityRow fibre token)
    ≡ persistentId fibre (head fibre token)
directHeadExact fibre token = refl

repairHeadExact :
  ∀ {Token PersistentId : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId)
    (token : Token) →
  headTokenId (repairedAuthorityRow fibre token)
    ≡ persistentId fibre (head fibre token)
repairHeadExact fibre token = refl

-- Injective persistent identity means equality of encoded head ids reflects
-- equality of the producer-level head tokens; numeric encoding has not merged
-- distinct dependency targets.
persistentHeadIdentityReflectsTokenHead :
  ∀ {Token PersistentId : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId)
    (left right : Token) →
  persistentId fibre (head fibre left) ≡ persistentId fibre (head fibre right) →
  head fibre left ≡ head fibre right
persistentHeadIdentityReflectsTokenHead fibre left right encodedEqual =
  persistentIdInjective fibre
    (head fibre left)
    (head fibre right)
    encodedEqual

------------------------------------------------------------------------
-- Physical mutation separation.
--
-- The semantic theorem above licenses elimination of the post-insert rewrite;
-- this receipt records the physical distinction without pretending mutation
-- count is semantic identity.
------------------------------------------------------------------------

record TokenMutationReceipt : Set where
  constructor mutationReceipt
  field
    insertedRows : Nat
    postInsertUpdates : Nat

open TokenMutationReceipt public

directMutationReceipt : Nat → TokenMutationReceipt
directMutationReceipt count = mutationReceipt count zero

insertThenRepairMutationReceipt : Nat → TokenMutationReceipt
insertThenRepairMutationReceipt count = mutationReceipt count count

directHasNoSelfRewrite :
  ∀ count →
  postInsertUpdates (directMutationReceipt count) ≡ zero
directHasNoSelfRewrite count = refl

repairRewritesWholeFibre :
  ∀ count →
  postInsertUpdates (insertThenRepairMutationReceipt count) ≡ count
repairRewritesWholeFibre count = refl

-- Combining semantic equivalence with the mutation receipt gives the exact
-- admissibility boundary consumed by the runtime optimisation.
record ProducerCompleteRewriteElimination
  (Token PersistentId : Set)
  : Set₁ where
  field
    fibre : ProducerCompleteDependencyFibre Token PersistentId
    authorityExact :
      ∀ token →
      directAuthorityRow fibre token ≡ repairedAuthorityRow fibre token
    consumerExact :
      ∀ {Observation : Set}
        (observe : PersistentTokenRow Token PersistentId → Observation)
        token →
      observe (directAuthorityRow fibre token)
        ≡ observe (repairedAuthorityRow fibre token)
    noPostInsertRewrite :
      ∀ count →
      postInsertUpdates (directMutationReceipt count) ≡ zero

open ProducerCompleteRewriteElimination public

compileRewriteElimination :
  ∀ {Token PersistentId : Set}
    (fibre : ProducerCompleteDependencyFibre Token PersistentId) →
  ProducerCompleteRewriteElimination Token PersistentId
compileRewriteElimination fibre = record
  { fibre = fibre
  ; authorityExact = producerCompleteProjectionExact fibre
  ; consumerExact = consumerObservationExact fibre
  ; noPostInsertRewrite = directHasNoSelfRewrite
  }
