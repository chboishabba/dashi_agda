module DASHI.Crypto.MLKEMFiniteStateTranscriptCapacityExact where

------------------------------------------------------------------------
-- ML-KEM: FINITE STATE x TRANSCRIPT PROTECTED-CAPACITY BOUND
--
-- Purpose
-- -------
-- Formalise the exact combinatorial seam needed after the local uncertainty
-- theorem.  If a protected label is recoverable from a maintained state plus a
-- readout/query transcript, then the protected-label carrier injects into the
-- product StateCode x TranscriptCode.  Consequently, once separate finite
-- capacity bounds are supplied for those two coordinates, protected capacity
-- is bounded by their product.
--
-- This is intentionally finite/combinatorial.  It does not invoke Shannon
-- entropy, runtime, or any ML-KEM-specific hardness assumption.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

record StateTranscriptRecovery {h s t p : Level} : Set (lsuc (h ⊔ s ⊔ t ⊔ p)) where
  constructor state-transcript-recovery
  field
    Hidden : Set h
    StateCode : Set s
    TranscriptCode : Set t
    Protected : Set p

    state : Hidden → StateCode
    transcript : Hidden → TranscriptCode
    protected : Hidden → Protected
    decode : StateCode × TranscriptCode → Protected

    decodeCorrect :
      (hidden : Hidden) →
      decode (state hidden , transcript hidden) ≡ protected hidden

open StateTranscriptRecovery public

JointCode :
  ∀ {h s t p} →
  StateTranscriptRecovery {h} {s} {t} {p} → Set (s ⊔ t)
JointCode recovery = StateCode recovery × TranscriptCode recovery

observeJoint :
  ∀ {h s t p}
    (recovery : StateTranscriptRecovery {h} {s} {t} {p}) →
  Hidden recovery → JointCode recovery
observeJoint recovery hidden =
  state recovery hidden , transcript recovery hidden

sameJointCodeForcesSameProtected :
  ∀ {h s t p}
    {recovery : StateTranscriptRecovery {h} {s} {t} {p}}
    {left right : Hidden recovery} →
  observeJoint recovery left ≡ observeJoint recovery right →
  protected recovery left ≡ protected recovery right
sameJointCodeForcesSameProtected {recovery = recovery} {left} {right} jointSame =
  begin
    protected recovery left
      ≡⟨ sym (decodeCorrect recovery left) ⟩
    decode recovery (observeJoint recovery left)
      ≡⟨ cong (decode recovery) jointSame ⟩
    decode recovery (observeJoint recovery right)
      ≡⟨ decodeCorrect recovery right ⟩
    protected recovery right
  ∎
  where
  open import Relation.Binary.PropositionalEquality using (cong; sym)
  open import Relation.Binary.PropositionalEquality.≡-Reasoning

record ProtectedRepresentatives
    {h s t p : Level}
    (recovery : StateTranscriptRecovery {h} {s} {t} {p})
    : Set (h ⊔ p) where
  constructor protected-representatives
  field
    representative : Protected recovery → Hidden recovery
    representativeCorrect :
      (label : Protected recovery) →
      protected recovery (representative label) ≡ label

open ProtectedRepresentatives public

codeOfProtected :
  ∀ {h s t p}
    {recovery : StateTranscriptRecovery {h} {s} {t} {p}} →
  ProtectedRepresentatives recovery →
  Protected recovery → JointCode recovery
codeOfProtected {recovery = recovery} reps label =
  observeJoint recovery (representative reps label)

codeOfProtectedInjective :
  ∀ {h s t p}
    {recovery : StateTranscriptRecovery {h} {s} {t} {p}}
    (reps : ProtectedRepresentatives recovery)
    {left right : Protected recovery} →
  codeOfProtected reps left ≡ codeOfProtected reps right →
  left ≡ right
codeOfProtectedInjective {recovery = recovery} reps {left} {right} codeSame =
  begin
    left
      ≡⟨ sym (representativeCorrect reps left) ⟩
    protected recovery (representative reps left)
      ≡⟨ sameJointCodeForcesSameProtected codeSame ⟩
    protected recovery (representative reps right)
      ≡⟨ representativeCorrect reps right ⟩
    right
  ∎
  where
  open import Relation.Binary.PropositionalEquality using (sym)
  open import Relation.Binary.PropositionalEquality.≡-Reasoning

------------------------------------------------------------------------
-- Explicit finite-capacity interface.
--
-- Rather than importing a particular finite-set library here, expose the exact
-- multiplicative numerical seam consumed downstream:
--
--   protectedCount <= jointCount
--   jointCount <= stateCount * transcriptCount
--
-- gives
--
--   protectedCount <= stateCount * transcriptCount.
------------------------------------------------------------------------

open import Data.Nat using (Nat; _≤_; _*_)
import Data.Nat.Properties as NatP

stateTranscriptCapacityBound :
  (protectedCount stateCount transcriptCount jointCount : Nat) →
  protectedCount ≤ jointCount →
  jointCount ≤ stateCount * transcriptCount →
  protectedCount ≤ stateCount * transcriptCount
stateTranscriptCapacityBound
  protectedCount stateCount transcriptCount jointCount
  protectedIntoJoint jointIntoProduct =
  NatP.≤-trans protectedIntoJoint jointIntoProduct

record FiniteStateTranscriptCapacity : Set where
  constructor finite-state-transcript-capacity
  field
    protectedCount : Nat
    stateCount : Nat
    transcriptCount : Nat
    jointCount : Nat

    protectedInjectsIntoJointCount : protectedCount ≤ jointCount
    jointBoundedByProduct : jointCount ≤ stateCount * transcriptCount

open FiniteStateTranscriptCapacity public

protectedCapacityProductBound :
  (capacity : FiniteStateTranscriptCapacity) →
  protectedCount capacity ≤ stateCount capacity * transcriptCount capacity
protectedCapacityProductBound capacity =
  stateTranscriptCapacityBound
    (protectedCount capacity)
    (stateCount capacity)
    (transcriptCount capacity)
    (jointCount capacity)
    (protectedInjectsIntoJointCount capacity)
    (jointBoundedByProduct capacity)

------------------------------------------------------------------------
-- AUTHORITY BOUNDARY
--
-- The semantic theorem above proves an actual injection
--
--     Protected -> StateCode x TranscriptCode
--
-- once representatives exist and exact decoding is supplied.
--
-- Turning that injection into a concrete cardinal inequality still requires a
-- finite-cardinality producer for the actual state/transcript carriers.  For a
-- bounded-cell state this should be supplied by a separate exact product-power
-- count; for an adaptive query/readout procedure it should be supplied by a
-- transcript-tree capacity theorem.  Neither is silently assumed here.
------------------------------------------------------------------------
