module DASHI.Core.ContextualDialecticRoleExact where

------------------------------------------------------------------------
-- CONTEXTUAL DIALECTIC ROLE
--
-- Source basis:
--   User-supplied DASHI origin/reconstruction material in which named people,
--   religions, political positions, sexualities and other examples could occupy
--   different 3/6/9 or stage roles depending on the argument being modelled.
--   The recovered notes explicitly distinguish an authentic historical joke
--   label ("369 lesbian") from any claim that sexual orientation has an
--   intrinsic number.
--
-- Mathematical cross-pollination:
--   DASHI.Biology.TernaryCyclicDialecticExact already proves that dialectical
--   labels are external annotations on the cyclic ternary carrier: an
--   automorphism can exchange labelled positions. This module extracts the
--   generic frame-relative role principle without importing named demographic
--   categories into the theorem statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Roles are indexed by a frame.
------------------------------------------------------------------------

data DialecticRole : Set where
  initialRole counterRole mediatingRole closureRole : DialecticRole

record ContextualRoleSystem (Frame Entity : Set) : Set₁ where
  field
    roleIn : Frame → Entity → DialecticRole

open ContextualRoleSystem public

record RoleChangeWitness
    {Frame Entity : Set}
    (system : ContextualRoleSystem Frame Entity) : Set where
  constructor role-change-witness
  field
    entity : Entity
    firstFrame secondFrame : Frame
    roleChanged :
      roleIn system firstFrame entity ≡ roleIn system secondFrame entity → ⊥

open RoleChangeWitness public

roleChangeBlocksIntrinsicRole :
  ∀ {Frame Entity}
    {system : ContextualRoleSystem Frame Entity} →
  RoleChangeWitness system →
  (intrinsic : Entity → DialecticRole) →
  ((frame : Frame) (entity : Entity) →
    roleIn system frame entity ≡ intrinsic entity) →
  ⊥
roleChangeBlocksIntrinsicRole witness intrinsic agrees =
  roleChanged witness
    (trans
      (agrees (firstFrame witness) (entity witness))
      (sym (agrees (secondFrame witness) (entity witness))))

------------------------------------------------------------------------
-- Concrete frame-relative specimen.
------------------------------------------------------------------------

data DemoFrame : Set where
  argumentA argumentB : DemoFrame

data DemoEntity : Set where
  sameEntity : DemoEntity

demoRoleSystem : ContextualRoleSystem DemoFrame DemoEntity
demoRoleSystem = record
  { roleIn = role
  }
  where
    role : DemoFrame → DemoEntity → DialecticRole
    role argumentA sameEntity = initialRole
    role argumentB sameEntity = counterRole

demoRoleChanges : RoleChangeWitness demoRoleSystem
demoRoleChanges =
  role-change-witness
    sameEntity
    argumentA
    argumentB
    (λ ())

noIntrinsicRoleExplainsBothFrames :
  (intrinsic : DemoEntity → DialecticRole) →
  ((frame : DemoFrame) (entity : DemoEntity) →
    roleIn demoRoleSystem frame entity ≡ intrinsic entity) →
  ⊥
noIntrinsicRoleExplainsBothFrames =
  roleChangeBlocksIntrinsicRole demoRoleChanges

------------------------------------------------------------------------
-- Historical-example scope boundary.
------------------------------------------------------------------------

record ContextualDialecticRoleBoundary : Set where
  constructor contextual-dialectic-role-boundary
  field
    namedIdentityHasIntrinsicDialecticNumber : Bool
    namedIdentityHasIntrinsicDialecticNumberIsFalse :
      namedIdentityHasIntrinsicDialecticNumber ≡ false
    jokeLabelIsOntology : Bool
    jokeLabelIsOntologyIsFalse : jokeLabelIsOntology ≡ false
    roleMayChangeWithComparisonFrame : Bool
    roleMayChangeWithComparisonFrameIsTrue :
      roleMayChangeWithComparisonFrame ≡ true

canonicalContextualDialecticRoleBoundary : ContextualDialecticRoleBoundary
canonicalContextualDialecticRoleBoundary =
  contextual-dialectic-role-boundary
    false refl
    false refl
    true refl
