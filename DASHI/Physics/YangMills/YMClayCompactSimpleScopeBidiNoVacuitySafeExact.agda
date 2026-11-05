{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayCompactSimpleScopeBidiNoVacuitySafeExact where

------------------------------------------------------------------------
-- SEM.P02: exact all-compact-simple-group QUANTIFIER soundness firewall.
--
-- In the original Top.LiteralYangMillsCarriers the field
-- CompactSimpleGroup : Set is freely selected. A proof
--     (forall G : chosenGroupSet, PhysicallyCorrect G)
-- can be VACUOUS when that selected Set is empty, or too weak when it
-- contains just one chosen SU(2) label.
--
-- A mathematical Clay theorem needs externally specified compact
-- SIMPLE Lie groups, and the selected internal group index set must
-- actually represent them, not merely have a convenient name.
--
-- This pure no-postulate --safe owner proves the precise condition
-- needed to turn source-internal all-group witnesses into EXTERNAL
-- all-group witnesses: an explicitly chosen total index mapping
-- and same-group interpretation of every relevant predicate.
--
-- The reverse direction additionally requires total decoding and
-- a checked inverse equation. This gives a genuine *conditional*
-- bidi equivalence under scope AND semantic identity, not an unjustified
-- theorem that SU(2) entails all compact simple G.
--
-- ExternalCarrier/ExternalPredicate remain to be instantiated to
-- authoritative mathematical compact-simple groups / actual physical
-- Yang--Mills requirements. No group classification or mass gap is
-- smuggled in here. This remains an explicitly semantic firewall.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data Empty : Set where

data Unit : Set where
  unit : Unit

-- A vacuous internal universal theorem exists even with NO GROUPS.
internalAllOnEmptyIsTrivial :
  ∀ {Predicate : Empty → Set} →
  (∀ group → Predicate group)
internalAllOnEmptyIsTrivial ()

-- The externally specified group scope is nonempty once we
-- independently supply any actual external compact-simple witness.
externalWitnessRejectsEmptyInternalScope :
  ∀ {External : Set}
    (actualExternalGroup : External) →
    (encodeSelected : External → Empty) →
    Empty
externalWitnessRejectsEmptyInternalScope actualExternalGroup encodeSelected =
  encodeSelected actualExternalGroup

record SelectedGroupScope
    (ExternalGroup SelectedInternalGroup : Set) : Set where
  constructor selectedGroupScope
  field
    externalWitness : ExternalGroup
    encode : ExternalGroup → SelectedInternalGroup
    decode : SelectedInternalGroup → ExternalGroup
    encodeAfterDecode : ∀ group → encode (decode group) ≡ group
    decodeAfterEncode : ∀ group → decode (encode group) ≡ group

open SelectedGroupScope public

sameMeaningForward :
  ∀ {A B : Set} → A ≡ B → A → B
sameMeaningForward refl proof = proof

sameMeaningBackward :
  ∀ {A B : Set} → A ≡ B → B → A
sameMeaningBackward refl proof = proof

selectedAllGroupsGivesExternalAllGroups :
  ∀ {ExternalGroup InternalGroup : Set}
    (scope : SelectedGroupScope ExternalGroup InternalGroup)
    (externalPhysical : ExternalGroup → Set)
    (internalPhysical : InternalGroup → Set) →
    (∀ external →
      externalPhysical external
      ≡ internalPhysical (encode scope external)) →
    (∀ internal → internalPhysical internal) →
    (∀ external → externalPhysical external)
selectedAllGroupsGivesExternalAllGroups
    scope externalPhysical internalPhysical sameProof internalAll external =
  sameMeaningBackward (sameProof external)
    (internalAll (encode scope external))

externalAllGroupsGivesSelectedAllGroups :
  ∀ {ExternalGroup InternalGroup : Set}
    (scope : SelectedGroupScope ExternalGroup InternalGroup)
    (externalPhysical : ExternalGroup → Set)
    (internalPhysical : InternalGroup → Set) →
    (∀ external →
      externalPhysical external
      ≡ internalPhysical (encode scope external)) →
    (∀ external → externalPhysical external) →
    (∀ internal → internalPhysical internal)
externalAllGroupsGivesSelectedAllGroups
    scope externalPhysical internalPhysical sameProof externalAll internal =
  sameMeaningForward
    (cong internalPhysical (encodeAfterDecode scope internal))
    (sameMeaningForward
      (sameProof (decode scope internal))
      (externalAll (decode scope internal)))

-- The *external-to-internal* theorem does not require the
-- decodeAfterEncode equality. It is retained because true selected
-- scope equivalence (not just a sufficient embedding) must also
-- preserve external identities without aliasing distinct groups.
-- The record's witness and inverse equations rule out an empty
-- internal group scope entirely.

internalGroupExistenceFromExternalWitness :
  ∀ {ExternalGroup InternalGroup : Set}
    (scope : SelectedGroupScope ExternalGroup InternalGroup) →
    InternalGroup
internalGroupExistenceFromExternalWitness scope =
  encode scope (externalWitness scope)

-- The following input is the truly open physical one. Naming this
-- structure or its abstract carrier does not construct the actual
-- classification/topology of compact simple Lie groups, a matching
-- SU(N) matrix backend, measurable Haar, continuum QFT or Clay gap.
