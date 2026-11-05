{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayProofRelevantFieldAnchoringSafeExact where

------------------------------------------------------------------------
-- CRITICAL 219-field truth firewall: a field (name : Set) CHOOSES A TYPE.
-- It DOES NOT INHABIT that type and is not an exact proof lemma.
--
-- Both original sources (BalabanClayGate4PhysicalClosureRound6ExactCutset
-- and YangMillsSubmissionExactCutset) have 219/219 declarations of this
-- exact type-valued form. This genuinely standalone --safe Agda
-- module gives a constructive negative control and the necessary
-- proof-relevant, SAME-OBJECT upgrade interface.
--
-- Do NOT mistake the existence of an original 219-field record inhabitant
-- (only choosing 219 Sets) for inhabitation of 219 physical propositions.
-- Only AnchoredField can promote a chosen named field, and it explicitly
-- requires both (1) equality to a FIXED selected physical predicate on
-- ONE selected construction and (2) a proof of the original field type.
--
-- The forward/backward transport is an equivalence for a FIXED equality.
-- It is NOT a claim that every selected physical predicate can be proved,
-- nor an if-and-only-if from Clay completion to historical cutsets.
-- No postulates, holes, unsafe imports, physical SU(N) or Clay claim.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

data NoProof : Set where

data Trivial : Set where
  trivial : Trivial

record BareNamedField : Set₁ where
  constructor bareNamedField
  field
    statement : Set

open BareNamedField public

-- Even the empty proposition is a perfectly valid Set-valued FIELD.
-- Thus making the original record cannot count as proving its fields.
perfectlyLegalButFalseTypeChoice : BareNamedField
perfectlyLegalButFalseTypeChoice =
  bareNamedField NoProof

noUniversalProofFromBareField :
  ((field : BareNamedField) → statement field) →
  NoProof
noUniversalProofFromBareField pretendToProveAll =
  pretendToProveAll perfectlyLegalButFalseTypeChoice

-- Equality transport, fully defined by the Agda identity eliminator.
transportSameStatement :
  ∀ {A B : Set} → A ≡ B → A → B
transportSameStatement refl witness = witness

transportBackwards :
  ∀ {A B : Set} → A ≡ B → B → A
transportBackwards refl witness = witness

-- SAME-OBJECT proof-relevant completion. The selected physical
-- proposition is a function of the SAME selected object Y, not a
-- free type chosen after the fact by a submitter.
record AnchoredField
    {PhysicalObject : Set}
    (chosenOriginalType : Set)
    (selectedObject : PhysicalObject)
    (selectedPhysicalPredicate : PhysicalObject → Set)
    : Set₁ where
  constructor anchoredField
  field
    originalEqualsSelectedPhysical :
      chosenOriginalType ≡ selectedPhysicalPredicate selectedObject
    actualWitness : chosenOriginalType

open AnchoredField public

anchoredFieldGivesSelectedPhysicalProof :
  ∀ {PhysicalObject}
    {originalType : Set}
    {Y : PhysicalObject}
    {physicalPredicate : PhysicalObject → Set} →
  AnchoredField originalType Y physicalPredicate →
  physicalPredicate Y
anchoredFieldGivesSelectedPhysicalProof field =
  transportSameStatement
    (originalEqualsSelectedPhysical field)
    (actualWitness field)

selectedPhysicalProofGivesAnchoredField :
  ∀ {PhysicalObject}
    {Y : PhysicalObject}
    {physicalPredicate : PhysicalObject → Set} →
  physicalPredicate Y →
  AnchoredField (physicalPredicate Y) Y physicalPredicate
selectedPhysicalProofGivesAnchoredField witness =
  anchoredField refl witness

anchoringThenProjectionIsIdentity :
  ∀ {PhysicalObject}
    {Y : PhysicalObject}
    {physicalPredicate : PhysicalObject → Set}
    (witness : physicalPredicate Y) →
  anchoredFieldGivesSelectedPhysicalProof
    (selectedPhysicalProofGivesAnchoredField witness)
  ≡ witness
anchoringThenProjectionIsIdentity witness = refl

-- Reverse transport is permissible only because we have already
-- supplied EXACT equality of types, not because two theorem names look
-- compatible or share the same original Set-valued field label.
anchoredFieldFromSelectedWithProofOfLiteralEquality :
  ∀ {PhysicalObject}
    {chosenOriginalType : Set}
    {Y : PhysicalObject}
    {physicalPredicate : PhysicalObject → Set} →
  chosenOriginalType ≡ physicalPredicate Y →
  physicalPredicate Y →
  AnchoredField chosenOriginalType Y physicalPredicate
anchoredFieldFromSelectedWithProofOfLiteralEquality equal witness =
  anchoredField equal (transportBackwards equal witness)

anchoredFalsePhysicalPredicateImpossible :
  ∀ {PhysicalObject} {Y : PhysicalObject}
    (originalType : Set) →
  AnchoredField originalType Y (λ _ → NoProof) →
  NoProof
anchoredFalsePhysicalPredicateImpossible originalType field =
  anchoredFieldGivesSelectedPhysicalProof field

-- The original 219-field record remains unchanged. For each of those
-- 219 names a separate chosen physical predicate on ONE original literal Y,
-- equality to that predicate, original witness, and actual kernel receipt
-- must be constructed before marking PROVED.
