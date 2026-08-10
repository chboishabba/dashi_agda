module DASHI.Physics.Closure.NSTriadKNScopedClassificationWitnessRound37Exact where

------------------------------------------------------------------------
-- DASHI PROOF-ENGINEERING CONTRIBUTION
--
-- The continuation analysis identified a recurring scope hazard: a theorem
-- proved for a selected/classified state must not silently turn that property
-- witness into an identity of the ambient carrier.  This matters directly for
-- HH-good/HH-bad, selected sectors, aligned fibres and the final official-data
-- scope audit.
--
-- `ClassifiedAt` therefore stores a property edge
--
--   index -- state -- evidence
--
-- without constructing a new ambient state or equating the state with its
-- class.  Classification may be transported only by an explicit implication
-- between the old and new predicates.  `HHBadAt` specializes this discipline
-- to shell/time-indexed badness.
--
-- This is repository-original type-safety infrastructure; no external theorem
-- or DOI is claimed for the record itself.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record ClassifiedAt
    {indexLevel stateLevel evidenceLevel : Level}
    {Index : Set indexLevel}
    {State : Set stateLevel}
    (Property : Index → State → Set evidenceLevel)
    (index : Index)
    (state : State) :
    Set (indexLevel ⊔ stateLevel ⊔ evidenceLevel) where
  constructor classified-at
  field
    evidence : Property index state

open ClassifiedAt public

forgetClassification :
  ∀ {indexLevel stateLevel evidenceLevel}
    {Index : Set indexLevel}
    {State : Set stateLevel}
    {Property : Index → State → Set evidenceLevel}
    {index state} →
  ClassifiedAt Property index state → State
forgetClassification {state = state} witness = state

forgetClassificationExact :
  ∀ {indexLevel stateLevel evidenceLevel}
    {Index : Set indexLevel}
    {State : Set stateLevel}
    {Property : Index → State → Set evidenceLevel}
    {index state}
    (witness : ClassifiedAt Property index state) →
  forgetClassification witness ≡ state
forgetClassificationExact witness = refl

mapClassification :
  ∀ {indexLevel stateLevel evidenceLevel targetLevel}
    {Index : Set indexLevel}
    {State : Set stateLevel}
    {Source : Index → State → Set evidenceLevel}
    {Target : Index → State → Set targetLevel}
    {index state} →
  (Source index state → Target index state) →
  ClassifiedAt Source index state →
  ClassifiedAt Target index state
mapClassification implication witness =
  classified-at (implication (evidence witness))

record HHBadIndex
    {timeLevel : Level}
    (Time : Set timeLevel) : Set timeLevel where
  constructor hh-bad-index
  field
    shell : Nat
    time : Time

open HHBadIndex public

HHBadAt :
  ∀ {timeLevel stateLevel evidenceLevel}
    {Time : Set timeLevel}
    {State : Set stateLevel} →
  (Bad : HHBadIndex Time → State → Set evidenceLevel) →
  HHBadIndex Time → State →
  Set (timeLevel ⊔ stateLevel ⊔ evidenceLevel)
HHBadAt = ClassifiedAt

scopedClassificationWitnessTyped : Bool
scopedClassificationWitnessTyped = true

scopedClassificationWitnessTypedIsTrue :
  scopedClassificationWitnessTyped ≡ true
scopedClassificationWitnessTypedIsTrue = refl
