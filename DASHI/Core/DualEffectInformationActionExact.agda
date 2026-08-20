module DASHI.Core.DualEffectInformationActionExact where

------------------------------------------------------------------------
-- DUAL-EFFECT ACTIONS
--
-- Animal communication, environmental sampling/intervention, and expensive
-- garment materialisation can all change the world and/or refine what the
-- system knows.  Treating "information gathering" as outside the action
-- language prevents bounded future equivalence and planning from reasoning
-- about active sensing/experimentation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)

record DualEffectAction
    (World Information Action : Set) : Set₁ where
  constructor dualEffectAction
  field
    worldStep : Action → World → World
    informationStep : Action → Information → Information

open DualEffectAction public

record JointState (World Information : Set) : Set where
  constructor jointState
  field
    world : World
    information : Information

open JointState public

jointStep :
  ∀ {World Information Action} →
  DualEffectAction World Information Action →
  Action → JointState World Information → JointState World Information
jointStep system action state =
  jointState
    (worldStep system action (world state))
    (informationStep system action (information state))

------------------------------------------------------------------------
-- Pure information actions and pure world actions are special cases.  These
-- are properties of a declared action, not separate action universes.
------------------------------------------------------------------------

record InformationOnly
    {World Information Action : Set}
    (system : DualEffectAction World Information Action)
    (action : Action) : Set₁ where
  constructor informationOnly
  field
    worldFixed : ∀ world → worldStep system action world ≡ world

open InformationOnly public

record WorldOnly
    {World Information Action : Set}
    (system : DualEffectAction World Information Action)
    (action : Action) : Set₁ where
  constructor worldOnly
  field
    informationFixed :
      ∀ information → informationStep system action information ≡ information

open WorldOnly public

informationOnlyPreservesWorldCoordinate :
  ∀ {World Information Action}
    {system : DualEffectAction World Information Action}
    {action : Action} →
  InformationOnly system action →
  (state : JointState World Information) →
  world (jointStep system action state) ≡ world state
informationOnlyPreservesWorldCoordinate witness state =
  worldFixed witness (world state)

worldOnlyPreservesInformationCoordinate :
  ∀ {World Information Action}
    {system : DualEffectAction World Information Action}
    {action : Action} →
  WorldOnly system action →
  (state : JointState World Information) →
  information (jointStep system action state) ≡ information state
worldOnlyPreservesInformationCoordinate witness state =
  informationFixed witness (information state)

------------------------------------------------------------------------
-- Information value is consumer-relative.  We avoid forcing utilities or
-- probabilities into the kernel: a domain supplies a theorem that an action
-- separates two currently collapsed alternatives for a declared observer.
------------------------------------------------------------------------

record InformationSeparatingAction
    {World Information Action Observation : Set}
    (system : DualEffectAction World Information Action)
    (observe : Information → Observation)
    (action : Action)
    (left right : Information) : Set₁ where
  constructor informationSeparatingAction
  field
    sameBefore : observe left ≡ observe right
    differAfter :
      observe (informationStep system action left)
      ≡ observe (informationStep system action right) →
      Data.Empty.⊥

------------------------------------------------------------------------
-- No theorem says every separating action is worth taking: cost, welfare,
-- physical risk and authority remain consumer/domain obligations.
------------------------------------------------------------------------
