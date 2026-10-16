module DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT HARDENING FOR THE UPSTREAM MONSTER LINEAR-ACTION SEAM
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

record PaidWeightTwoLinearActionBridge
    {Monster K : Set}
    {bridge}
    (legacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge)
    : Setω where
  field
    constituentActPreservesZeroWitness : WeightTwo.constituentActPreservesZero legacy
    constituentActPreservesAdditionWitness : WeightTwo.constituentActPreservesAddition legacy
    constituentActPreservesScalingWitness : WeightTwo.constituentActPreservesScaling legacy
    constituentInvariantUnderMonsterActionWitness :
      WeightTwo.constituentInvariantUnderMonsterAction legacy
open PaidWeightTwoLinearActionBridge public

forgetPaidWeightTwoLinearActionBridge :
  ∀ {Monster K bridge}
    (legacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge) →
  PaidWeightTwoLinearActionBridge legacy →
  WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge
forgetPaidWeightTwoLinearActionBridge legacy paid = legacy

record PaidLinearSingleActionProducer
    (legacy : LinearZeta.LinearSingleActionProducer) : Setω where
  field
    centralActionIsLinearWitness : LinearZeta.centralActionIsLinear legacy
    normalizerActionIsLinearWitness : LinearZeta.normalizerActionIsLinear legacy
    phaseScalingIsLinearWitness : LinearZeta.phaseScalingIsLinear legacy
    inclusionIsLinearWitness : LinearZeta.inclusionIsLinear legacy
    inertiaRestrictionIsLinearWitness : LinearZeta.inertiaRestrictionIsLinear legacy
open PaidLinearSingleActionProducer public

forgetPaidLinearSingleActionProducer :
  (legacy : LinearZeta.LinearSingleActionProducer) →
  PaidLinearSingleActionProducer legacy →
  LinearZeta.LinearSingleActionProducer
forgetPaidLinearSingleActionProducer legacy paid = legacy

data TypedLinearityObligationCreatesPaidLinearAction : Set where

typedLinearityObligationDoesNotPayLinearAction :
  TypedLinearityObligationCreatesPaidLinearAction → ⊥
typedLinearityObligationDoesNotPayLinearAction ()

record Boundary : Set where
  constructor boundary
  field
    legacyWeightTwoLinearityFieldsAreProofRelevant : Bool
    legacyLinearZetaFieldsAreProofRelevant : Bool
    paidWeightTwoWrapperAvailable : Bool
    paidLinearZetaWrapperAvailable : Bool
    typedLinearityObligationAlonePaysLinearAction : Bool
    actualPaidWeightTwoBridgeInhabitedHere : Bool
    actualPaidLinearZetaRestrictionInhabitedHere : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  false false
  true true
  false
  false false
