module DASHI.Moonshine.Monster3BLinearActionProofRelevantHardeningExact where

------------------------------------------------------------------------
-- PROOF-RELEVANT HARDENING FOR THE UPSTREAM MONSTER LINEAR-ACTION SEAM
--
-- Two legacy owners correctly name the linear representation obligations needed
-- before the Monster 3B isotypic/Hom-space programme can run:
--
--   * MonsterWeightTwoLinearActionBridgeExact;
--   * IbrahimMonster3BLinearZetaSectorRestrictionExact.
--
-- Several of those obligations are stored as fields whose VALUES are `Set`s.
-- Such fields name proposition types; they do not contain proofs inhabiting
-- those propositions.  This owner leaves the legacy APIs intact and adds paid
-- wrappers requiring witnesses on the SAME literal carriers/actions.
--
-- No external mathematical source is used here.  This is a DASHI interface
-- correction following the same proof-relevant discipline already applied to
-- H_zeta, W_zeta, multiplicity and basis recognition.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterWeightTwoLinearActionBridgeExact as WeightTwo
import DASHI.Wikimedia.IbrahimMonster3BLinearZetaSectorRestrictionExact as LinearZeta

------------------------------------------------------------------------
-- 1. Paid full weight-two linear constituent/action bridge.
------------------------------------------------------------------------

record PaidWeightTwoLinearActionBridge
    {Monster K : Set}
    {bridge}
    (legacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge)
    : Setω where
  field
    constituentActPreservesZeroWitness :
      WeightTwo.constituentActPreservesZero legacy
    constituentActPreservesAdditionWitness :
      WeightTwo.constituentActPreservesAddition legacy
    constituentActPreservesScalingWitness :
      WeightTwo.constituentActPreservesScaling legacy
    constituentInvariantUnderMonsterActionWitness :
      WeightTwo.constituentInvariantUnderMonsterAction legacy

open PaidWeightTwoLinearActionBridge public

forgetPaidWeightTwoLinearActionBridge :
  ∀ {Monster K bridge}
    (legacy : WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge) →
  PaidWeightTwoLinearActionBridge legacy →
  WeightTwo.WeightTwoLinearActionBridge {Monster} {K} bridge
forgetPaidWeightTwoLinearActionBridge legacy paid = legacy

------------------------------------------------------------------------
-- 2. Paid SAME literal zeta-eigenspace linear restriction.
------------------------------------------------------------------------

record PaidLinearSingleActionProducer
    (legacy : LinearZeta.LinearSingleActionProducer)
    : Setω where
  field
    centralActionIsLinearWitness :
      LinearZeta.centralActionIsLinear legacy
    normalizerActionIsLinearWitness :
      LinearZeta.normalizerActionIsLinear legacy
    phaseScalingIsLinearWitness :
      LinearZeta.phaseScalingIsLinear legacy
    inclusionIsLinearWitness :
      LinearZeta.inclusionIsLinear legacy
    inertiaRestrictionIsLinearWitness :
      LinearZeta.inertiaRestrictionIsLinear legacy

open PaidLinearSingleActionProducer public

forgetPaidLinearSingleActionProducer :
  (legacy : LinearZeta.LinearSingleActionProducer) →
  PaidLinearSingleActionProducer legacy →
  LinearZeta.LinearSingleActionProducer
forgetPaidLinearSingleActionProducer legacy paid = legacy

------------------------------------------------------------------------
-- 3. WrongType / non-promotion firewall.
------------------------------------------------------------------------

data TypedLinearityObligationCreatesPaidLinearAction : Set where

typedLinearityObligationDoesNotPayLinearAction :
  TypedLinearityObligationCreatesPaidLinearAction → ⊥
typedLinearityObligationDoesNotPayLinearAction ()

------------------------------------------------------------------------
-- 4. Machine-readable boundary.
------------------------------------------------------------------------

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
