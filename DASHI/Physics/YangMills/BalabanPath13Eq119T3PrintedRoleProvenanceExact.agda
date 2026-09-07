{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanPath13Eq119T3PrintedRoleProvenanceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record T3PrintedRoleStatus : Set where
  constructor status
  field
    t3RightJacobianAdapterConstructed : Bool
    t3InverseLawsTransported : Bool
    perPointInverseReceiptsPruned : Bool
    selectedChartNormalizationConstructed : Bool
    concreteT3DatasetConstructed : Bool
    physicalEq119Closed : Bool
open T3PrintedRoleStatus public

canonicalT3PrintedRoleStatus : T3PrintedRoleStatus
canonicalT3PrintedRoleStatus = status
  true
  true
  true
  false
  false
  false

t3AdapterConstructedIsTrue :
  t3RightJacobianAdapterConstructed canonicalT3PrintedRoleStatus ≡ true
t3AdapterConstructedIsTrue = refl

t3InverseTransportIsTrue :
  t3InverseLawsTransported canonicalT3PrintedRoleStatus ≡ true
t3InverseTransportIsTrue = refl

selectedChartNormalizationClosedIsFalse :
  selectedChartNormalizationConstructed canonicalT3PrintedRoleStatus ≡ false
selectedChartNormalizationClosedIsFalse = refl

physicalEq119ClosedIsFalse :
  physicalEq119Closed canonicalT3PrintedRoleStatus ≡ false
physicalEq119ClosedIsFalse = refl

cmp98Path13T3PrintedRoleProvenanceLevel : ProofLevel
cmp98Path13T3PrintedRoleProvenanceLevel = machineChecked
