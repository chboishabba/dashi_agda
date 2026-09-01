module DASHI.Physics.YangMills.BalabanRootedPositiveFormPhysicalStateRound203Exact where

------------------------------------------------------------------------
-- ROUND 203
--
-- Terminal cutset compression.
--
-- R200--R202 show that quotient/GNS bookkeeping is not a separate blocker.
-- The remaining analytic producer can be stated on exactly one object: a
-- physical state which induces a positive form on rooted representatives.
-- This record is intentionally minimal and theorem-bearing; it is not a
-- substitute for the Haar/Gibbs construction itself.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientPositiveFormRound201Exact as R201
import DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientGNSBridgeRound200Exact as R200
import DASHI.Physics.YangMills.BalabanRootedPositiveFormGNSCompilerRound202Exact as R202

record RootedPhysicalState
    (Configuration Rooted Scalar : Set) : Set₁ where
  field
    normalise : Configuration → Rooted
    PhysicalState : Set
    positiveFormProducer :
      R201.PhysicalStatePositiveFormProducer PhysicalState Rooted Scalar

open RootedPhysicalState public

physicalStateGNSBridge :
  ∀ {Configuration Rooted Scalar}
    (state : RootedPhysicalState Configuration Rooted Scalar) →
  R200.RootedPhysicalQuotientGNSBridge Configuration Rooted Scalar
physicalStateGNSBridge state =
  R202.compileRootedPositiveFormToGNSBridge
    (normalise state)
    (R201.form (positiveFormProducer state))
