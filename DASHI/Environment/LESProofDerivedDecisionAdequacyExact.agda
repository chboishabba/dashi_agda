module DASHI.Environment.LESProofDerivedDecisionAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerDecisionAdequacyFromReductionExact as Adequacy
import DASHI.Core.ConsumerAdequacyJointPolicyBidiCompilerExact as Compiler
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESAdaptiveSPACModelSearchExact as SPAC

------------------------------------------------------------------------
-- LES PROOF-DERIVED MODEL ADEQUACY
--
-- Runtime SPAC tiers remain first-order labels.  Rich exact/approximate model
-- objects are linked to those labels by application-supplied realization
-- relations, after which the policy adequacy token must be equivalent to a
-- certificate-derived adequacy proof.
------------------------------------------------------------------------

record LESDecisionAdequacyBridge
    (mechanism : Basis.DomainMechanismSocket) : Set₂ where
  constructor lesDecisionAdequacyBridge
  field
    ExactRealises :
      SPAC.SPACFidelityTier →
      Reduction.ConsumerRelativeReduction
        (Basis.State mechanism)
        (Basis.Control mechanism)
        (Basis.Observation mechanism) → Set

    ApproxRealises :
      SPAC.SPACFidelityTier →
      Approx.ApproximateTraceReduction
        (Basis.State mechanism)
        (Basis.Control mechanism)
        (Basis.Observation mechanism) → Set

    interface : Adequacy.FirstOrderAdequacyInterface
      ExactRealises ApproxRealises

    exactModelRealisationReference : String
    approximateModelRealisationReference : String
    adequacyConsumerReference : String

open LESDecisionAdequacyBridge public

LESProofDerivedJointPolicy :
  ∀ {mechanism : Basis.DomainMechanismSocket}
    (bridge : LESDecisionAdequacyBridge mechanism)
    (system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism))
    (Authority : Basis.Control mechanism → Set) →
  (Basis.State mechanism → Set) →
  SPAC.SPACFidelityTier →
  Set₁
LESProofDerivedJointPolicy bridge system Authority =
  Compiler.CertifiedAdequacyJointPolicy
    system Authority
    (ExactRealises bridge)
    (ApproxRealises bridge)
    (interface bridge)

------------------------------------------------------------------------
-- Forward constructors expose the two admissible proof routes to an action
-- branch.  The exact route is future-exact; the approximate route is permitted
-- only with the existing certified decision-margin machinery.
------------------------------------------------------------------------

lesExactROMActBranch :
  ∀ {mechanism : Basis.DomainMechanismSocket}
    {bridge : LESDecisionAdequacyBridge mechanism}
    {system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)}
    {Authority : Basis.Control mechanism → Set}
    {live : Basis.State mechanism → Set}
    {tier : SPAC.SPACFidelityTier}
    {control : Basis.Control mechanism}
    (rom : Reduction.ConsumerRelativeReduction
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)) →
  ExactRealises bridge tier rom →
  (decide : Basis.Observation mechanism → Basis.Control mechanism) →
  Adequacy.ExactDecisionAdequacy rom decide control →
  Robust.RobustlyNoWorseThanBaseline system live control →
  Authority control →
  LESProofDerivedJointPolicy bridge system Authority live tier
lesExactROMActBranch {bridge = bridge} =
  Compiler.exactROMActBranch (interface bridge)

lesApproximateROMActBranch :
  ∀ {mechanism : Basis.DomainMechanismSocket}
    {bridge : LESDecisionAdequacyBridge mechanism}
    {system : Robust.HypothesisInterventionSystem
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)}
    {Authority : Basis.Control mechanism → Set}
    {live : Basis.State mechanism → Set}
    {tier : SPAC.SPACFidelityTier}
    {control : Basis.Control mechanism}
    (model : Approx.ApproximateTraceReduction
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)) →
  ApproxRealises bridge tier model →
  (decide : Basis.Observation mechanism → Basis.Control mechanism) →
  Adequacy.ApproximateDecisionAdequacy model decide control →
  Robust.RobustlyNoWorseThanBaseline system live control →
  Authority control →
  LESProofDerivedJointPolicy bridge system Authority live tier
lesApproximateROMActBranch {bridge = bridge} =
  Compiler.approximateROMActBranch (interface bridge)

record LESProofDerivedAdequacyBoundary : Set where
  constructor lesProofDerivedAdequacyBoundary
  field
    spacTierLabelAloneCreatesDecisionAdequacy : Bool
    spacTierLabelAloneCreatesDecisionAdequacyIsFalse :
      spacTierLabelAloneCreatesDecisionAdequacy ≡ false

    exactConsumerROMCanCreateAdequacy : Bool
    exactConsumerROMCanCreateAdequacyIsTrue :
      exactConsumerROMCanCreateAdequacy ≡ true

    approximateMarginReceiptCanCreateAdequacy : Bool
    approximateMarginReceiptCanCreateAdequacyIsTrue :
      approximateMarginReceiptCanCreateAdequacy ≡ true

    modelAdequacyRemainsSeparateFromRobustnessAndAuthority : Bool
    modelAdequacyRemainsSeparateFromRobustnessAndAuthorityIsTrue :
      modelAdequacyRemainsSeparateFromRobustnessAndAuthority ≡ true

canonicalLESProofDerivedAdequacyBoundary : LESProofDerivedAdequacyBoundary
canonicalLESProofDerivedAdequacyBoundary =
  lesProofDerivedAdequacyBoundary false refl true refl true refl true refl
