module DASHI.Environment.LESProofDerivedDecisionAdequacyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ConsumerRelativeReductionKernelExact as Reduction
import DASHI.Core.ConsumerRelativeApproximateFidelityBridgeExact as Approx
import DASHI.Core.ConsumerRelativeReductionSearchExact as Search
import DASHI.Core.ConsumerDecisionAdequacyFromReductionExact as Adequacy
import DASHI.Core.ConsumerAdequacyJointPolicyBidiCompilerExact as Compiler
import DASHI.Core.RobustInterventionAcrossHypothesesExact as Robust
import DASHI.Environment.LESDomainBasisBidiFrontierExact as Basis
import DASHI.Environment.LESAdaptiveSPACModelSearchExact as SPAC

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

------------------------------------------------------------------------
-- Direct LES candidate-search route.  This is the literal forward half of the
-- bidi architecture: candidate certification constructs the exact ROM consumed
-- by the decision-adequacy/action compiler.
------------------------------------------------------------------------

lesCertifiedCandidateActBranch :
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
    {candidate : Search.ReductionCandidate
      (Basis.State mechanism)
      (Basis.Control mechanism)
      (Basis.Observation mechanism)
      (Basis.evolve mechanism)
      (Basis.observe mechanism)}
    (certificate : Search.CandidateCertification candidate) →
  ExactRealises bridge tier (Search.certificationAsReduction certificate) →
  (decide : Basis.Observation mechanism → Basis.Control mechanism) →
  Adequacy.ExactDecisionAdequacy
    (Search.certificationAsReduction certificate) decide control →
  Robust.RobustlyNoWorseThanBaseline system live control →
  Authority control →
  LESProofDerivedJointPolicy bridge system Authority live tier
lesCertifiedCandidateActBranch {bridge = bridge} =
  Compiler.certifiedCandidateActBranch (interface bridge)

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
    certifiedSPACCandidateCanFeedDecisionAdequacy : Bool
    certifiedSPACCandidateCanFeedDecisionAdequacyIsTrue :
      certifiedSPACCandidateCanFeedDecisionAdequacy ≡ true
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
  lesProofDerivedAdequacyBoundary
    false refl true refl true refl true refl true refl
