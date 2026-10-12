{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicTensorNetworkAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-STRENGTH AUDIT FOR THE INSPECTED HOLOGRAPHIC TENSOR NETWORK
--
-- Upstream source:
--   sneed-and-feed/adelic-spectral-zeta/
--   formalization/Formalization/Quantum/HolographicTensorNetwork.lean
--
-- Important distinctions found by direct source inspection:
--
--   * `holographicState n T` is a uniform pure-state amplitude, independent of T;
--   * `holographicContract n T` is diagonal maximally mixed, also independent of T;
--   * therefore the named contract is not the pure density matrix |psi><psi| of
--     the named state (which would have nonzero off-diagonal entries);
--   * sibling Lean PR #68 now source-writes this mismatch as an exact depth-one
--     no-go: the pure-state 0-1 coherence is strictly positive while the named
--     diagonal contract has exactly zero 0-1 coherence;
--   * hence the upstream state/contract same-object weld is impossible as the
--     definitions currently stand; one construction/identification must change;
--   * `canonicalQubitTensor` proves one parent->two-child isometry only; the
--     source does not prove the stronger all-bipartition perfect-tensor property
--     usually used in holographic-code / RT constructions;
--   * `treeEntanglementEntropy k` is defined to be k log 2 and the area-law
--     theorem is reflexive at that definition level;
--   * `ryu_takayanagi_discrete` supplies an existential real equal to k log 2,
--     but does not derive that value from the constructed state/contract.
--
-- Therefore the source contains a valid arithmetic area-law toy theorem, but
-- not yet a same-object RT entanglement-entropy derivation for its named tensor
-- network state.  This audit prevents the latter from being promoted.
------------------------------------------------------------------------

upstreamRepository : String
upstreamRepository = "sneed-and-feed/adelic-spectral-zeta"

upstreamSourcePath : String
upstreamSourcePath =
  "formalization/Formalization/Quantum/HolographicTensorNetwork.lean"

record HolographicTensorNetworkAudit : Set where
  constructor holographicTensorNetworkAudit
  field
    holographicStateDefined : Bool
    holographicContractDefined : Bool

    holographicStateDependsOnPerfectTensorArgument : Bool
    contractIgnoresPerfectTensorArgument : Bool

    holographicStateContractMismatch : Bool
    namedContractIsPureDensityMatrixOfNamedState : Bool
    upstreamStateContractMismatchSourceWrittenInLean : Bool
    upstreamStateContractSameObjectImpossibleAsWritten : Bool
    upstreamDefinitionReplacementRequired : Bool

    canonicalQubitTensorParentChildIsometryProved : Bool
    canonicalQubitTensorIsometryIsNotStrongPerfectTensorReceipt : Bool

    treeEntanglementEntropyDefinedAsKLogTwo : Bool
    rtTheoremIsDefinitionLevelAreaLaw : Bool
    rtEntropyDerivedFromConstructedBoundaryState : Bool
    upstreamRTNotDerivedFromConstructedBoundaryState : Bool

    correctedMaximallyEntangledCutModelRequired : Bool

canonicalHolographicTensorNetworkAudit : HolographicTensorNetworkAudit
canonicalHolographicTensorNetworkAudit =
  holographicTensorNetworkAudit
    true
    true
    false
    true
    true
    false
    true
    true
    true
    true
    true
    true
    true
    false
    true
    true

------------------------------------------------------------------------
-- Compact firewall names consumed by cross-lane code/tests.
------------------------------------------------------------------------

holographicStateContractMismatch : Bool
holographicStateContractMismatch = true

contractIgnoresPerfectTensorArgument : Bool
contractIgnoresPerfectTensorArgument = true

upstreamStateContractMismatchSourceWrittenInLean : Bool
upstreamStateContractMismatchSourceWrittenInLean = true

upstreamStateContractSameObjectImpossibleAsWritten : Bool
upstreamStateContractSameObjectImpossibleAsWritten = true

upstreamDefinitionReplacementRequired : Bool
upstreamDefinitionReplacementRequired = true

canonicalQubitTensorIsometryIsNotStrongPerfectTensorReceipt : Bool
canonicalQubitTensorIsometryIsNotStrongPerfectTensorReceipt = true

rtTheoremIsDefinitionLevelAreaLaw : Bool
rtTheoremIsDefinitionLevelAreaLaw = true

upstreamRTNotDerivedFromConstructedBoundaryState : Bool
upstreamRTNotDerivedFromConstructedBoundaryState = true

correctedMaximallyEntangledCutModelRequired : Bool
correctedMaximallyEntangledCutModelRequired = true

upstreamSameObjectRTAuditRecorded :
  upstreamRTNotDerivedFromConstructedBoundaryState ≡ true
upstreamSameObjectRTAuditRecorded = refl
