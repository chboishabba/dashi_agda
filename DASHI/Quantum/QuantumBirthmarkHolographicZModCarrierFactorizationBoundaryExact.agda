{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkHolographicZModCarrierFactorizationBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cross-kernel RT carrier-factorisation boundary
--
-- Sibling Lean PR #68 now uses pinned Mathlib equivalences
--
--   ZMod.finEquiv n
--   Equiv.finProdFinEquiv
--
-- together with 2^(k+r)=2^k*2^r to construct an explicit bijection
--
--   ZMod (2^(k+r))  ≃  Fin (2^k) × Fin (2^r).
--
-- This closes the finite carrier/cardinality/factor-index algebra that was
-- previously bundled into the RT same-object seam.  It deliberately does NOT
-- identify the first factor with the upstream depth-k subtree, chosen tensor
-- subsystem, reduced density matrix, geometric minimal cut, or physical AdS/CFT
-- boundary region.  Those are semantic/state/geometric payments, not carrier
-- bijection facts.
------------------------------------------------------------------------

record ZModCarrierFactorizationBoundary : Set where
  constructor zmodCarrierFactorizationBoundary
  field
    upstreamZModCarrierFactorizationSourceWritten : Bool
    carrierBijectionNoLongerRequired : Bool
    binaryProductIndexRoundTripSourceWritten : Bool
    depthKSubtreeSemanticIdentificationStillRequired : Bool
    reducedDensityMatrixSemanticIdentificationStillRequired : Bool
    minimalCutSemanticIdentificationStillRequired : Bool
    tensorNetworkStateIdentificationStillRequired : Bool
    physicalAdSCFTStillRequired : Bool

canonicalBoundary : ZModCarrierFactorizationBoundary
canonicalBoundary =
  zmodCarrierFactorizationBoundary
    true true true true true true true true

upstreamZModCarrierFactorizationSourceWritten : Bool
upstreamZModCarrierFactorizationSourceWritten = true

carrierBijectionNoLongerRequired : Bool
carrierBijectionNoLongerRequired = true

depthKSubtreeSemanticIdentificationStillRequired : Bool
depthKSubtreeSemanticIdentificationStillRequired = true

minimalCutSemanticIdentificationStillRequired : Bool
minimalCutSemanticIdentificationStillRequired = true

tensorNetworkStateIdentificationStillRequired : Bool
tensorNetworkStateIdentificationStillRequired = true

statusStatement : String
statusStatement =
  "Sibling Lean now constructs an explicit ZMod(2^(k+r)) <-> Fin(2^k) x Fin(2^r) equivalence with exact round trips. The upstream RT carrier-factorization/cardinality layer is therefore source-paid. Remaining RT debt is semantic same-object identification of the selected factor with the upstream depth-k subtree/reduced subsystem/minimal cut and of the corrected entangled state with the upstream tensor-network state; physical AdS/CFT remains separate."

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

carrierEquivalenceDoesNotIdentifySubsystem : Bool
carrierEquivalenceDoesNotIdentifySubsystem = true

carrierEquivalenceDoesNotConstructPartialTrace : Bool
carrierEquivalenceDoesNotConstructPartialTrace = true

carrierEquivalenceDoesNotProveMinimalCut : Bool
carrierEquivalenceDoesNotProveMinimalCut = true

carrierEquivalenceDoesNotIdentifyTensorNetworkState : Bool
carrierEquivalenceDoesNotIdentifyTensorNetworkState = true

carrierEquivalenceDoesNotImplyPhysicalHolography : Bool
carrierEquivalenceDoesNotImplyPhysicalHolography = true
