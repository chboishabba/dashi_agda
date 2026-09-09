module DASHI.ComputerScience.TernaryDecisionCertificationProductExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.ComputerScience.FactorProducerReceiptExact as FactorReceipt
import DASHI.ComputerScience.ConsumerIndexedTernarySearchKernelExact as Decision
import DASHI.ComputerScience.TernaryProofSearchDecisionDebtBridgeExact as ProofDecision

------------------------------------------------------------------------
-- TERNARY DECISION STATUS × CERTIFICATION / PROVENANCE
--
-- The generic decision/provenance product is now owned centrally.  This module
-- specialises it to factor receipts and exposes the proof-search specialization.
------------------------------------------------------------------------

FactorDecisionPacket : Set
FactorDecisionPacket = Decision.TernaryDecisionPacket FactorReceipt.FactorProducerReceipt

-- Small in-repo factor: positive decision with an actual kernel certificate.
factor15KernelPositive : FactorDecisionPacket
factor15KernelPositive =
  Decision.ternaryDecisionPacket pos FactorReceipt.factor15ClassicalReceipt

-- Same factor, different producer fibre: still positive, but quantum producer.
factor15QuantumPositive : FactorDecisionPacket
factor15QuantumPositive =
  Decision.ternaryDecisionPacket pos FactorReceipt.factor15QuantumReceipt

-- RSA-260: positive external arithmetic verification while method/cost remain
-- unresolved and kernel big-integer certification remains downstream.
rsa260ExternalPositive : FactorDecisionPacket
rsa260ExternalPositive =
  Decision.ternaryDecisionPacket pos FactorReceipt.rsa260ExternalReceipt

-- Unknown/source-only candidate can remain unresolved without being converted
-- into a negative claim.
unresolvedFactorCandidate : FactorReceipt.FactorProducerReceipt → FactorDecisionPacket
unresolvedFactorCandidate receipt = Decision.ternaryDecisionPacket zer receipt

------------------------------------------------------------------------
-- Proof-search uses the same generic trit × provenance product underneath its
-- more specific finite-search packet, while retaining debt/admission semantics.
------------------------------------------------------------------------

ProofSearchDecisionPacket : Set₁
ProofSearchDecisionPacket = ProofDecision.ProofSearchDecisionPacket

proofSearchUnresolved : ProofSearchDecisionPacket
proofSearchUnresolved = ProofDecision.canonicalDeferredUnresolvedPacket

proofSearchPositive : ProofSearchDecisionPacket
proofSearchPositive = ProofDecision.canonicalDeferredPositiveSearchPacket

proofSearchFiniteNegative : ProofSearchDecisionPacket
proofSearchFiniteNegative = ProofDecision.canonicalDeferredNegativeFiniteSearchPacket

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PositiveDecisionImpliesKernelCertification : Set where
data PositiveDecisionIdentifiesProducer : Set where
data UnresolvedDecisionMeansNegative : Set where
data CertificationClassIsDecisionTrit : Set where

positiveDoesNotImplyKernelCertification :
  PositiveDecisionImpliesKernelCertification → ⊥
positiveDoesNotImplyKernelCertification ()

positiveDoesNotIdentifyProducer : PositiveDecisionIdentifiesProducer → ⊥
positiveDoesNotIdentifyProducer ()

unresolvedDoesNotMeanNegative : UnresolvedDecisionMeansNegative → ⊥
unresolvedDoesNotMeanNegative ()

certificationIsNotDecisionStatus : CertificationClassIsDecisionTrit → ⊥
certificationIsNotDecisionStatus ()

record TernaryDecisionCertificationBoundary : Set where
  constructor ternaryDecisionCertificationBoundary
  field
    genericDecisionProvenanceProductReused : Bool
    ternaryDecisionAndCertificationSeparate : Bool
    positiveKernelFactorRepresentable : Bool
    positiveExternalFactorRepresentable : Bool
    samePositiveDecisionMayHaveDifferentProducer : Bool
    unresolvedCandidateRepresentable : Bool
    positiveAutomaticallyKernelCertified : Bool
    unresolvedAutomaticallyNegative : Bool
    proofSearchIntegratedHere : Bool

canonicalTernaryDecisionCertificationBoundary :
  TernaryDecisionCertificationBoundary
canonicalTernaryDecisionCertificationBoundary =
  ternaryDecisionCertificationBoundary
    true true true true true true false false true
