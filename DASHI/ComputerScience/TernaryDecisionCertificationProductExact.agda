module DASHI.ComputerScience.TernaryDecisionCertificationProductExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.ComputerScience.FactorProducerReceiptExact as FactorReceipt
import DASHI.ComputerScience.TernaryProofSearchDecisionDebtBridgeExact as ProofDecision

------------------------------------------------------------------------
-- TERNARY DECISION STATUS × CERTIFICATION / PROVENANCE
--
-- A trit says only whether the declared decision consumer is negative,
-- unresolved, or positive.  It does not by itself say how that verdict was
-- certified or produced.  Those coordinates remain in the receipt fibre.
------------------------------------------------------------------------

record FactorDecisionPacket : Set where
  constructor factorDecisionPacket
  field
    decision : Trit
    receipt : FactorReceipt.FactorProducerReceipt

open FactorDecisionPacket public

-- Small in-repo factor: positive decision with an actual kernel certificate.
factor15KernelPositive : FactorDecisionPacket
factor15KernelPositive =
  factorDecisionPacket pos FactorReceipt.factor15ClassicalReceipt

-- Same factor, different producer fibre: still positive, but quantum producer.
factor15QuantumPositive : FactorDecisionPacket
factor15QuantumPositive =
  factorDecisionPacket pos FactorReceipt.factor15QuantumReceipt

-- RSA-260: positive external arithmetic verification while method/cost remain
-- unresolved and kernel big-integer certification remains downstream.
rsa260ExternalPositive : FactorDecisionPacket
rsa260ExternalPositive =
  factorDecisionPacket pos FactorReceipt.rsa260ExternalReceipt

-- Unknown/source-only candidate can remain unresolved without being converted
-- into a negative claim.
unresolvedFactorCandidate : FactorReceipt.FactorProducerReceipt → FactorDecisionPacket
unresolvedFactorCandidate receipt = factorDecisionPacket zer receipt

------------------------------------------------------------------------
-- Proof-search uses the same decision carrier but retains its own proof-debt,
-- admission and finite-exhaustion semantics in the dedicated bridge.
------------------------------------------------------------------------

ProofSearchDecisionPacket : Set
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
    true true true true true false false true
