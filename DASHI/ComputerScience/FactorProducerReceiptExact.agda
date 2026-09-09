module DASHI.ComputerScience.FactorProducerReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Crypto.FiniteFactorArithmetic as Factor
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- FACTOR PRODUCER / VERIFIER / PROVENANCE FIBRE
--
-- A downstream consumer may care only that d divides N, while upstream
-- producers may be radically different: a classical order scan, Shor,
-- batch-GCD/shared-prime discovery, GNFS, an external announcement, etc.
--
-- This module keeps those coordinates distinct.  In particular:
--   * an externally checked multiplication identity is not a kernel proof;
--   * a valid factor does not reveal the algorithm that found it;
--   * cheap verification does not imply cheap discovery;
--   * equal factors from two producers do not identify their execution paths.
------------------------------------------------------------------------

data FactorProducerClass : Set where
  classicalOrderFindingProducer : FactorProducerClass
  quantumShorProducer : FactorProducerClass
  batchGCDSharedPrimeProducer : FactorProducerClass
  numberFieldSieveProducer : FactorProducerClass
  externallyAnnouncedProducer : FactorProducerClass
  unknownFactorProducer : FactorProducerClass

data FactorVerificationClass : Set where
  kernelFactorCertificate : FactorVerificationClass
  externallyCheckedArithmeticIdentity : FactorVerificationClass
  sourceReportedOnly : FactorVerificationClass

data FactorExecutionKnowledge : Set where
  executionPathKnown : FactorExecutionKnowledge
  executionMethodNamedButPathUnknown : FactorExecutionKnowledge
  executionMethodUnresolved : FactorExecutionKnowledge

data FactorCostKnowledge : Set where
  costReceiptAvailable : FactorCostKnowledge
  partialCostReceipt : FactorCostKnowledge
  costUnresolved : FactorCostKnowledge

-- Evidence is deliberately heterogeneous.  Small/formal fixtures can carry the
-- repository's actual FactorCertificate, while externally sourced large-number
-- facts can remain string-indexed until a dedicated big-integer kernel lane
-- supplies the corresponding certificate.

data FactorEvidence : Set where
  certifiedFactorEvidence :
    (N d : Nat) →
    Factor.FactorCertificate N d →
    FactorEvidence

  externalFactorIdentityEvidence :
    (modulusReference : String) →
    (factorReference : String) →
    (cofactorReference : String) →
    (verificationReference : String) →
    FactorEvidence

record FactorProducerReceipt : Set where
  constructor factorProducerReceipt
  field
    evidence : FactorEvidence
    producerClass : FactorProducerClass
    verificationClass : FactorVerificationClass
    executionKnowledge : FactorExecutionKnowledge
    costKnowledge : FactorCostKnowledge
    provenanceReference : String
    methodReference : String
    complexityReference : String

open FactorProducerReceipt public

------------------------------------------------------------------------
-- Canonical small certified fixtures already owned by the crypto stack.
------------------------------------------------------------------------

factor15ClassicalReceipt : FactorProducerReceipt
factor15ClassicalReceipt =
  factorProducerReceipt
    (certifiedFactorEvidence 15 3 Factor.factor3Of15)
    classicalOrderFindingProducer
    kernelFactorCertificate
    executionPathKnown
    costReceiptAvailable
    "DASHI.Crypto.FiniteFactorArithmetic.factor3Of15"
    "ordinary order/modexp/Euclid machine descent"
    "consumer-indexed classical machine path costs are owned by the CS factoring descent"

factor15QuantumReceipt : FactorProducerReceipt
factor15QuantumReceipt =
  factorProducerReceipt
    (certifiedFactorEvidence 15 3 Factor.factor3Of15)
    quantumShorProducer
    kernelFactorCertificate
    executionPathKnown
    partialCostReceipt
    "DASHI.Crypto.FiniteFactorArithmetic.factor3Of15"
    "certified Shor order-finding/factor extraction"
    "quantum gate/depth/qubit costs remain distinct from classical transition costs"

factor21ClassicalReceipt : FactorProducerReceipt
factor21ClassicalReceipt =
  factorProducerReceipt
    (certifiedFactorEvidence 21 7 Factor.factor7Of21)
    classicalOrderFindingProducer
    kernelFactorCertificate
    executionPathKnown
    costReceiptAvailable
    "DASHI.Crypto.FiniteFactorArithmetic.factor7Of21"
    "ordinary order/modexp/Euclid machine descent"
    "consumer-indexed classical machine path costs are owned by the CS factoring descent"

factor21QuantumReceipt : FactorProducerReceipt
factor21QuantumReceipt =
  factorProducerReceipt
    (certifiedFactorEvidence 21 7 Factor.factor7Of21)
    quantumShorProducer
    kernelFactorCertificate
    executionPathKnown
    partialCostReceipt
    "DASHI.Crypto.FiniteFactorArithmetic.factor7Of21"
    "certified Shor order-finding/factor extraction"
    "quantum gate/depth/qubit costs remain distinct from classical transition costs"

------------------------------------------------------------------------
-- RSA-260: external factor identity, method deliberately unresolved.
------------------------------------------------------------------------

rsa260ExternalReceipt : FactorProducerReceipt
rsa260ExternalReceipt =
  factorProducerReceipt
    (externalFactorIdentityEvidence
      "RSA-260 (260 decimal digits / 862 bits)"
      "4397328654844826923795068102505872571721883526553349659561256924505973939597593482272505698004801207988043088656411102133523080581"
      "published complementary 130-digit factor"
      "external arbitrary-precision multiplication check reconstructs RSA-260; dedicated kernel big-integer certificate deferred")
    externallyAnnouncedProducer
    externallyCheckedArithmeticIdentity
    executionMethodUnresolved
    costUnresolved
    "Eric Lu (@penlume), public factor announcement, 2026-09-03"
    "no public method receipt admitted here"
    "algorithm/runtime/hardware/resource profile unresolved"

------------------------------------------------------------------------
-- Consumer-relative firewalls.
------------------------------------------------------------------------

data EqualFactorImpliesEqualProducer : Set where
data EasyVerificationImpliesEasyDiscovery : Set where
data ExternalArithmeticCheckIsKernelCertificate : Set where
data UnknownMethodMayBeClassifiedAsQuantum : Set where

equalFactorDoesNotIdentifyProducer : EqualFactorImpliesEqualProducer → ⊥
equalFactorDoesNotIdentifyProducer ()

easyVerificationDoesNotBoundDiscovery : EasyVerificationImpliesEasyDiscovery → ⊥
easyVerificationDoesNotBoundDiscovery ()

externalCheckDoesNotBecomeKernelCertificate :
  ExternalArithmeticCheckIsKernelCertificate → ⊥
externalCheckDoesNotBecomeKernelCertificate ()

unknownMethodCannotBePromotedToQuantum : UnknownMethodMayBeClassifiedAsQuantum → ⊥
unknownMethodCannotBePromotedToQuantum ()

canonicalFactorProducerReceipt : Receipt.GenericReceipt
canonicalFactorProducerReceipt =
  Receipt.mkNonPromotingReceipt
    "factor producer/verifier fibre"
    "DASHI.ComputerScience.FactorProducerReceiptExact"
    "FactorProducerReceipt"
    "separates factor evidence, producer class, verification status, execution knowledge, complexity knowledge, and provenance"
    "generic producer-specific correctness/cost compilers and dedicated RSA-260 kernel big-integer certification remain downstream obligations"
    "agda -i . DASHI/ComputerScience/FactorProducerReceiptExact.agda"
