module DASHI.ComputerScience.ShorClassicalQuantumFibreComparisonExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.FibreProgramComplexityExact as ClassicalComplexity
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as QuantumComplexity
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.ShorQuantumRunFactorTransportExact as QuantumFactor
import DASHI.Crypto.FiniteFactorArithmetic as Factor

------------------------------------------------------------------------
-- SAME ARITHMETIC CONSUMER, DIFFERENT EXECUTION FIBRES
--
-- The certified quantum order-finding run now feeds factor extraction through
-- an equality transport from the recovered order to the existing certified
-- split order.  The common factor result is therefore a theorem about those
-- two routes, not a definitional consequence of discarding the quantum run.
------------------------------------------------------------------------

sameCertifiedFactor :
  ∀ {N : Nat}
    (P : Shor.ShorFactoringProblem N)
    (R : Shor.QuantumShorFactoringRun P) →
  QuantumFactor.quantumShorFactorFromRecoveredOrder P R
  ≡ Shor.classicalShorFactor P
sameCertifiedFactor = QuantumFactor.quantumRecoveredOrderFactorAgreesWithClassical

quantumRecoveredOrderExact :
  ∀ {N : Nat}
    (P : Shor.ShorFactoringProblem N)
    (R : Shor.QuantumShorFactoringRun P) →
  Shor.quantumRecoveredOrder P R ≡ Shor.order P
quantumRecoveredOrderExact = Shor.quantumRecoveredOrderIsSplitOrder

record ClassicalQuantumFactorComparison
    {N : Nat}
    (P : Shor.ShorFactoringProblem N)
    (R : Shor.QuantumShorFactoringRun P) : Set₁ where
  constructor classicalQuantumFactorComparison
  field
    sameFactorCertificate :
      QuantumFactor.quantumShorFactorFromRecoveredOrder P R
      ≡ Shor.classicalShorFactor P

    classicalCostProfile : ClassicalComplexity.ComplexityProfile
    quantumCostProfile : QuantumComplexity.QuantumCostProfile

    sameArithmeticResultImpliesSameExecutionPath : Bool
    classicalTransitionCountEqualsQuantumGateCountByDefinition : Bool
    quantumSuccessEvidenceIsSeparate : Bool
    physicalCostComparisonAlreadyClosed : Bool

open ClassicalQuantumFactorComparison public

mkComparison :
  ∀ {N : Nat}
    (P : Shor.ShorFactoringProblem N)
    (R : Shor.QuantumShorFactoringRun P)
    (classicalCost : ClassicalComplexity.ComplexityProfile)
    (quantumCost : QuantumComplexity.QuantumCostProfile) →
  ClassicalQuantumFactorComparison P R
mkComparison P R classicalCost quantumCost =
  classicalQuantumFactorComparison
    (QuantumFactor.quantumRecoveredOrderFactorAgreesWithClassical P R)
    classicalCost
    quantumCost
    false
    false
    true
    false

record ShorClassicalQuantumBoundary : Set where
  constructor shorClassicalQuantumBoundary
  field
    sameCertifiedFactor : Bool
    sameExecutionSemantics : Bool
    quantumOrderRecoveryRequiresSuccessEvidence : Bool
    quantumAndClassicalCostsGloballyComparableWithoutConsumer : Bool
    quantumFibreIsBinaryOrTernaryStorageEncoding : Bool

canonicalShorClassicalQuantumBoundary : ShorClassicalQuantumBoundary
canonicalShorClassicalQuantumBoundary =
  shorClassicalQuantumBoundary true false true false false
