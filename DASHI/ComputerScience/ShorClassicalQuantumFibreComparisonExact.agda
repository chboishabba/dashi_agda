module DASHI.ComputerScience.ShorClassicalQuantumFibreComparisonExact where

open import DASHI.Core.Prelude

import DASHI.ComputerScience.FibreProgramComplexityExact as ClassicalComplexity
import DASHI.ComputerScience.QuantumExecutionFibreAdapterExact as QuantumComplexity
import DASHI.Crypto.ShorFactoring as Shor
import DASHI.Crypto.FiniteFactorArithmetic as Factor

------------------------------------------------------------------------
-- SAME ARITHMETIC CONSUMER, DIFFERENT EXECUTION FIBRES
--
-- The existing Shor owner deliberately separates the quantum order-finding
-- run from the certified classical factor extraction.  Once a successful
-- quantum run recovers the exact split order, both routes expose the same
-- certified arithmetic factor.  This does not identify their execution paths
-- or cost coordinates.
------------------------------------------------------------------------

sameCertifiedFactor :
  ∀ {N : Nat}
    (P : Shor.ShorFactoringProblem N)
    (R : Shor.QuantumShorFactoringRun P) →
  Shor.quantumShorFactor P R ≡ Shor.classicalShorFactor P
sameCertifiedFactor P R = refl

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
      Shor.quantumShorFactor P R ≡ Shor.classicalShorFactor P

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
    refl
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
