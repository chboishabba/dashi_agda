module DASHI.Algebra.Quantum.DASHIShorProductiveJoin where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Quantum.DASHIQuantumComputationProgram
open import DASHI.Algebra.Quantum.GeneralShor
open import DASHI.Crypto.RSAArithmeticCore
open import DASHI.Crypto.FiniteFactorArithmetic
open import DASHI.Crypto.RSAShorVulnerabilityBridge

------------------------------------------------------------------------
-- Highest-alpha productive join.
--
-- The existing DASHI quantum programme supplies reversible wave transport,
-- observation, semantic descent, compression, and normal forms. General Shor
-- supplies a finite QFT/hidden-period machine. RSA contributes the concrete
-- modular arithmetic target.
------------------------------------------------------------------------

record DASHIShorProductiveJoin : Set₂ where
  field
    quantumProgramme : QuantumComputationProgramme

    hiddenPeriodProblem : HiddenPeriodProblem
    periodFindingMachine :
      ShorPeriodFindingMachine hiddenPeriodProblem

    rsaPublicState : RSAPublicState
    rsaVulnerability :
      RSAShorVulnerability rsaPublicState

    semanticSeed :
      State (descentSystem quantumProgramme) → Nat

open DASHIShorProductiveJoin public

joinedRSAFactor :
  (J : DASHIShorProductiveJoin) →
  Σ Nat
    (λ d →
      FactorCertificate
        (publicModulus (rsaPublicState J))
        d)
joinedRSAFactor J = rsaShorFactor (rsaVulnerability J)

joinedHybridStep :
  (J : DASHIShorProductiveJoin) →
  State (descentSystem (quantumProgramme J)) →
  State (descentSystem (quantumProgramme J))
joinedHybridStep J =
  hybridStep
    (descentSystem (quantumProgramme J))
    (bridge (quantumProgramme J))
    (hybrid (quantumProgramme J))

joinedHybridCodeLengthDescent :
  (J : DASHIShorProductiveJoin) →
  ∀ s →
  codeLength
    (descentSystem (quantumProgramme J))
    (joinedHybridStep J s)
  ≤
  codeLength
    (descentSystem (quantumProgramme J))
    s
joinedHybridCodeLengthDescent J =
  hybrid-codeLength-descent
    (descentSystem (quantumProgramme J))
    (bridge (quantumProgramme J))
    (hybrid (quantumProgramme J))
