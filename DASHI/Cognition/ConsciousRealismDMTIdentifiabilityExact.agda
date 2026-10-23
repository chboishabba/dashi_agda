module DASHI.Cognition.ConsciousRealismDMTIdentifiabilityExact where

------------------------------------------------------------------------
-- Mathematical cut only: this is NOT evidence of independent DMT entities.
-- Hoffman/Prakash 2014 and Hoffman/Prakash/Prentner 2023 own the kernel
-- framework; Hoffman/Prakash/Chattopadhyay own trace-chain theory;
-- Gallimore/Hermansson/Hoffman 2026 own their DMT hypothesis.
-- The conditional identity and non-decoding statements are DASHI deductions.
------------------------------------------------------------------------
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
open import Data.Empty using (⊥)
import DASHI.Core.FiniteStochasticBisimulationExact as Stochastic
import DASHI.Cognition.ConsciousRealismDMTSourceAtlasExact as Sources

-- A concrete stochastic matrix instance must discharge normalization separately.
record KernelComposition (K : Set) : Set where
  constructor kernelComposition
  field
    sequential : K → K → K
    identity : K
    rightIdentity : (q : K) → sequential q identity ≡ q
    leftIdentity : (q : K) → sequential identity q ≡ q
open KernelComposition public

qualiaKernel : ∀ {K : Set} → KernelComposition K → K → K → K → K
qualiaKernel alg decision action perception =
  sequential alg (sequential alg decision action) perception

-- For any kernel algebra, the formal factorisation Q = Q I I exists.
-- It does not uniquely identify latent physical or conscious mechanisms.
anyKernelAdmitsIdentityFactorisation :
  ∀ {K : Set} (alg : KernelComposition K) (q : K) →
  qualiaKernel alg q (identity alg) (identity alg) ≡ q
anyKernelAdmitsIdentityFactorisation alg q =
  trans
    (cong (λ x → sequential alg x (identity alg))
      (rightIdentity alg q))
    (rightIdentity alg q)

data OriginHypothesis : Set where
  endogenousModel : OriginHypothesis
  independentAgentModel : OriginHypothesis

record InterpretedKernel (K : Set) : Set where
  constructor interpretedKernel
  field
    observableLaw : K
    originInterpretation : OriginHypothesis
open InterpretedKernel public

internalInterpretation : ∀ {K : Set} → K → InterpretedKernel K
internalInterpretation q = interpretedKernel q endogenousModel

externalInterpretation : ∀ {K : Set} → K → InterpretedKernel K
externalInterpretation q = interpretedKernel q independentAgentModel

sameObservableLaw : ∀ {K : Set} (q : K) →
  observableLaw (internalInterpretation q) ≡
  observableLaw (externalInterpretation q)
sameObservableLaw q = refl

endogenousIsNotIndependent :
  endogenousModel ≡ independentAgentModel → ⊥
endogenousIsNotIndependent ()

-- No classifier of just the shared observable law can be universally
-- correct on two otherwise unrestricted, differently tagged hypotheses.
noUniversalOriginDecoder :
  ∀ {K : Set} (q : K) (decoder : K → OriginHypothesis) →
  decoder q ≡ endogenousModel →
  decoder q ≡ independentAgentModel → ⊥
noUniversalOriginDecoder q decoder internalCorrect externalCorrect =
  endogenousIsNotIndependent (trans (sym internalCorrect) externalCorrect)

-- Zero cooperation makes an external-channel story observationally null.
-- We do not assert any external channel or any physiological mechanism.
data Cooperation : Set where
  noncooperating : Cooperation
  cooperating : Cooperation

record ResponseMasses (Target Reply : Set) : Set where
  field
    nullMass : Target → Reply → Nat
    cooperatingMass : Target → Reply → Nat
open ResponseMasses public

agentResponseMass : ∀ {Target Reply : Set} →
  ResponseMasses Target Reply → Cooperation → Target → Reply → Nat
agentResponseMass channel noncooperating target reply =
  nullMass channel target reply
agentResponseMass channel cooperating target reply =
  cooperatingMass channel target reply

zeroCooperationSameAsNull : ∀ {Target Reply : Set}
  (channel : ResponseMasses Target Reply) (target : Target) (reply : Reply) →
  agentResponseMass channel noncooperating target reply ≡
  nullMass channel target reply
zeroCooperationSameAsNull channel target reply = refl

-- Reuse existing repository theorem: same current observation quotient
-- need not entail identical future transitions under intervention.
existingBisimulationDefectPrecludesUniversalLumping :
  Stochastic.KernelBisimulation Stochastic.demoKernel → ⊥
existingBisimulationDefectPrecludesUniversalLumping candidate =
  Stochastic.kernelDefectContradictsBisimulation
    candidate Stochastic.demoKernelDefect

record DMTClaimBoundary : Set where
  constructor dmtClaimBoundary
  field
    kernelFactorisationProvesExternalAgents : Bool
    kernelFactorisationProvesExternalAgentsIsFalse :
      kernelFactorisationProvesExternalAgents ≡ false
    traceAlgebraAloneIdentifiesNeuralStates : Bool
    traceAlgebraAloneIdentifiesNeuralStatesIsFalse :
      traceAlgebraAloneIdentifiesNeuralStates ≡ false
    thisModuleContainsParticipantEvidence : Bool
    thisModuleContainsParticipantEvidenceIsFalse :
      thisModuleContainsParticipantEvidence ≡ false
    changedKernelMustSatisfyFixedKernelTraceLaw : Bool
    changedKernelMustSatisfyFixedKernelTraceLawIsFalse :
      changedKernelMustSatisfyFixedKernelTraceLaw ≡ false

canonicalDMTClaimBoundary : DMTClaimBoundary
canonicalDMTClaimBoundary =
  dmtClaimBoundary false refl false refl false refl false refl
