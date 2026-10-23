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
import DASHI.Biology.Psychedelic5HT2AAttentionBoundaryExact as Salience
import DASHI.Biology.PsychedelicVisualOperatorAlgebra as Visual

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

------------------------------------------------------------------------
-- Existing psychedelic prior art, not new empirical findings:
--  * Salience: measured LSD/receptor dependencies, candidate salience effects,
--    and a hard boundary before entity communication.
--  * Visual: separate endogenous generation, pattern completion, coupling,
--    prior precision, and uncalibrated psycho-perceptual parameters.
-- Derived visual features of the same Q do not add source-identifying data.
------------------------------------------------------------------------

existingSalienceDoesNotEstablishEntityCommunication :
  Salience.telepathicEntitySignalEstablished
    Salience.canonicalPsychedelic5HT2AAttentionBoundary ≡ false
existingSalienceDoesNotEstablishEntityCommunication =
  Salience.telepathicEntitySignalEstablishedIsFalse
    Salience.canonicalPsychedelic5HT2AAttentionBoundary

existingVisualParametersNotCalibrated :
  Visual.modelParametersAreEmpiricallyCalibrated
    Visual.canonicalVisualOperatorBoundary ≡ false
existingVisualParametersNotCalibrated =
  Visual.modelParametersAreEmpiricallyCalibratedIsFalse
    Visual.canonicalVisualOperatorBoundary

-- Any feature obtained by postprocessing the same observable Q (e.g.
-- endogenous geometric motifs or fitted visual operators) still cannot
-- distinguish two origin labels assigned to that identical observable.
-- New independent calibrated measurements may instead refine the fibre.
derivedPsychedelicFeaturesCannotUniquelyDecodeOrigin :
  ∀ {K F : Set}
  (q : K)
  (features : K → F)
  (decode : K → F → OriginHypothesis) →
  decode q (features q) ≡ endogenousModel →
  decode q (features q) ≡ independentAgentModel → ⊥
derivedPsychedelicFeaturesCannotUniquelyDecodeOrigin q features decode =
  noUniversalOriginDecoder q (λ law → decode law (features law))

-- A target-blind conditional-response class is genuinely testable if the
-- response masses are independently measured under locked randomized targets:
-- an observed target-specific difference excludes any response distribution
-- that is constant across those targets. The premise is an empirical debt.
-- This says nothing about which physical channel caused the difference.
targetDependentResponseExcludesTargetBlindModel :
  ∀ {Target Reply : Set}
  (observedMass : Target → Reply → Nat)
  (targetA targetB : Target)
  (reply : Reply)
  (blindMass : Reply → Nat) →
  (observedMass targetA reply ≡ observedMass targetB reply → ⊥) →
  observedMass targetA reply ≡ blindMass reply →
  observedMass targetB reply ≡ blindMass reply →
  ⊥
targetDependentResponseExcludesTargetBlindModel
  observedMass targetA targetB reply blindMass differs matchesA matchesB =
  differs (trans matchesA (sym matchesB))
