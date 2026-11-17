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
import DASHI.Cognition.KlueverFormConstantProjection as Kluver
import DASHI.Cognition.VisualTuringKlueverBridge as VisualTuring
import DASHI.Cognition.ModeSelectionToProjectionLaw as ModeLaw
import DASHI.Cognition.CorticalLogPolarProjectionGeometry as Cortical
import DASHI.Biology.TuringPatternRegimeSurface as Turing
import DASHI.Cognition.Kluver5HT2ACrossPollinationExact as Kluver5HT2A

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

------------------------------------------------------------------------
-- Klüver / Kluever source-specific prior art.
--
-- Heinrich Klüver's historical mescal-vision classification is attributed in
-- the existing KluverLogPolar5HT2ASourceAtlasExact. Bressloff et al. 2001
-- and Ermentrout/Cowan 1979 own the source-side cortical pattern account.
-- DASHI.Cognition.ModeSelectionToProjectionLaw ALREADY proves the concrete
-- distinct-stripes/spots -> same lattice relation, and non-totality. We
-- consume that same witness, not a new encoding of the four form constants.
------------------------------------------------------------------------

klueverModeLaw : ModeLaw.ManyToOneLatticeWitness
klueverModeLaw = ModeLaw.canonicalManyToOneLatticeWitness

-- The pre-existing proof has a local empty type. Transport its impossible
-- case to the standard empty type without assuming them definitionally equal.
modeLawImpossible : ModeLaw.⊥ → ⊥
modeLawImpossible ()

-- No function assigning a single underlying Turing family to every lattice
-- report can be correct on both already-proved admissible projections.
-- This is stronger than merely labelling Klüver projection "lossy".
klueverLatticeNoUniformInverse :
  (decode : Kluver.KlueverForm → Turing.TuringPatternFamily) →
  ((family : Turing.TuringPatternFamily) →
   VisualTuring.ProjectsAsKluever family Kluver.latticeGrating →
   decode Kluver.latticeGrating ≡ family) →
  ⊥
klueverLatticeNoUniformInverse decode claimsInverse =
  modeLawImpossible
    (ModeLaw.stripe≢spot
      (trans
        (sym (claimsInverse Turing.stripeFamily
          VisualTuring.stripesAsLattice))
        (claimsInverse Turing.spotFamily
          VisualTuring.spotsAsLattice)))

-- A second independent degeneracy: cortical angular- and radial-periodic
-- features can each project to the same cobweb percept in the original
-- CorticalLogPolarProjectionGeometry relation. This too is a source-bounded
-- synthetic consequence, not a claim of experimentally measured V1 fields.
radialPeriodIsNotAngularPeriod :
  Cortical.radialPeriodicity ≡ Cortical.angularPeriodicity → ⊥
radialPeriodIsNotAngularPeriod ()

cobwebNoUniformCorticalFeatureInverse :
  (decode : Kluver.KlueverForm → Cortical.VisualModeFeature) →
  ((feature : Cortical.VisualModeFeature) →
   Cortical.FeatureProjectsAs feature Kluver.radialCobweb →
   decode Kluver.radialCobweb ≡ feature) →
  ⊥
cobwebNoUniformCorticalFeatureInverse decode claimsInverse =
  radialPeriodIsNotAngularPeriod
    (trans
      (sym (claimsInverse Cortical.radialPeriodicity
        Cortical.radialPeriodAsCobweb))
      (claimsInverse Cortical.angularPeriodicity
        Cortical.angularPeriodAsCobweb))

-- Original CROSS-POLLINATION owner already distinguishes the proven finite
-- visual geometry from the still-uncalibrated drug-to-visual mechanism.
existingKluver5HT2ACompositeIsNotCalibrated :
  Kluver5HT2A.jointMechanismEmpiricallyClosed
    Kluver5HT2A.canonicalKluver5HT2ACrossPollination ≡ false
existingKluver5HT2ACompositeIsNotCalibrated =
  Kluver5HT2A.jointMechanismEmpiricallyClosedIsFalse
    Kluver5HT2A.canonicalKluver5HT2ACrossPollination

existingKluverSalienceDoesNotIdentifyExternalAgency :
  Kluver5HT2A.feltImportanceProvesExternalAgency
    Kluver5HT2A.canonicalKluver5HT2ACrossPollination ≡ false
existingKluverSalienceDoesNotIdentifyExternalAgency =
  Kluver5HT2A.feltImportanceProvesExternalAgencyIsFalse
    Kluver5HT2A.canonicalKluver5HT2ACrossPollination

-- Crucial separation of operators:
-- Klüver uses a (generally many-to-one and partial) mode -> observed-form
-- projection. Markov first-return traces use a subset of Markov *states*.
-- The first operation need not preserve a one-step Markov transition law.
-- Therefore T_V(Q) for neural states cannot silently be identified with
-- a Markov kernel on reported Klüver labels. The repository's original
-- finite bisimulation/lumping counterexample above enforces this distinction.
