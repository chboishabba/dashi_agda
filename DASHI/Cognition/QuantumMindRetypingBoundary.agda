module DASHI.Cognition.QuantumMindRetypingBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.BalancedTernary as BT
import DASHI.Cognition.CognitiveVacuumClassBoundary as Vacuum
import DASHI.Cognition.DashiCognitiveSystem as Cognitive
import DASHI.Cognition.PhysicalCouplingFactorisation as Coupling

------------------------------------------------------------------------
-- The word "quantum" is split into three authority levels.  Only the
-- structural lane is internal to this formalism.  A physical mechanism must
-- arrive through an independently measured coupling witness.
------------------------------------------------------------------------

data QuantumUsage : Set where
  structuralAnalogy : QuantumUsage
  physicalMechanism : QuantumUsage
  phenomenalMetaphor : QuantumUsage

data RetypedQuantumFeature : Set where
  indefiniteCommitment : RetypedQuantumFeature
  branchCommitment : RetypedQuantumFeature
  crossScaleConstraintCoupling : RetypedQuantumFeature
  quotientDegeneracy : RetypedQuantumFeature
  multiscaleDefectMinimum : RetypedQuantumFeature

data PopularQuantumClaim : Set where
  superpositionClaim : PopularQuantumClaim
  collapseClaim : PopularQuantumClaim
  nonlocalityClaim : PopularQuantumClaim
  coherentBrainStateClaim : PopularQuantumClaim
  microtubuleQubitClaim : PopularQuantumClaim
  goedelConsciousnessClaim : PopularQuantumClaim
  quantumCauseOfConsciousnessClaim : PopularQuantumClaim

retypeStructural : PopularQuantumClaim → List RetypedQuantumFeature
retypeStructural superpositionClaim = indefiniteCommitment ∷ quotientDegeneracy ∷ []
retypeStructural collapseClaim = branchCommitment ∷ []
retypeStructural nonlocalityClaim = crossScaleConstraintCoupling ∷ []
retypeStructural coherentBrainStateClaim = []
retypeStructural microtubuleQubitClaim = []
retypeStructural goedelConsciousnessClaim = []
retypeStructural quantumCauseOfConsciousnessClaim = []

------------------------------------------------------------------------
-- The ternary zero lane is applicability without positive commitment.  It is
-- a structural analogue of unresolved choice, not a Hilbert-space state.
------------------------------------------------------------------------

structuralIndefiniteness : BT.Trit
structuralIndefiniteness = BT.zero

structuralCommitment : BT.Trit
structuralCommitment = BT.pos

zeroIsNonCommitted : structuralIndefiniteness ≡ BT.zero
zeroIsNonCommitted = refl

positiveIsCommitted : structuralCommitment ≡ BT.pos
positiveIsCommitted = refl

record DecisionProjection
    (system : Cognitive.DASHICognitiveSystem)
    (control : Cognitive.Control system)
    (source : Cognitive.Configuration system)
    (token : BT.Trit) : Set where
  field
    target : Cognitive.Configuration system
    targetIsStep :
      target ≡ Cognitive.stepConfiguration system control source token

open DecisionProjection public

canonicalDecisionProjection :
  ∀ {system control source token} →
  DecisionProjection system control source token
canonicalDecisionProjection {system} {control} {source} {token} = record
  { target = Cognitive.stepConfiguration system control source token
  ; targetIsStep = refl
  }

------------------------------------------------------------------------
-- Vacuum structure is explicitly additional to stable observational class.
-- This imports the already-proved separation rather than identifying every
-- stable cognitive class with an energy vacuum.
------------------------------------------------------------------------

StableNeedNotBeVacuum : Set
StableNeedNotBeVacuum =
  Vacuum.VacuumClass
    Vacuum.booleanCognitiveSystem
    Vacuum.booleanDefectModel
    false
  → ⊥

stableNeedNotBeVacuum : StableNeedNotBeVacuum
stableNeedNotBeVacuum = Vacuum.falseStableClassIsNotVacuum

------------------------------------------------------------------------
-- Physical candidates are optional implementations.  They do not alter the
-- alphabet and are admitted only as typed couplings to the hidden carrier or
-- stack maintenance layer.
------------------------------------------------------------------------

data CandidateImplementation : Set where
  biochemicalRouting : CandidateImplementation
  electromagneticCoupling : CandidateImplementation
  tunnellingRouting : CandidateImplementation
  microtubuleDynamics : CandidateImplementation
  ordinaryNetworkDynamics : CandidateImplementation

record PhysicalCandidateBinding
    (system : Cognitive.DASHICognitiveSystem) : Set₁ where
  field
    implementation : CandidateImplementation
    stateCoupling : Coupling.PhysicalSemanticFactorisation system
    measuredBinding : Bool
    causalBinding : Bool

open PhysicalCandidateBinding public

record QuantumMindAuthorityBoundary : Set where
  constructor quantumMindAuthorityBoundary
  field
    structuralRetypingDefined : Bool
    ternaryCommitmentDefined : Bool
    quotientDegeneracyDefined : Bool
    multiscaleVacuumMinimumDefined : Bool
    longLivedCoherenceEstablished : Bool
    microtubuleQubitsEstablished : Bool
    objectiveCollapseRequired : Bool
    goedelImpliesConsciousness : Bool
    quantumCauseEstablished : Bool

canonicalQuantumMindBoundary : QuantumMindAuthorityBoundary
canonicalQuantumMindBoundary =
  quantumMindAuthorityBoundary
    true true true true
    false false false false false

coherenceStillExternal :
  QuantumMindAuthorityBoundary.longLivedCoherenceEstablished
    canonicalQuantumMindBoundary ≡ false
coherenceStillExternal = refl

microtubuleQubitsStillExternal :
  QuantumMindAuthorityBoundary.microtubuleQubitsEstablished
    canonicalQuantumMindBoundary ≡ false
microtubuleQubitsStillExternal = refl

collapseNotRequired :
  QuantumMindAuthorityBoundary.objectiveCollapseRequired
    canonicalQuantumMindBoundary ≡ false
collapseNotRequired = refl

goedelPromotionBlocked :
  QuantumMindAuthorityBoundary.goedelImpliesConsciousness
    canonicalQuantumMindBoundary ≡ false
goedelPromotionBlocked = refl

quantumCausalityStillExternal :
  QuantumMindAuthorityBoundary.quantumCauseEstablished
    canonicalQuantumMindBoundary ≡ false
quantumCausalityStillExternal = refl

------------------------------------------------------------------------
-- Named historical programmes are represented only as claim profiles.  This
-- records what can be translated structurally and what remains outside the
-- theorem layer; it does not assert a historical or empirical verdict.
------------------------------------------------------------------------

data Programme : Set where
  bohmProgramme : Programme
  penroseProgramme : Programme
  orchORProgramme : Programme
  decoherenceObjection : Programme
  cnetProgramme : Programme

record ProgrammeRetyping : Set where
  constructor programmeRetyping
  field
    programme : Programme
    structuralContent : List RetypedQuantumFeature
    requiresPhysicalBinding : Bool
    establishesConsciousness : Bool
    reading : String

bohmRetyping : ProgrammeRetyping
bohmRetyping = programmeRetyping
  bohmProgramme
  (quotientDegeneracy ∷ crossScaleConstraintCoupling ∷ [])
  false
  false
  "Implicate-order language is retained only as a structural analogy to pre-projection quotient structure."

penroseRetyping : ProgrammeRetyping
penroseRetyping = programmeRetyping
  penroseProgramme
  (quotientDegeneracy ∷ branchCommitment ∷ [])
  false
  false
  "Classwise reasoning and quotient dependence survive; Goedel-to-consciousness and objective-collapse promotion do not."

orchORRetyping : ProgrammeRetyping
orchORRetyping = programmeRetyping
  orchORProgramme
  (branchCommitment ∷ crossScaleConstraintCoupling ∷ [])
  true
  false
  "Discrete constrained selection is structurally expressible, while microtubule quantum implementation remains an empirical binding."

decoherenceRetyping : ProgrammeRetyping
decoherenceRetyping = programmeRetyping
  decoherenceObjection
  []
  true
  false
  "Decoherence bears directly only on a proposed coherent physical implementation, not on the quotient, MDL, or ternary structure itself."

cnetRetyping : ProgrammeRetyping
cnetRetyping = programmeRetyping
  cnetProgramme
  (branchCommitment ∷ crossScaleConstraintCoupling ∷ [])
  true
  false
  "A tunnelling proposal may instantiate a routing layer, but it is neither required by nor promoted to the cognitive formalism."
