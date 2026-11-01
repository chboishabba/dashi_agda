module DASHI.Physics.QuantumVacuum.ExtractionPhysicsSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

------------------------------------------------------------------------
-- Physics-facing classification extracted from the DIA vacuum-energy
-- survey.  These constructors are mechanisms and evidential states, not
-- assertions that useful net power has been demonstrated.
------------------------------------------------------------------------

data Mechanism : Set where
  casimirRelaxation           : Mechanism
  tunableCasimirCycle         : Mechanism
  coilVacuumNoise             : Mechanism
  groundStateSuppression      : Mechanism
  nonlinearVacuumDownconversion : Mechanism
  energeticVacuumDecay        : Mechanism

data MachineClass : Set where
  transient : MachineClass
  continuous : MachineClass

data EvidenceLevel : Set where
  theoreticalProposal : EvidenceLevel
  numericalModel       : EvidenceLevel
  preliminaryExperiment : EvidenceLevel
  replicatedExperiment : EvidenceLevel
  closedEngineeringCycle : EvidenceLevel

record BoundaryModeShift : Set where
  constructor mkBoundaryModeShift
  field
    unrestrictedModeCount : Nat
    restrictedModeCount   : Nat
    measurableStress      : Bool

record ExtractionClaim : Set where
  constructor mkExtractionClaim
  field
    mechanism             : Mechanism
    machineClass          : MachineClass
    evidence              : EvidenceLevel
    observableEffect      : Bool
    couplingMechanism     : Bool
    nonEquilibriumAsymmetry : Bool
    resetAccounted        : Bool
    replicated            : Bool

-- A deliberately strict promotion predicate.  It captures the useful
-- distinction:
--
--   observed vacuum effect ≠ demonstrated useful power cycle.
--
-- The theorem below is computational, so downstream modules can reduce a
-- concrete claim rather than trusting a free-standing status flag.

promotable? : ExtractionClaim → Bool
promotable? c with ExtractionClaim.observableEffect c
... | false = false
... | true with ExtractionClaim.couplingMechanism c
...   | false = false
...   | true with ExtractionClaim.nonEquilibriumAsymmetry c
...     | false = false
...     | true with ExtractionClaim.resetAccounted c
...       | false = false
...       | true with ExtractionClaim.replicated c
...         | false = false
...         | true = true

record PromotionWitness (c : ExtractionClaim) : Set where
  constructor mkPromotionWitness
  field
    observableEffectClosed       : ExtractionClaim.observableEffect c ≡ true
    couplingMechanismClosed      : ExtractionClaim.couplingMechanism c ≡ true
    nonEquilibriumAsymmetryClosed : ExtractionClaim.nonEquilibriumAsymmetry c ≡ true
    resetAccountingClosed        : ExtractionClaim.resetAccounted c ≡ true
    replicationClosed            : ExtractionClaim.replicated c ≡ true

promotionWitnessImpliesPromotable :
  (c : ExtractionClaim) → PromotionWitness c → promotable? c ≡ true
promotionWitnessImpliesPromotable c witness
  rewrite PromotionWitness.observableEffectClosed witness
        | PromotionWitness.couplingMechanismClosed witness
        | PromotionWitness.nonEquilibriumAsymmetryClosed witness
        | PromotionWitness.resetAccountingClosed witness
        | PromotionWitness.replicationClosed witness = refl

-- The default reading of the surveyed mechanisms is explicitly unpromoted.
-- This is not a scientific verdict against future experiments; it simply
-- prevents conjectural mechanisms from entering DASHI as established power
-- sources without the five physical closures above.

surveyedMechanismClaim : Mechanism → MachineClass → EvidenceLevel → ExtractionClaim
surveyedMechanismClaim m class evidence =
  mkExtractionClaim m class evidence true true false false false

surveyedMechanismNotPromoted :
  (m : Mechanism) → (class : MachineClass) → (evidence : EvidenceLevel) →
  promotable? (surveyedMechanismClaim m class evidence) ≡ false
surveyedMechanismNotPromoted m class evidence = refl
