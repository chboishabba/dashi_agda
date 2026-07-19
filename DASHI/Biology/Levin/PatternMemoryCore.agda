module DASHI.Biology.Levin.PatternMemoryCore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Primitive using (Level; _⊔_; lsuc)

------------------------------------------------------------------------
-- Candidate-only core for developmental bioelectric pattern memory.
--
-- The formal separation is:
--   present morphology / electrical carrier / decoded target / repair.
-- A decoded target is not identified definitionally with the presently
-- realised body, and no consciousness or clinical authority follows.

record PatternMemorySystem
  {ℓs ℓm ℓe ℓg ℓp : Level} :
  Set (lsuc (ℓs ⊔ ℓm ⊔ ℓe ⊔ ℓg ⊔ ℓp)) where
  field
    State        : Set ℓs
    Morphology   : Set ℓm
    Electrical   : Set ℓe
    Goal         : Set ℓg
    Perturbation : Set ℓp

    body         : State → Morphology
    voltage      : State → Electrical
    decodeGoal   : Electrical → Goal
    perturb      : Perturbation → State → State
    repairStep   : State → State
    satisfies    : Morphology → Goal → Bool

open PatternMemorySystem public

record LatentPatternWitness
  {ℓs ℓm ℓe ℓg ℓp : Level}
  (S : PatternMemorySystem {ℓs} {ℓm} {ℓe} {ℓg} {ℓp}) :
  Set (ℓs ⊔ ℓg) where
  field
    state : State S
    latentGoalIsNotYetRealised :
      satisfies S (body S state) (decodeGoal S (voltage S state)) ≡ false

open LatentPatternWitness public

record TriggeredReadoutWitness
  {ℓs ℓm ℓe ℓg ℓp : Level}
  (S : PatternMemorySystem {ℓs} {ℓm} {ℓe} {ℓg} {ℓp}) :
  Set (ℓs ⊔ ℓp) where
  field
    state        : State S
    trigger      : Perturbation S
    afterTrigger : State S
    isRepairReadout :
      afterTrigger ≡ repairStep S (perturb S trigger state)
    decodedGoalIsRealised :
      satisfies S
        (body S afterTrigger)
        (decodeGoal S (voltage S state))
      ≡ true

open TriggeredReadoutWitness public

data PatternMemoryEvidenceStatus : Set where
  definitionOnly        : PatternMemoryEvidenceStatus
  modelWitness          : PatternMemoryEvidenceStatus
  experimentalCandidate : PatternMemoryEvidenceStatus
  replicatedFinding     : PatternMemoryEvidenceStatus
  mechanisticHypothesis : PatternMemoryEvidenceStatus
  philosophicalReading  : PatternMemoryEvidenceStatus

canonicalPatternMemoryNotes : List String
canonicalPatternMemoryNotes =
  "Present morphology is not definitionally identical to decoded target morphology"
  ∷ "Voltage is a typed carrier; calling it memory requires an intervention-sensitive witness"
  ∷ "Triggered regeneration may expose a latent target that was not phenotypically visible"
  ∷ "Pattern-memory witnesses do not establish consciousness, representation in every semantic sense, or clinical authority"
  ∷ []

record PatternMemoryBoundary : Set where
  field
    candidateOnly : Bool
    candidateOnlyIsTrue : candidateOnly ≡ true

    voltagePatternIsNotAutomaticallyMemory : Bool
    voltagePatternIsNotAutomaticallyMemoryIsFalse :
      voltagePatternIsNotAutomaticallyMemory ≡ false

    attractorIsNotAutomaticallyRepresentation : Bool
    attractorIsNotAutomaticallyRepresentationIsFalse :
      attractorIsNotAutomaticallyRepresentation ≡ false

    noClinicalAuthority : Bool
    noClinicalAuthorityIsFalse : noClinicalAuthority ≡ false

open PatternMemoryBoundary public

canonicalPatternMemoryBoundary : PatternMemoryBoundary
canonicalPatternMemoryBoundary = record
  { candidateOnly = true
  ; candidateOnlyIsTrue = refl
  ; voltagePatternIsNotAutomaticallyMemory = false
  ; voltagePatternIsNotAutomaticallyMemoryIsFalse = refl
  ; attractorIsNotAutomaticallyRepresentation = false
  ; attractorIsNotAutomaticallyRepresentationIsFalse = refl
  ; noClinicalAuthority = false
  ; noClinicalAuthorityIsFalse = refl
  }
