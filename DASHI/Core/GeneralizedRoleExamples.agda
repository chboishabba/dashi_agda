module DASHI.Core.GeneralizedRoleExamples where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens

-- Minimal concrete carriers show that the role grammar is generated from the
-- domain parameter rather than hand-authored as QiOperator, DonkeyOperator, …
data DonkeyState : Set where
  resting working recovering : DonkeyState

data DonkeyAction : Set where
  feed rest move groom : DonkeyAction

data DonkeyObservation : Set where
  gait hydration load stress : DonkeyObservation

data QiState : Set where
  openFlow blockedFlow balancedFlow : QiState

data QiAction : Set where
  redirect soften openThreshold : QiAction

data QiObservation : Set where
  circulation pressure boundary : QiObservation

data EvidenceToken : Set where
  observed modelled historical : EvidenceToken

DonkeyRole : FormalRole → Set
DonkeyRole carrierSpaceRole    = DonkeyState
DonkeyRole stateRole           = DonkeyState
DonkeyRole operatorRole        = DonkeyAction
DonkeyRole observableRole      = DonkeyObservation
DonkeyRole spectrumToolRole    = DonkeyObservation → Nat
DonkeyRole boundaryGateRole    = DonkeyState → Bool
DonkeyRole obstructionRole     = DonkeyObservation
DonkeyRole algebraRole         = DonkeyAction → DonkeyAction → DonkeyAction
DonkeyRole proofObligationRole = Set
DonkeyRole decompositionRole   = DonkeyState → List DonkeyObservation
DonkeyRole hamiltonianRole     = DonkeyState → Nat
DonkeyRole metricRole          = DonkeyState → DonkeyState → Nat
DonkeyRole projectionRole      = DonkeyState → DonkeyObservation
DonkeyRole residualRole        = List DonkeyObservation
DonkeyRole receiptRole         = EvidenceToken
DonkeyRole functorRole         = DonkeyAction → DonkeyAction
DonkeyRole transitionRole      = DonkeyState → DonkeyAction → DonkeyState
DonkeyRole invariantRole       = DonkeyState → Set
DonkeyRole symmetryRole        = DonkeyState → DonkeyState
DonkeyRole modeRole            = DonkeyState
DonkeyRole sourceRole          = DonkeyState
DonkeyRole sinkRole            = DonkeyState
DonkeyRole flowRole            = DonkeyState → DonkeyState
DonkeyRole constraintRole      = DonkeyState → Set
DonkeyRole remedyRole          = DonkeyAction

QiRole : FormalRole → Set
QiRole carrierSpaceRole    = QiState
QiRole stateRole           = QiState
QiRole operatorRole        = QiAction
QiRole observableRole      = QiObservation
QiRole spectrumToolRole    = QiObservation → Nat
QiRole boundaryGateRole    = QiState → Bool
QiRole obstructionRole     = QiObservation
QiRole algebraRole         = QiAction → QiAction → QiAction
QiRole proofObligationRole = Set
QiRole decompositionRole   = QiState → List QiObservation
QiRole hamiltonianRole     = QiState → Nat
QiRole metricRole          = QiState → QiState → Nat
QiRole projectionRole      = QiState → QiObservation
QiRole residualRole        = List QiObservation
QiRole receiptRole         = EvidenceToken
QiRole functorRole         = QiAction → QiAction
QiRole transitionRole      = QiState → QiAction → QiState
QiRole invariantRole       = QiState → Set
QiRole symmetryRole        = QiState → QiState
QiRole modeRole            = QiState
QiRole sourceRole          = QiState
QiRole sinkRole            = QiState
QiRole flowRole            = QiState → QiState
QiRole constraintRole      = QiState → Set
QiRole remedyRole          = QiAction

donkeyDomain : RoleFamily
donkeyDomain = record { Carrier = DonkeyState ; RoleType = DonkeyRole }

qiDomain : RoleFamily
qiDomain = record { Carrier = QiState ; RoleType = QiRole }

DonkeyOperator : Set
DonkeyOperator = RoleType donkeyDomain operatorRole

QiOperator : Set
QiOperator = RoleType qiDomain operatorRole

DonkeyObservable : Set
DonkeyObservable = RoleType donkeyDomain observableRole

QiObservable : Set
QiObservable = RoleType qiDomain observableRole

donkeyFeedTerm : TypedTerm EvidenceToken
donkeyFeedTerm =
  record
    { domain   = donkeyDomain
    ; role     = operatorRole
    ; evidence = observed
    ; payload  = feed
    }

qiBoundaryTerm : TypedTerm EvidenceToken
qiBoundaryTerm =
  record
    { domain   = qiDomain
    ; role     = boundaryGateRole
    ; evidence = modelled
    ; payload  = λ where
        openFlow     → true
        blockedFlow  → false
        balancedFlow → true
    }

-- The proof-lens layer is independently indexed from the role layer.
TrivialLensWitness :
  (D : RoleFamily) → ProofLens → (r : FormalRole) → RoleType D r → Set
TrivialLensWitness D lens r payload = ⊤

trivialLenses : (D : RoleFamily) → LensFamily D
trivialLenses D = record { LensWitness = TrivialLensWitness D }

donkeyWaveReceipt : RoleLensReceipt EvidenceToken
donkeyWaveReceipt =
  record
    { receiptDomain     = donkeyDomain
    ; receiptLenses     = trivialLenses donkeyDomain
    ; receiptRole       = operatorRole
    ; receiptPayload    = feed
    ; receiptLens       = waveLens
    ; receiptWitness    = tt
    ; receiptEvidence   = observed
    ; Residual           = Nat
    ; receiptResidual   = 0
    ; Admissible         = ⊤
    ; receiptAdmissible = tt
    }

donkeySpectralReceipt : RoleLensReceipt EvidenceToken
donkeySpectralReceipt =
  record
    { receiptDomain     = donkeyDomain
    ; receiptLenses     = trivialLenses donkeyDomain
    ; receiptRole       = observableRole
    ; receiptPayload    = gait
    ; receiptLens       = spectralLens
    ; receiptWitness    = tt
    ; receiptEvidence   = modelled
    ; Residual           = Nat
    ; receiptResidual   = 0
    ; Admissible         = ⊤
    ; receiptAdmissible = tt
    }
