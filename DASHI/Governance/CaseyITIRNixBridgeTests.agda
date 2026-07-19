module DASHI.Governance.CaseyITIRNixBridgeTests where

open import Agda.Primitive using (lzero)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)

open import DASHI.Governance.CaseyITIRNixBridge

------------------------------------------------------------------------
-- A closed singleton model exercises every boundary without postulates.

unitJoin : JoinSemilattice ⊤
unitJoin = record
  { _⊔_ = λ _ _ → tt
  ; ⊔-associative = λ _ _ _ → refl
  ; ⊔-commutative = λ _ _ → refl
  ; ⊔-idempotent = λ _ → refl
  }

unitCasey : CaseySubstrate {lzero}
unitCasey = record
  { State = ⊤
  ; stateJoin = unitJoin
  }

unitGovernance :
  GovernanceLayer
    {rℓ = lzero}
    {vℓ = lzero}
    {pℓ = lzero}
    unitCasey
unitGovernance = record
  { ReceiptState = ⊤
  ; receiptJoin = unitJoin
  ; ActiveView = ⊤
  ; Proposal = ⊤
  ; propose = λ _ → tt
  ; emitResolution = λ _ _ _ → tt
  ; activeView = λ _ _ → tt
  }

unitBuildBoundary :
  BuildBoundary
    {bℓ = lzero}
    {aℓ = lzero}
    unitCasey
    unitGovernance
unitBuildBoundary = record
  { BuildView = ⊤
  ; Artifact = ⊤
  ; freeze = λ _ _ _ → tt
  ; nixMaterialize = λ _ → tt
  }

unitModel :
  InstitutionalModel
    {lzero}
    {lzero}
    {lzero}
    {lzero}
    {lzero}
    {lzero}
    {lzero}
    {lzero}
    {lzero}
unitModel = record
  { O-Organization = ⊤
  ; R-Requirement = ⊤
  ; casey = unitCasey
  ; governance = unitGovernance
  ; buildBoundary = unitBuildBoundary
  ; C-Code = λ _ _ _ → tt
  ; Gap = ⊤
  ; _≤F_ = λ _ _ → ⊤
  ; F-Gap = λ _ _ → tt
  }

unitCycle : GovernanceCycle unitModel
unitCycle = record
  { organization = tt
  ; requirement = tt
  ; stateBefore = tt
  ; receiptsBefore = tt
  ; proposal = tt
  ; proposalIsComputed = refl
  ; receiptsAfter = tt
  ; receiptsAreEmitted = refl
  ; gapDoesNotIncrease = tt
  }

unitObserver :
  ObserverBoundary
    {refℓ = lzero}
    unitCasey
    unitGovernance
unitObserver = record
  { ImmutableReference = ⊤
  ; stateReference = λ _ → tt
  ; receiptReference = λ _ → tt
  ; activeViewReference = λ _ → tt
  }

unitBuildDeterministic :
  nixMaterialize unitBuildBoundary tt ≡
  nixMaterialize unitBuildBoundary tt
unitBuildDeterministic = refl
