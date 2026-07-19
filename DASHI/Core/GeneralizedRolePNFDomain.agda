module DASHI.Core.GeneralizedRolePNFDomain where

open import DASHI.Core.Prelude
open import DASHI.Core.FormalRole
open import DASHI.Core.ProofLens
open import DASHI.Core.IndexedRoleEvidence

-- A bounded PNF/ITIR instance.  These are source-local formal objects, not
-- verdicts about the truth of the underlying narrative.
data PNFState : Set where
  raw captured normalized compared promoted blocked : PNFState

data PNFOperation : Set where
  ingest anchor normalize extract compare gate : PNFOperation

data PNFObservable : Set where
  sourceSpan proposition provenanceLink disagreement omission : PNFObservable

data PNFEvidenceToken : Set where
  sourceLocalReceipt corroboratedReceipt reviewerReceipt : PNFEvidenceToken

data PNFResidual : Set where
  unresolvedSupport contextDrift incompatibleNarrative missingSource : PNFResidual

PNFRole : FormalRole → Set
PNFRole carrierSpaceRole    = PNFState
PNFRole stateRole           = PNFState
PNFRole operatorRole        = PNFOperation
PNFRole observableRole      = PNFObservable
PNFRole spectrumToolRole    = List PNFObservable → List PNFObservable
PNFRole boundaryGateRole    = PNFState → Bool
PNFRole obstructionRole     = PNFResidual
PNFRole algebraRole         = PNFOperation → PNFOperation → PNFOperation
PNFRole proofObligationRole = PNFObservable → Set
PNFRole decompositionRole   = PNFState → List PNFObservable
PNFRole hamiltonianRole     = PNFState → Nat
PNFRole metricRole          = PNFState → PNFState → Nat
PNFRole projectionRole      = PNFState → List PNFObservable
PNFRole residualRole        = List PNFResidual
PNFRole receiptRole         = PNFEvidenceToken
PNFRole functorRole         = PNFOperation → PNFOperation
PNFRole transitionRole      = PNFState → PNFOperation → PNFState
PNFRole invariantRole       = PNFState → Set
PNFRole symmetryRole        = PNFState → PNFState
PNFRole modeRole            = PNFState
PNFRole sourceRole          = PNFObservable
PNFRole sinkRole            = PNFObservable
PNFRole flowRole            = PNFState → PNFState
PNFRole constraintRole      = PNFState → Set
PNFRole remedyRole          = PNFOperation

pnfDomain : RoleFamily
pnfDomain = record { Carrier = PNFState ; RoleType = PNFRole }

data PNFLensWitness :
  ProofLens → (r : FormalRole) → PNFRole r → Set where
  provenanceNormalFormWitness :
    (op : PNFOperation) →
    PNFLensWitness pnfLens operatorRole op

  provenanceObservableWitness :
    (obs : PNFObservable) →
    PNFLensWitness pnfLens observableRole obs

  disagreementGraphWitness :
    (residuals : List PNFResidual) →
    PNFLensWitness graphLens residualRole residuals

pnfLenses : LensFamily pnfDomain
pnfLenses = record { LensWitness = PNFLensWitness }

PNFEvidence : EvidenceFamily pnfDomain
PNFEvidence =
  record
    { EvidenceFor = λ r payload → PNFEvidenceToken
    }

-- This first policy checks only structural admissibility.  Truth, legal
-- authority, and promotion remain separate downstream obligations.
PNFPolicy : ReceiptPolicy pnfDomain PNFEvidence
PNFPolicy =
  record
    { ResidualFor = λ r payload → List PNFResidual
    ; Gate = λ r payload evidence residuals → ⊤
    }

-- Explicit non-promotion boundary: a source-local receipt is evidence of
-- provenance, not an automatic truth or legal/moral verdict.
data PNFPromotion : Set where

pnfPromotionImpossibleHere : PNFPromotion → ⊥
pnfPromotionImpossibleHere ()
