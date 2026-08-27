module DASHI.Physics.Closure.TSFVLocalActionCandidateAuditExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.List using (_++_)

import DASHI.Physics.Foundations.HistoryLocalActionAccumulationExact as Action
import DASHI.Physics.Foundations.TSFVFeynmanDerivationObligationsExact as Obligations
import DASHI.Physics.Closure.TSFVCandidate256CalibrationLawDiagnostic as TSFV
import DASHI.Physics.Closure.W4SurrogateScaleSettingBoundary as Surrogate

------------------------------------------------------------------------
-- Highest-alpha TSFV action-candidate audit.
--
-- Candidate256 already supplies a signed address, a bounded v3 valuation,
-- and an involutive T action under which the valuation is invariant.  This
-- file turns that local invariant into an additive finite-history functional
-- using the generic action accumulator, then states exactly why that is still
-- only a structural action candidate rather than the physical S[gamma].
------------------------------------------------------------------------

tsfvLocalActionSystem : Action.LocalActionSystem
tsfvLocalActionSystem =
  record
    { State = Surrogate.Candidate256QuotientClass
    ; localAction = λ left right →
        TSFV.v3AddressDepth
          TSFV.candidate256TritValuationFuel
          (TSFV.candidate256IntegerAddress right)
    ; actionReading =
        "Structural TSFV candidate: each finite step contributes the bounded v3 depth of the destination quotient representative; accumulation is additive by construction, not yet physical action."
    }

tsfvLocalActionTInvariant :
  (left right : Surrogate.Candidate256QuotientClass) →
  Action.localAction
    tsfvLocalActionSystem
    (TSFV.candidate256QuotientT left)
    (TSFV.candidate256QuotientT right)
  ≡
  Action.localAction tsfvLocalActionSystem left right
tsfvLocalActionTInvariant left right
  rewrite TSFV.candidate256AddressNegationCompatibility right =
  TSFV.v3AddressNegationInvariant
    TSFV.candidate256TritValuationFuel
    (TSFV.candidate256IntegerAddress right)

tsfvLocalActionSymmetry : Action.LocalActionSymmetry tsfvLocalActionSystem
tsfvLocalActionSymmetry =
  record
    { transform = TSFV.candidate256QuotientT
    ; transformInvolutive = TSFV.candidate256QuotientTInvolutive
    ; localActionInvariant = tsfvLocalActionTInvariant
    }

------------------------------------------------------------------------
-- Concrete finite trace and exact laws.
------------------------------------------------------------------------

candidateLeft : Surrogate.Candidate256QuotientClass
candidateLeft = Surrogate.candidate256LeftQuotientClass

candidateRight : Surrogate.Candidate256QuotientClass
candidateRight = Surrogate.candidate256RightQuotientClass

canonicalTSFVTrace : List (Action.Step tsfvLocalActionSystem)
canonicalTSFVTrace =
  (candidateLeft , candidateRight)
  ∷ (candidateRight , candidateLeft)
  ∷ []

canonicalTSFVStructuralAction : Nat
canonicalTSFVStructuralAction =
  Action.historyAction tsfvLocalActionSystem canonicalTSFVTrace

tsfvStructuralActionTInvariant :
  Action.historyAction
    tsfvLocalActionSystem
    (Action.transformTrace tsfvLocalActionSymmetry canonicalTSFVTrace)
  ≡
  canonicalTSFVStructuralAction
tsfvStructuralActionTInvariant =
  Action.historyActionInvariant tsfvLocalActionSymmetry canonicalTSFVTrace

canonicalTraceAdditivity :
  Action.historyAction
    tsfvLocalActionSystem
    ( ((candidateLeft , candidateRight) ∷ [])
      ++
      ((candidateRight , candidateLeft) ∷ []) )
  ≡
  Action.historyAction
    tsfvLocalActionSystem
    ((candidateLeft , candidateRight) ∷ [])
  +
  Action.historyAction
    tsfvLocalActionSystem
    ((candidateRight , candidateLeft) ∷ [])
canonicalTraceAdditivity =
  Action.historyActionAppend
    tsfvLocalActionSystem
    ((candidateLeft , candidateRight) ∷ [])
    ((candidateRight , candidateLeft) ∷ [])

------------------------------------------------------------------------
-- Candidate audit: what has actually been gained.
------------------------------------------------------------------------

data ActionCandidateProperty : Set where
  finiteLocalContributionAvailable : ActionCandidateProperty
  finiteTraceAdditivityProved : ActionCandidateProperty
  tInvarianceProved : ActionCandidateProperty
  representativeCalibrationInvariantAvailable : ActionCandidateProperty
  physicalDimensionMissing : ActionCandidateProperty
  lagrangianOrHamiltonianOriginMissing : ActionCandidateProperty
  continuumLimitMissing : ActionCandidateProperty
  empiricalActionCalibrationMissing : ActionCandidateProperty

data ActionCandidateStatus : Set where
  structuralCandidateConstructed : ActionCandidateStatus
  physicalActionDerived : ActionCandidateStatus

canonicalCandidateProperties : List ActionCandidateProperty
canonicalCandidateProperties =
  finiteLocalContributionAvailable
  ∷ finiteTraceAdditivityProved
  ∷ tInvarianceProved
  ∷ representativeCalibrationInvariantAvailable
  ∷ physicalDimensionMissing
  ∷ lagrangianOrHamiltonianOriginMissing
  ∷ continuumLimitMissing
  ∷ empiricalActionCalibrationMissing
  ∷ []

record TSFVLocalActionCandidateAudit : Set₁ where
  field
    localActionSurface : Action.LocalActionSystem
    symmetrySurface : Action.LocalActionSymmetry localActionSurface
    accumulationBoundary : Action.LocalActionAccumulationBoundary

    candidateProperties : List ActionCandidateProperty
    candidatePropertiesAreCanonical :
      candidateProperties ≡ canonicalCandidateProperties

    status : ActionCandidateStatus
    statusIsStructuralOnly : status ≡ structuralCandidateConstructed

    structuralActionIsPhysicalAction : Bool
    structuralActionIsPhysicalActionIsFalse :
      structuralActionIsPhysicalAction ≡ false

    v3DepthHasPhysicalActionUnits : Bool
    v3DepthHasPhysicalActionUnitsIsFalse :
      v3DepthHasPhysicalActionUnits ≡ false

    tInvarianceAloneDeterminesFeynmanAction : Bool
    tInvarianceAloneDeterminesFeynmanActionIsFalse :
      tInvarianceAloneDeterminesFeynmanAction ≡ false

    auditReading : String

open TSFVLocalActionCandidateAudit public

canonicalTSFVLocalActionCandidateAudit : TSFVLocalActionCandidateAudit
canonicalTSFVLocalActionCandidateAudit =
  record
    { localActionSurface = tsfvLocalActionSystem
    ; symmetrySurface = tsfvLocalActionSymmetry
    ; accumulationBoundary = Action.canonicalLocalActionAccumulationBoundary
    ; candidateProperties = canonicalCandidateProperties
    ; candidatePropertiesAreCanonical = refl
    ; status = structuralCandidateConstructed
    ; statusIsStructuralOnly = refl
    ; structuralActionIsPhysicalAction = false
    ; structuralActionIsPhysicalActionIsFalse = refl
    ; v3DepthHasPhysicalActionUnits = false
    ; v3DepthHasPhysicalActionUnitsIsFalse = refl
    ; tInvarianceAloneDeterminesFeynmanAction = false
    ; tInvarianceAloneDeterminesFeynmanActionIsFalse = refl
    ; auditReading =
        "TSFV now has a concrete additive finite-history action candidate generated from its existing bounded v3 address valuation, with exact Candidate256 T-invariance.  The audit refuses physical promotion because action units, a Lagrangian/Hamiltonian origin, continuum control, and empirical action calibration remain absent."
    }

------------------------------------------------------------------------
-- The hard-arrow ledger remains open: this construction advances the action
-- problem from a bare interface to a concrete candidate audit, but does not
-- inhabit the physical-action derivation obligation.
------------------------------------------------------------------------

tsfvPhysicalActionObligationStillOpen : Obligations.DerivationObligation
tsfvPhysicalActionObligationStillOpen = Obligations.tsfvActionObligation
