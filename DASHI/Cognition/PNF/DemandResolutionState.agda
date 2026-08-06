module DASHI.Cognition.PNF.DemandResolutionState where

open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- Candidate availability and semantic resolution are different states.
-- Runtime state code 2 is reserved for an explicit resolved target.
------------------------------------------------------------------------

data DemandStatus : Set where
  openDemand resolvedDemand deferredWorldDemand failedDemand : DemandStatus

record CandidateEvidence : Set where
  constructor candidateEvidence
  field
    candidateDemand : DemandId
    candidateTargetKind candidateTargetIdentity : Nat
    candidateRank : Nat

open CandidateEvidence public

record ResolvedTarget : Set where
  constructor resolvedTarget
  field
    resolvedKind resolvedIdentity : Nat

open ResolvedTarget public

data DemandState : DemandStatus → Set where
  openWithNoCandidates : DemandState openDemand
  openWithCandidates :
    CandidateEvidence → DemandState openDemand
  resolvedWithTarget :
    ResolvedTarget → DemandState resolvedDemand
  deferredToWorld : DemandState deferredWorldDemand
  demandFailed : DemandState failedDemand

candidateDoesNotResolve :
  CandidateEvidence → DemandState openDemand
candidateDoesNotResolve = openWithCandidates

resolveDemand : ResolvedTarget → DemandState resolvedDemand
resolveDemand = resolvedWithTarget

openCandidateCannotBeResolvedState :
  DemandState openDemand → DemandState resolvedDemand → ⊥
openCandidateCannotBeResolvedState openWithNoCandidates (resolvedWithTarget target) =
  λ ()
openCandidateCannotBeResolvedState
  (openWithCandidates candidate)
  (resolvedWithTarget target) = λ ()

record DemandStateBoundary : Set where
  constructor demandStateBoundary
  field
    candidateRowsKeepDemandOpen :
      CandidateEvidence → DemandState openDemand
    resolvedStateRequiresTarget :
      ResolvedTarget → DemandState resolvedDemand
    unresolvedWorldStateHasNoResolvedTarget :
      DemandState deferredWorldDemand

open DemandStateBoundary public

canonicalDemandStateBoundary : DemandStateBoundary
canonicalDemandStateBoundary =
  demandStateBoundary
    candidateDoesNotResolve
    resolveDemand
    deferredToWorld
