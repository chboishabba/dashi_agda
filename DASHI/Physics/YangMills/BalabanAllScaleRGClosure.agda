module DASHI.Physics.YangMills.BalabanAllScaleRGClosure where

------------------------------------------------------------------------
-- Exact induction principle for an RG invariant domain.  The mathematical
-- frontier is isolated in the one-step preservation hypothesis; the passage
-- from one-step preservation to every finite scale is fully checked.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import DASHI.Physics.YangMills.CompactLieProofLevel

record RGInvariantDomain (State : Set) : Set₁ where
  field
    renormalize : Nat → State → State
    Admissible : Nat → State → Set
    initialState : State
    initialAdmissible : Admissible zero initialState
    oneStepPreserves : ∀ scale state →
      Admissible scale state →
      Admissible (suc scale) (renormalize scale state)

open RGInvariantDomain public

iterateRG :
  ∀ {State : Set} →
  RGInvariantDomain State → Nat → State
iterateRG domain zero = initialState domain
iterateRG domain (suc scale) =
  renormalize domain scale (iterateRG domain scale)

allScalesAdmissible :
  ∀ {State : Set} →
  (domain : RGInvariantDomain State) →
  ∀ scale → Admissible domain scale (iterateRG domain scale)
allScalesAdmissible domain zero = initialAdmissible domain
allScalesAdmissible domain (suc scale) =
  oneStepPreserves domain scale (iterateRG domain scale)
    (allScalesAdmissible domain scale)

record SummableRGErrors (ErrorBound : Set) : Set₁ where
  field
    errorAt : Nat → ErrorBound
    partialSum : Nat → ErrorBound
    totalBound : ErrorBound
    LessEqual : ErrorBound → ErrorBound → Set
    partialSumsBounded : ∀ scale → LessEqual (partialSum scale) totalBound

open SummableRGErrors public

record AllScaleRGCertificate (State ErrorBound : Set) : Set₁ where
  field
    invariantDomain : RGInvariantDomain State
    errorControl : SummableRGErrors ErrorBound
    admissibleAtEveryScale : ∀ scale →
      Admissible invariantDomain scale (iterateRG invariantDomain scale)

open AllScaleRGCertificate public

assembleAllScaleRG :
  ∀ {State ErrorBound : Set} →
  (domain : RGInvariantDomain State) →
  SummableRGErrors ErrorBound →
  AllScaleRGCertificate State ErrorBound
assembleAllScaleRG domain errors = record
  { invariantDomain = domain
  ; errorControl = errors
  ; admissibleAtEveryScale = allScalesAdmissible domain
  }

allScaleInductionLevel : ProofLevel
allScaleInductionLevel = machineChecked

allScaleOneStepPreservationLevel : ProofLevel
allScaleOneStepPreservationLevel = conjectural
