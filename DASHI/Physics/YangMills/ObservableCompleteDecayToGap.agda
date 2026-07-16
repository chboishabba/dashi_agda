module DASHI.Physics.YangMills.ObservableCompleteDecayToGap where

-- Fail-closed endpoint guard.  Decay in one scalar channel is not promoted to
-- a Hamiltonian gap; a spectrally detecting observable family is required.

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.String using (String)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; openTarget )

record ObservableCompleteDecayToGap : Set₁ where
  field
    Hilbert : Set
    Observable : Set
    Vector : Set
    Time : Set

    vacuum : Vector
    centeredState : Observable → Vector
    closureSpanCenteredStatesIsVacuumOrthogonal : Set
    physicalDecayRate : ℝ
    physicalDecayRatePositive : Set
    prefactor : Observable → ℝ
    correlation : Observable → Time → ℝ
    semigroupDecay : ∀ (A : Observable) (t : Time) → Set
    spectralGapConclusion : Set

    sourceAuthorityId : SourceAuthorityId
    theoremLocator : String
    status : VerificationStatus

observableCompleteGapAvailable : Bool
observableCompleteGapAvailable = false

currentObservableCompleteGapStatus : VerificationStatus
currentObservableCompleteGapStatus = openTarget
