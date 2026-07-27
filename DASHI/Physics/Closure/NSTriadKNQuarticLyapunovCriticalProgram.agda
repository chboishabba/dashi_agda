module DASHI.Physics.Closure.NSTriadKNQuarticLyapunovCriticalProgram where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Nat.Base using (_≤_)

open import DASHI.Physics.Closure.NSTriadKNQuarticLyapunovDegreeAudit public
open import DASHI.Physics.Closure.NSTriadKNQuarticLyapunovEulerInvariantDecomposition public
open import DASHI.Physics.Closure.NSTriadKNAdaptiveQuarticCoherenceCharts public
open import DASHI.Physics.Closure.NSTriadKNPeriodicStokesModeDegeneracy public

------------------------------------------------------------------------
-- Fail-closed research socket for the periodic 3-D problem.
--
-- The paper's transferable content is now exact:
--   * square only an Euler-invariant quadratic energy;
--   * retain quadratic/cubic/quartic derivative pieces;
--   * let quadratic and quartic reserves jointly dominate the cubic part;
--   * use equivariant adaptive coherence charts, not one fixed shear mode.
--
-- The remaining field is the actual cutoff-uniform PDE inequality.
------------------------------------------------------------------------

record PeriodicCriticalQuarticCandidate {c s : Level} :
    Set (lsuc (c ⊔ s)) where
  field
    Cutoff : Set c
    State : Set s

    lyapunovValue referenceEnergy : Cutoff → State → Nat
    quadraticReserve cubicMagnitude quarticReserve :
      Cutoff → State → Nat

    lowerEquivalenceConstant upperEquivalenceConstant : Nat
    lowerEquivalent : ∀ cutoff state →
      lowerEquivalenceConstant * referenceEnergy cutoff state
      ≤ lyapunovValue cutoff state
    upperEquivalent : ∀ cutoff state →
      lyapunovValue cutoff state
      ≤ upperEquivalenceConstant * referenceEnergy cutoff state

    exactEulerInvariantDegreeDecomposition : Set
    exactSignedNearFarIdentification : Set
    chartSelectionEquivariant : Set
    zeroConcentratedTransitionDiffuseCoverage : Set
    switchingDoesNotIncreaseLyapunovValue : Set
    positiveChartDwellTime : Set

    cutoffUniformJointDomination : ∀ cutoff state →
      cubicMagnitude cutoff state
      ≤ quadraticReserve cutoff state + quarticReserve cutoff state

    dominationStrictOnEveryNonzeroBoundaryState : Set
    boundIndependentOfCutoff : Set

open PeriodicCriticalQuarticCandidate public

record QuarticCandidateControlsBKM
    {c s : Level}
    (candidate : PeriodicCriticalQuarticCandidate {c} {s}) :
    Set (lsuc (c ⊔ s)) where
  field
    weightedVorticityEnvelope : Cutoff candidate → State candidate → Nat
    finiteTimeEnvelopeExpenditure : Set
    envelopeDominatesVorticityInfinityNorm : Set
    expenditureBoundIndependentOfCutoff : Set
    finiteVorticityTimeIntegral : Set

open QuarticCandidateControlsBKM public

quarticPaperTransferAlgebraClosed : Bool
quarticPaperTransferAlgebraClosed = true

quarticPaperTransferAlgebraClosedIsTrue :
  quarticPaperTransferAlgebraClosed ≡ true
quarticPaperTransferAlgebraClosedIsTrue = refl

cutoffUniformPeriodicCriticalQuarticDominationClosed : Bool
cutoffUniformPeriodicCriticalQuarticDominationClosed = false

cutoffUniformPeriodicCriticalQuarticDominationClosedIsFalse :
  cutoffUniformPeriodicCriticalQuarticDominationClosed ≡ false
cutoffUniformPeriodicCriticalQuarticDominationClosedIsFalse = refl

periodicQuarticImpliesFiniteBKMIntegralClosed : Bool
periodicQuarticImpliesFiniteBKMIntegralClosed = false

periodicQuarticImpliesFiniteBKMIntegralClosedIsFalse :
  periodicQuarticImpliesFiniteBKMIntegralClosed ≡ false
periodicQuarticImpliesFiniteBKMIntegralClosedIsFalse = refl
