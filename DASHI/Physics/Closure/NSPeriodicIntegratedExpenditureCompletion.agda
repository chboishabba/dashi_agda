module DASHI.Physics.Closure.NSPeriodicIntegratedExpenditureCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer
import DASHI.Physics.Closure.NSPeriodicWallIHarmonicCompletion as WallI
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete-PDE bridge from the official Wall I estimate to the existing exact
-- integrated compact-Gamma expenditure theorem.
--
-- The genuinely analytic work is represented by proof-relevant propositions:
-- substitution of the Galerkin Navier--Stokes vector field into the observable
-- derivatives, identification of the Wall I budget with the coercive pointwise
-- ledger, and cutoff-uniform control of the forcing and switch remainder.
------------------------------------------------------------------------

record PeriodicConcreteExpenditureInputs
    {i l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveCompletionLaws A)
    (Index Time State : Set i) : Set (lsuc (i ⊔ l)) where
  field
    harmonicInputs : WallI.PeriodicWallIHarmonicInputs A Index Time State

    selectedIndex : Time → Index
    selectedState : Time → State

    selectedAdmissible : ∀ τ →
      WallI.CommonAdmissible harmonicInputs
        (selectedIndex τ) τ (selectedState τ)

    ConcreteNavierStokesDerivativeSubstitution : Set i
    WallIBudgetMatchesDifferentialLedger : Set i
    ForcingAndSwitchRemainderUniform : Set i

    concreteNavierStokesDerivativeSubstitution :
      ConcreteNavierStokesDerivativeSubstitution

    wallIBudgetMatchesDifferentialLedger :
      WallIBudgetMatchesDifferentialLedger

    forcingAndSwitchRemainderUniform :
      ForcingAndSwitchRemainderUniform

    pointwiseExpenditure : PointwiseCompactGammaExpenditure A Time

    expenditureTransport :
      ConcreteExpenditureTransport {l = l} A L pointwiseExpenditure

open PeriodicConcreteExpenditureInputs public

concretePeriodicWallIEstimateAlongTrajectory :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (P : PeriodicConcreteExpenditureInputs {l = l} A L Index Time State) →
  ∀ τ →
  _≤_ A
    (WallI.nonlinearTotal
      (harmonicInputs P)
      (selectedIndex P τ) τ (selectedState P τ))
    (WallI.officialWallIBudget
      (harmonicInputs P)
      (selectedIndex P τ) τ (selectedState P τ))
concretePeriodicWallIEstimateAlongTrajectory P τ =
  WallI.periodicWallIHarmonicEstimate
    (harmonicInputs P)
    (selectedIndex P τ) τ (selectedState P τ)
    (selectedAdmissible P τ)

periodicIntegratedWeightedShellEstimate :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (P : PeriodicConcreteExpenditureInputs {l = l} A L Index Time State) →
  _≤_ A
    (weightedShellExpenditure (expenditureTransport P))
    (_+_ A
      (potential (pointwiseExpenditure P)
        (initialTime (pointwiseExpenditure P)))
      (forcingAndDataRemainder (pointwiseExpenditure P)))
periodicIntegratedWeightedShellEstimate {L = L} P =
  pointwise-compactGamma-finite-weighted-shell-expenditure
    L (pointwiseExpenditure P) (expenditureTransport P)

periodicIntegratedVorticityEstimate :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (P : PeriodicConcreteExpenditureInputs {l = l} A L Index Time State) →
  _≤_ A
    (vorticityExpenditure (expenditureTransport P))
    (_+_ A
      (potential (pointwiseExpenditure P)
        (initialTime (pointwiseExpenditure P)))
      (forcingAndDataRemainder (pointwiseExpenditure P)))
periodicIntegratedVorticityEstimate {L = L} P =
  pointwise-compactGamma-finite-vorticity-expenditure
    L (pointwiseExpenditure P) (expenditureTransport P)

periodicIntegratedBKMContinuation :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (P : PeriodicConcreteExpenditureInputs {l = l} A L Index Time State) →
  Continuation (expenditureTransport P)
periodicIntegratedBKMContinuation {L = L} P =
  pointwise-compactGamma-bkm-continuation
    L (pointwiseExpenditure P) (expenditureTransport P)

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

integratedExpenditureAssemblyLevel : ProofLevel
integratedExpenditureAssemblyLevel = machineChecked

concreteNavierStokesDerivativeSubstitutionLevel : ProofLevel
concreteNavierStokesDerivativeSubstitutionLevel = conditional

concreteIntegratedCompactGammaExpenditureLevel : ProofLevel
concreteIntegratedCompactGammaExpenditureLevel = conjectural

periodicConcreteExpenditureInputsInhabited : Bool
periodicConcreteExpenditureInputsInhabited = false
