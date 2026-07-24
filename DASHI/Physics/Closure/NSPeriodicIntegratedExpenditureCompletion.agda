module DASHI.Physics.Closure.NSPeriodicIntegratedExpenditureCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer
import DASHI.Physics.Closure.NSPeriodicWallIHarmonicCompletion as WallI
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Concrete-PDE bridge from the official Wall I estimate to the existing exact
-- integrated compact-Gamma expenditure theorem.
--
-- Opaque marker propositions are deliberately avoided.  An inhabitant must tie
-- the selected Galerkin Navier--Stokes derivative to the actual potential
-- derivative, prove that the official Wall I budget is paid by the same
-- coercive-envelope rate used by the pointwise expenditure record, and identify
-- the integrated remainder with forcing plus chart-switch costs.
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

    pointwiseExpenditure : PointwiseCompactGammaExpenditure A Time

    navierStokesPotentialDerivative : Time → Scalar A

    navierStokesDerivativeMeaning : ∀ τ →
      navierStokesPotentialDerivative τ ≡
      potentialDerivative pointwiseExpenditure τ

    wallIBudgetPaidByCoerciveEnvelope : ∀ τ →
      _≤_ A
        (WallI.officialWallIBudget harmonicInputs
          (selectedIndex τ) τ (selectedState τ))
        (coerciveEnvelopeRate pointwiseExpenditure τ)

    forcingRemainder switchRemainder : Scalar A

    forcingAndSwitchRemainderMeaning :
      forcingAndDataRemainder pointwiseExpenditure ≡
      _+_ A forcingRemainder switchRemainder

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

concretePeriodicNonlinearPaidByEnvelope :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (P : PeriodicConcreteExpenditureInputs {l = l} A L Index Time State) →
  ∀ τ →
  _≤_ A
    (WallI.nonlinearTotal
      (harmonicInputs P)
      (selectedIndex P τ) τ (selectedState P τ))
    (coerciveEnvelopeRate (pointwiseExpenditure P) τ)
concretePeriodicNonlinearPaidByEnvelope {A = A} P τ =
  ≤-trans A
    (concretePeriodicWallIEstimateAlongTrajectory P τ)
    (wallIBudgetPaidByCoerciveEnvelope P τ)

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
