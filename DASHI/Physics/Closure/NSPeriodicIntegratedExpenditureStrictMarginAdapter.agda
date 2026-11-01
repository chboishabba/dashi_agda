module DASHI.Physics.Closure.NSPeriodicIntegratedExpenditureStrictMarginAdapter where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer as Producer
import DASHI.Physics.Closure.NSPeriodicWallIHarmonicCompletion as WallI
import DASHI.Physics.Closure.NSPeriodicStrictDissipationMargin as Margin
import DASHI.Physics.Closure.NSPeriodicIntegratedExpenditureCompletion as Expenditure
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Constructor from the named strict-margin ledger to Wall II.
--
-- The generic expenditure record previously accepted the comparison
--   officialWallIBudget <= coerciveEnvelopeRate
-- directly.  This adapter derives that comparison from an exact decomposition
-- of the official budget into near/far payments plus a nonnegative, genuinely
-- positive surviving margin.
------------------------------------------------------------------------

record PeriodicStrictMarginExpenditureInputs
    {i l : Level}
    (A : AbsorptionArithmetic)
    (L : Producer.OrderedAdditiveCompletionLaws A)
    (Index Time State : Set i) : Set (lsuc (i ⊔ l)) where
  field
    harmonicInputs : WallI.PeriodicWallIHarmonicInputs A Index Time State

    selectedIndex : Time → Index
    selectedState : Time → State

    selectedAdmissible : ∀ τ →
      WallI.CommonAdmissible harmonicInputs
        (selectedIndex τ) τ (selectedState τ)

    pointwiseExpenditure :
      Producer.PointwiseCompactGammaExpenditure A Time

    navierStokesPotentialDerivative : Time → Scalar A

    navierStokesDerivativeMeaning : ∀ τ →
      navierStokesPotentialDerivative τ ≡
      Producer.potentialDerivative pointwiseExpenditure τ

    strictMarginAt :
      Time → Margin.PeriodicStrictDissipationMarginInputs A

    officialBudgetMeaning : ∀ τ →
      WallI.officialWallIBudget harmonicInputs
        (selectedIndex τ) τ (selectedState τ)
      ≡
      _+_ A
        (_+_ A
          (Margin.nearTerm (strictMarginAt τ))
          (Margin.farLowTerm (strictMarginAt τ)))
        (Margin.farHighTerm (strictMarginAt τ))

    viscosityBudgetMeaning : ∀ τ →
      Margin.viscosityBudget (strictMarginAt τ) ≡
      Producer.coerciveEnvelopeRate pointwiseExpenditure τ

    forcingRemainder switchRemainder : Scalar A

    forcingAndSwitchRemainderMeaning :
      Producer.forcingAndDataRemainder pointwiseExpenditure ≡
      _+_ A forcingRemainder switchRemainder

    expenditureTransport :
      Producer.ConcreteExpenditureTransport {l = l}
        A L pointwiseExpenditure

open PeriodicStrictMarginExpenditureInputs public

strictMarginPaysOfficialBudget :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : Producer.OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (I : PeriodicStrictMarginExpenditureInputs
    {l = l} A L Index Time State) →
  ∀ τ →
  _≤_ A
    (WallI.officialWallIBudget (harmonicInputs I)
      (selectedIndex I τ) τ (selectedState I τ))
    (Producer.coerciveEnvelopeRate (pointwiseExpenditure I) τ)
strictMarginPaysOfficialBudget {A = A} I τ =
  subst
    (λ rhs →
      _≤_ A
        (WallI.officialWallIBudget (harmonicInputs I)
          (selectedIndex I τ) τ (selectedState I τ))
        rhs)
    (viscosityBudgetMeaning I τ)
    officialBelowViscosity
  where
  margin = strictMarginAt I τ

  componentSumBelowViscosity :
    _≤_ A
      (_+_ A
        (_+_ A
          (Margin.nearTerm margin)
          (Margin.farLowTerm margin))
        (Margin.farHighTerm margin))
      (Margin.viscosityBudget margin)
  componentSumBelowViscosity =
    Margin.periodicNonlinearBelowViscosity margin

  officialBelowViscosity :
    _≤_ A
      (WallI.officialWallIBudget (harmonicInputs I)
        (selectedIndex I τ) τ (selectedState I τ))
      (Margin.viscosityBudget margin)
  officialBelowViscosity =
    subst
      (λ lhs →
        _≤_ A lhs (Margin.viscosityBudget margin))
      (sym (officialBudgetMeaning I τ))
      componentSumBelowViscosity

strictMarginInputsToConcreteExpenditure :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : Producer.OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  PeriodicStrictMarginExpenditureInputs
    {l = l} A L Index Time State →
  Expenditure.PeriodicConcreteExpenditureInputs
    {l = l} A L Index Time State
strictMarginInputsToConcreteExpenditure I = record
  { harmonicInputs = harmonicInputs I
  ; selectedIndex = selectedIndex I
  ; selectedState = selectedState I
  ; selectedAdmissible = selectedAdmissible I
  ; pointwiseExpenditure = pointwiseExpenditure I
  ; navierStokesPotentialDerivative = navierStokesPotentialDerivative I
  ; navierStokesDerivativeMeaning = navierStokesDerivativeMeaning I
  ; wallIBudgetPaidByCoerciveEnvelope = strictMarginPaysOfficialBudget I
  ; forcingRemainder = forcingRemainder I
  ; switchRemainder = switchRemainder I
  ; forcingAndSwitchRemainderMeaning = forcingAndSwitchRemainderMeaning I
  ; expenditureTransport = expenditureTransport I
  }

strictMarginIntegratedWeightedShellEstimate :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : Producer.OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (I : PeriodicStrictMarginExpenditureInputs
    {l = l} A L Index Time State) →
  _≤_ A
    (Producer.weightedShellExpenditure (expenditureTransport I))
    (_+_ A
      (Producer.potential (pointwiseExpenditure I)
        (Producer.initialTime (pointwiseExpenditure I)))
      (Producer.forcingAndDataRemainder (pointwiseExpenditure I)))
strictMarginIntegratedWeightedShellEstimate I =
  Expenditure.periodicIntegratedWeightedShellEstimate
    (strictMarginInputsToConcreteExpenditure I)

strictMarginIntegratedVorticityEstimate :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : Producer.OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (I : PeriodicStrictMarginExpenditureInputs
    {l = l} A L Index Time State) →
  _≤_ A
    (Producer.vorticityExpenditure (expenditureTransport I))
    (_+_ A
      (Producer.potential (pointwiseExpenditure I)
        (Producer.initialTime (pointwiseExpenditure I)))
      (Producer.forcingAndDataRemainder (pointwiseExpenditure I)))
strictMarginIntegratedVorticityEstimate I =
  Expenditure.periodicIntegratedVorticityEstimate
    (strictMarginInputsToConcreteExpenditure I)

strictMarginIntegratedBKMContinuation :
  ∀ {i l} {A : AbsorptionArithmetic}
    {L : Producer.OrderedAdditiveCompletionLaws A}
    {Index Time State : Set i} →
  (I : PeriodicStrictMarginExpenditureInputs
    {l = l} A L Index Time State) →
  Producer.Continuation (expenditureTransport I)
strictMarginIntegratedBKMContinuation I =
  Expenditure.periodicIntegratedBKMContinuation
    (strictMarginInputsToConcreteExpenditure I)

------------------------------------------------------------------------
-- Status: the strict-margin-to-expenditure adapter is checked.  The analytic
-- frontier is now the concrete construction of strictMarginAt and its exact
-- officialBudgetMeaning/viscosityBudgetMeaning identities.
------------------------------------------------------------------------

strictMarginExpenditureAdapterLevel : ProofLevel
strictMarginExpenditureAdapterLevel = machineChecked
