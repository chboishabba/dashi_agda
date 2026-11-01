module DASHI.Physics.Closure.NSCompactGammaConcretePotentialCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer
open import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation

------------------------------------------------------------------------
-- End-to-end adapter from the named packet/Gamma/ratio potential to the
-- existing pointwise-to-integrated-to-BKM theorem chain.
------------------------------------------------------------------------

record ConcretePotentialClosureData
    {t l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P) : Set (lsuc (t ⊔ l)) where
  field
    energyBudget : NavierStokesEnergyDissipationBudget A P I

    weightedShellExpenditure : Scalar A
    vorticityExpenditure : Scalar A

    weightedShellBelowEnvelope :
      _≤_ A weightedShellExpenditure (coerciveEnvelopeIntegral I)

    vorticityBelowWeightedShell :
      _≤_ A vorticityExpenditure weightedShellExpenditure

    Continuation : Set l

    invokeBKMAtEndpoint :
      _≤_ A vorticityExpenditure
        (_+_ A
          (totalPotential P (initialTime P))
          (forcingAndDataRemainder I)) →
      Continuation

open ConcretePotentialClosureData public

asConcreteExpenditureTransport :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P) →
  ConcretePotentialClosureData {l = l} A L C P I →
  ConcreteExpenditureTransport {l = l} A L
    (asPointwiseCompactGammaExpenditure C P I)
asConcreteExpenditureTransport L C P I D = record
  { potentialNonnegativity = concretePotentialNonnegativity L C P I
  ; energyDissipationBudget = halfInitialEnergy (energyBudget D)
  ; dissipationIntegralBelowEnergyBudget =
      concrete-dissipation-below-initial-energy (energyBudget D)
  ; weightedShellExpenditure = weightedShellExpenditure D
  ; vorticityExpenditure = vorticityExpenditure D
  ; weightedShellBelowCoerciveEnvelope = weightedShellBelowEnvelope D
  ; vorticityBelowWeightedShell = vorticityBelowWeightedShell D
  ; Continuation = Continuation D
  ; invokeBKMFromVorticityBound = invokeBKMAtEndpoint D
  }

concrete-potential-finite-envelope-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  _≤_ A
    (coerciveEnvelopeIntegral I)
    (_+_ A
      (totalPotential P (initialTime P))
      (forcingAndDataRemainder I))
concrete-potential-finite-envelope-expenditure L C P I D =
  pointwise-compactGamma-finite-envelope-expenditure
    L
    (asPointwiseCompactGammaExpenditure C P I)
    (asConcreteExpenditureTransport L C P I D)

concrete-potential-finite-weighted-shell-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  _≤_ A
    (weightedShellExpenditure D)
    (_+_ A
      (totalPotential P (initialTime P))
      (forcingAndDataRemainder I))
concrete-potential-finite-weighted-shell-expenditure L C P I D =
  pointwise-compactGamma-finite-weighted-shell-expenditure
    L
    (asPointwiseCompactGammaExpenditure C P I)
    (asConcreteExpenditureTransport L C P I D)

concrete-potential-finite-vorticity-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  _≤_ A
    (vorticityExpenditure D)
    (_+_ A
      (totalPotential P (initialTime P))
      (forcingAndDataRemainder I))
concrete-potential-finite-vorticity-expenditure L C P I D =
  pointwise-compactGamma-finite-vorticity-expenditure
    L
    (asPointwiseCompactGammaExpenditure C P I)
    (asConcreteExpenditureTransport L C P I D)

concrete-potential-bkm-continuation :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P)
    (D : ConcretePotentialClosureData {l = l} A L C P I) →
  Continuation D
concrete-potential-bkm-continuation L C P I D =
  pointwise-compactGamma-bkm-continuation
    L
    (asPointwiseCompactGammaExpenditure C P I)
    (asConcreteExpenditureTransport L C P I D)
