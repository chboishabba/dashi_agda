module DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer

------------------------------------------------------------------------
-- Concrete potential-level instantiation of the highest-alpha producer.
--
-- The potential is no longer a free function.  It is the sum of three named
-- compact-Gamma reserve components:
--
--   packet-energy reserve + Gamma-floor reserve + off-packet reserve.
--
-- Likewise its derivative, coercive envelope, dissipative payment, and forcing
-- remainder are assembled componentwise.  The only analytic leaves are the
-- three component differential identities and the selected real-valued
-- fundamental-theorem/integration instance.
------------------------------------------------------------------------

record ThreeWayAdditiveCalculus
    (A : AbsorptionArithmetic) : Set₁ where
  field
    combineThreeBalances :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
      _+_ A a₁ b₁ ≡ _+_ A c₁ d₁ →
      _+_ A a₂ b₂ ≡ _+_ A c₂ d₂ →
      _+_ A a₃ b₃ ≡ _+_ A c₃ d₃ →
      _+_ A
        (_+_ A (_+_ A a₁ a₂) a₃)
        (_+_ A (_+_ A b₁ b₂) b₃)
      ≡
      _+_ A
        (_+_ A (_+_ A c₁ c₂) c₃)
        (_+_ A (_+_ A d₁ d₂) d₃)

open ThreeWayAdditiveCalculus public

record ConcreteCompactGammaPotential
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time

    packetReserve gammaFloorReserve offPacketReserve : Time → Scalar A

    packetReserveDerivative : Time → Scalar A
    gammaFloorReserveDerivative : Time → Scalar A
    offPacketReserveDerivative : Time → Scalar A

    packetCoerciveRate gammaCoerciveRate ratioCoerciveRate : Time → Scalar A
    packetDissipationRate gammaDissipationRate ratioDissipationRate : Time → Scalar A
    packetForcingRate gammaForcingRate ratioForcingRate : Time → Scalar A

    packetDifferentialIdentity : ∀ τ →
      _+_ A (packetReserveDerivative τ) (packetCoerciveRate τ) ≡
      _+_ A (packetDissipationRate τ) (packetForcingRate τ)

    gammaDifferentialIdentity : ∀ τ →
      _+_ A (gammaFloorReserveDerivative τ) (gammaCoerciveRate τ) ≡
      _+_ A (gammaDissipationRate τ) (gammaForcingRate τ)

    ratioDifferentialIdentity : ∀ τ →
      _+_ A (offPacketReserveDerivative τ) (ratioCoerciveRate τ) ≡
      _+_ A (ratioDissipationRate τ) (ratioForcingRate τ)

    packetFinalNonnegative :
      _≤_ A (zero A) (packetReserve finalTime)
    gammaFinalNonnegative :
      _≤_ A (zero A) (gammaFloorReserve finalTime)
    ratioFinalNonnegative :
      _≤_ A (zero A) (offPacketReserve finalTime)

open ConcreteCompactGammaPotential public

totalPotential :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteCompactGammaPotential A Time → Time → Scalar A
totalPotential {A = A} P τ =
  _+_ A
    (_+_ A (packetReserve P τ) (gammaFloorReserve P τ))
    (offPacketReserve P τ)

totalPotentialDerivative :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteCompactGammaPotential A Time → Time → Scalar A
totalPotentialDerivative {A = A} P τ =
  _+_ A
    (_+_ A
      (packetReserveDerivative P τ)
      (gammaFloorReserveDerivative P τ))
    (offPacketReserveDerivative P τ)

totalCoerciveRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteCompactGammaPotential A Time → Time → Scalar A
totalCoerciveRate {A = A} P τ =
  _+_ A
    (_+_ A (packetCoerciveRate P τ) (gammaCoerciveRate P τ))
    (ratioCoerciveRate P τ)

totalDissipationRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteCompactGammaPotential A Time → Time → Scalar A
totalDissipationRate {A = A} P τ =
  _+_ A
    (_+_ A
      (packetDissipationRate P τ)
      (gammaDissipationRate P τ))
    (ratioDissipationRate P τ)

totalForcingRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteCompactGammaPotential A Time → Time → Scalar A
totalForcingRate {A = A} P τ =
  _+_ A
    (_+_ A (packetForcingRate P τ) (gammaForcingRate P τ))
    (ratioForcingRate P τ)

concrete-total-pointwise-balance :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time) →
  ∀ τ →
  _+_ A (totalPotentialDerivative P τ) (totalCoerciveRate P τ) ≡
  _+_ A (totalDissipationRate P τ) (totalForcingRate P τ)
concrete-total-pointwise-balance C P τ =
  combineThreeBalances C
    (packetDifferentialIdentity P τ)
    (gammaDifferentialIdentity P τ)
    (ratioDifferentialIdentity P τ)

------------------------------------------------------------------------
-- Selected integration realization.  This is the exact standard-analysis
-- socket: fundamental theorem plus linearity for the five concrete rates.
------------------------------------------------------------------------

record ConcreteCompactGammaIntegration
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time) : Set (lsuc t) where
  field
    coerciveEnvelopeIntegral : Scalar A
    dissipationIntegral : Scalar A
    forcingIntegral : Scalar A
    dataRemainder : Scalar A

    forcingAndDataRemainder : Scalar A
    forcingAndDataMeaning :
      forcingAndDataRemainder ≡ _+_ A forcingIntegral dataRemainder

    fundamentalTheoremAndLinearity :
      (∀ τ →
        _+_ A (totalPotentialDerivative P τ) (totalCoerciveRate P τ) ≡
        _+_ A (totalDissipationRate P τ) (totalForcingRate P τ)) →
      _+_ A
        (totalPotential P (initialTime P))
        (_+_ A dissipationIntegral forcingAndDataRemainder)
      ≡
      _+_ A
        (totalPotential P (finalTime P))
        (_+_ A coerciveEnvelopeIntegral dissipationIntegral)

open ConcreteCompactGammaIntegration public

asPointwiseCompactGammaExpenditure :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time) →
  ConcreteCompactGammaIntegration A P →
  PointwiseCompactGammaExpenditure A Time
asPointwiseCompactGammaExpenditure {A = A} C P I = record
  { initialTime = initialTime P
  ; finalTime = finalTime P
  ; potential = totalPotential P
  ; potentialDerivative = totalPotentialDerivative P
  ; coerciveEnvelopeRate = totalCoerciveRate P
  ; dissipationRate = totalDissipationRate P
  ; forcingRate = totalForcingRate P
  ; coerciveEnvelopeIntegral = coerciveEnvelopeIntegral I
  ; dissipationIntegral = dissipationIntegral I
  ; forcingTimeIntegral = forcingIntegral I
  ; dataRemainder = dataRemainder I
  ; forcingAndDataRemainder = forcingAndDataRemainder I
  ; forcingAndDataMeaning = forcingAndDataMeaning I
  ; pointwisePotentialBalance = concrete-total-pointwise-balance C P
  ; integratePointwiseBalance = fundamentalTheoremAndLinearity I
  }

concretePotentialNonnegativity :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveCompletionLaws A)
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P) →
  CompactGammaPotentialNonnegativity A L
    (asPointwiseCompactGammaExpenditure C P I)
concretePotentialNonnegativity L C P I = record
  { packetPotentialFinal = packetReserve P (finalTime P)
  ; gammaPotentialFinal = gammaFloorReserve P (finalTime P)
  ; ratioPotentialFinal = offPacketReserve P (finalTime P)
  ; packetPotentialFinalNonnegative = packetFinalNonnegative P
  ; gammaPotentialFinalNonnegative = gammaFinalNonnegative P
  ; ratioPotentialFinalNonnegative = ratioFinalNonnegative P
  ; finalPotentialDecomposition = refl
  }

------------------------------------------------------------------------
-- Navier-Stokes energy audit.  The selected dissipation integral is tied to the
-- viscosity-weighted gradient expenditure; it is not an unrelated scalar.
------------------------------------------------------------------------

record NavierStokesEnergyDissipationBudget
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (P : ConcreteCompactGammaPotential A Time)
    (I : ConcreteCompactGammaIntegration A P) : Set (lsuc t) where
  field
    viscosityGradientIntegral halfInitialEnergy : Scalar A
    dissipationIsViscosityGradientIntegral :
      dissipationIntegral I ≡ viscosityGradientIntegral
    energyInequality :
      _≤_ A viscosityGradientIntegral halfInitialEnergy

open NavierStokesEnergyDissipationBudget public

concrete-dissipation-below-initial-energy :
  ∀ {t} {A : AbsorptionArithmetic}
    {Time : Set t}
    {P : ConcreteCompactGammaPotential A Time}
    {I : ConcreteCompactGammaIntegration A P} →
  (E : NavierStokesEnergyDissipationBudget A P I) →
  _≤_ A (dissipationIntegral I) (halfInitialEnergy E)
concrete-dissipation-below-initial-energy {A = A} {I = I} E =
  subst
    (λ value → _≤_ A value (halfInitialEnergy E))
    (sym (dissipationIsViscosityGradientIntegral E))
    (energyInequality E)
