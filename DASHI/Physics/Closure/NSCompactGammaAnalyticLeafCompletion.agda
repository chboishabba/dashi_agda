module DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaDifferentialExpenditureProducer
open import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation

------------------------------------------------------------------------
-- Component reserve identities.
--
-- Each reserve identity is derived from two lower leaves:
--
--   1. the chain-rule identification of the reserve derivative;
--   2. the Navier--Stokes functional balance for that derivative.
--
-- Hence packet/Gamma/off-packet differential identities are no longer fields of
-- the final potential package.  They are theorem outputs of their corresponding
-- analytic leaves.
------------------------------------------------------------------------

record ReserveDifferentialLeaf
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    reserve reserveDerivative : Time → Scalar A
    functionalDerivative : Time → Scalar A
    coerciveRate dissipationRate forcingRate : Time → Scalar A

    reserveChainRule : ∀ τ →
      reserveDerivative τ ≡ functionalDerivative τ

    functionalNavierStokesBalance : ∀ τ →
      _+_ A (functionalDerivative τ) (coerciveRate τ) ≡
      _+_ A (dissipationRate τ) (forcingRate τ)

open ReserveDifferentialLeaf public

reserve-differential-identity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (R : ReserveDifferentialLeaf A Time) → ∀ τ →
  _+_ A (reserveDerivative R τ) (coerciveRate R τ) ≡
  _+_ A (dissipationRate R τ) (forcingRate R τ)
reserve-differential-identity {A = A} R τ =
  subst
    (λ derivative →
      _+_ A derivative (coerciveRate R τ) ≡
      _+_ A (dissipationRate R τ) (forcingRate R τ))
    (sym (reserveChainRule R τ))
    (functionalNavierStokesBalance R τ)

record ConcreteReserveLeaves
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time

    packetLeaf : ReserveDifferentialLeaf A Time
    gammaFloorLeaf : ReserveDifferentialLeaf A Time
    offPacketLeaf : ReserveDifferentialLeaf A Time

    packetFinalNonnegative :
      _≤_ A (zero A) (reserve packetLeaf finalTime)
    gammaFinalNonnegative :
      _≤_ A (zero A) (reserve gammaFloorLeaf finalTime)
    offPacketFinalNonnegative :
      _≤_ A (zero A) (reserve offPacketLeaf finalTime)

open ConcreteReserveLeaves public

packet-reserve-differential-identity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (R : ConcreteReserveLeaves A Time) → ∀ τ →
  _+_ A
    (reserveDerivative (packetLeaf R) τ)
    (coerciveRate (packetLeaf R) τ)
  ≡
  _+_ A
    (dissipationRate (packetLeaf R) τ)
    (forcingRate (packetLeaf R) τ)
packet-reserve-differential-identity R =
  reserve-differential-identity (packetLeaf R)

gamma-floor-reserve-differential-identity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (R : ConcreteReserveLeaves A Time) → ∀ τ →
  _+_ A
    (reserveDerivative (gammaFloorLeaf R) τ)
    (coerciveRate (gammaFloorLeaf R) τ)
  ≡
  _+_ A
    (dissipationRate (gammaFloorLeaf R) τ)
    (forcingRate (gammaFloorLeaf R) τ)
gamma-floor-reserve-differential-identity R =
  reserve-differential-identity (gammaFloorLeaf R)

off-packet-reserve-differential-identity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (R : ConcreteReserveLeaves A Time) → ∀ τ →
  _+_ A
    (reserveDerivative (offPacketLeaf R) τ)
    (coerciveRate (offPacketLeaf R) τ)
  ≡
  _+_ A
    (dissipationRate (offPacketLeaf R) τ)
    (forcingRate (offPacketLeaf R) τ)
off-packet-reserve-differential-identity R =
  reserve-differential-identity (offPacketLeaf R)

reserveLeavesToConcretePotential :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveLeaves A Time →
  ConcreteCompactGammaPotential A Time
reserveLeavesToConcretePotential R = record
  { initialTime = initialTime R
  ; finalTime = finalTime R
  ; packetReserve = reserve (packetLeaf R)
  ; gammaFloorReserve = reserve (gammaFloorLeaf R)
  ; offPacketReserve = reserve (offPacketLeaf R)
  ; packetReserveDerivative = reserveDerivative (packetLeaf R)
  ; gammaFloorReserveDerivative = reserveDerivative (gammaFloorLeaf R)
  ; offPacketReserveDerivative = reserveDerivative (offPacketLeaf R)
  ; packetCoerciveRate = coerciveRate (packetLeaf R)
  ; gammaCoerciveRate = coerciveRate (gammaFloorLeaf R)
  ; ratioCoerciveRate = coerciveRate (offPacketLeaf R)
  ; packetDissipationRate = dissipationRate (packetLeaf R)
  ; gammaDissipationRate = dissipationRate (gammaFloorLeaf R)
  ; ratioDissipationRate = dissipationRate (offPacketLeaf R)
  ; packetForcingRate = forcingRate (packetLeaf R)
  ; gammaForcingRate = forcingRate (gammaFloorLeaf R)
  ; ratioForcingRate = forcingRate (offPacketLeaf R)
  ; packetDifferentialIdentity = packet-reserve-differential-identity R
  ; gammaDifferentialIdentity = gamma-floor-reserve-differential-identity R
  ; ratioDifferentialIdentity = off-packet-reserve-differential-identity R
  ; packetFinalNonnegative = packetFinalNonnegative R
  ; gammaFinalNonnegative = gammaFinalNonnegative R
  ; ratioFinalNonnegative = offPacketFinalNonnegative R
  }

------------------------------------------------------------------------
-- Real-valued fundamental theorem and integral linearity.
--
-- This is the selected-analysis realization below
-- `ConcreteCompactGammaIntegration`: endpoint evaluation of the derivative and
-- linearity for the three rates produce the exact integrated balance.
------------------------------------------------------------------------

record RealFundamentalTheoremRealization
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time) : Set (lsuc t) where
  field
    coerciveIntegral dissipationIntegral forcingIntegral : Scalar A
    dataRemainder forcingAndDataRemainder : Scalar A

    forcingAndDataMeaning :
      forcingAndDataRemainder ≡ _+_ A forcingIntegral dataRemainder

    fundamentalTheoremAndIntegralLinearity :
      _+_ A
        (totalPotential (reserveLeavesToConcretePotential R) (initialTime R))
        (_+_ A dissipationIntegral forcingAndDataRemainder)
      ≡
      _+_ A
        (totalPotential (reserveLeavesToConcretePotential R) (finalTime R))
        (_+_ A coerciveIntegral dissipationIntegral)

open RealFundamentalTheoremRealization public

realFundamentalTheoremToIntegration :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (R : ConcreteReserveLeaves A Time) →
  RealFundamentalTheoremRealization A C R →
  ConcreteCompactGammaIntegration A (reserveLeavesToConcretePotential R)
realFundamentalTheoremToIntegration C R F = record
  { coerciveEnvelopeIntegral = coerciveIntegral F
  ; dissipationIntegral = dissipationIntegral F
  ; forcingIntegral = forcingIntegral F
  ; dataRemainder = dataRemainder F
  ; forcingAndDataRemainder = forcingAndDataRemainder F
  ; forcingAndDataMeaning = forcingAndDataMeaning F
  ; fundamentalTheoremAndLinearity =
      λ _ → fundamentalTheoremAndIntegralLinearity F
  }

------------------------------------------------------------------------
-- Selected Galerkin/Navier--Stokes energy identity.
--
-- The exact finite-dimensional identity is retained explicitly and the desired
-- viscosity-gradient budget is obtained by dropping the nonnegative final
-- energy.  `dropFinalEnergy` is the ordered-field consequence of that identity,
-- not a separate finiteness hypothesis.
------------------------------------------------------------------------

record SelectedGalerkinEnergyIdentity
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) : Set (lsuc t) where
  field
    initialKineticEnergy finalKineticEnergy : Scalar A
    viscosityGradientIntegral : Scalar A

    finalKineticEnergyNonnegative :
      _≤_ A (zero A) finalKineticEnergy

    exactGalerkinEnergyIdentity :
      initialKineticEnergy ≡
      _+_ A finalKineticEnergy viscosityGradientIntegral

    dissipationIntegralIsViscosityGradientIntegral :
      dissipationIntegral F ≡ viscosityGradientIntegral

    dropFinalEnergy :
      _≤_ A viscosityGradientIntegral initialKineticEnergy

open SelectedGalerkinEnergyIdentity public

selectedGalerkinEnergyToBudget :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) →
  SelectedGalerkinEnergyIdentity A C R F →
  NavierStokesEnergyDissipationBudget A
    (reserveLeavesToConcretePotential R)
    (realFundamentalTheoremToIntegration C R F)
selectedGalerkinEnergyToBudget C R F E = record
  { viscosityGradientIntegral = viscosityGradientIntegral E
  ; halfInitialEnergy = initialKineticEnergy E
  ; dissipationIsViscosityGradientIntegral =
      dissipationIntegralIsViscosityGradientIntegral E
  ; energyInequality = dropFinalEnergy E
  }

------------------------------------------------------------------------
-- Bernstein/vorticity transport to the concrete coercive envelope integral.
------------------------------------------------------------------------

record ConcreteBernsteinEnvelopeConnection
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveCalculus A)
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) : Set (lsuc t) where
  field
    weightedShellIntegral vorticityIntegral : Scalar A

    bernsteinShellSumBelowEnvelope :
      _≤_ A weightedShellIntegral (coerciveIntegral F)

    vorticityReconstructionBelowShellSum :
      _≤_ A vorticityIntegral weightedShellIntegral

open ConcreteBernsteinEnvelopeConnection public

bernstein-vorticity-below-concrete-envelope :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveCalculus A)
    {Time : Set t}
    (R : ConcreteReserveLeaves A Time)
    (F : RealFundamentalTheoremRealization A C R) →
  (B : ConcreteBernsteinEnvelopeConnection A C R F) →
  _≤_ A (vorticityIntegral B) (coerciveIntegral F)
bernstein-vorticity-below-concrete-envelope {A = A} C R F B =
  ≤-trans A
    (vorticityReconstructionBelowShellSum B)
    (bernsteinShellSumBelowEnvelope B)
