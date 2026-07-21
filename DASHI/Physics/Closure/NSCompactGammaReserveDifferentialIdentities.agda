module DASHI.Physics.Closure.NSCompactGammaReserveDifferentialIdentities where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion

------------------------------------------------------------------------
-- Γ-floor reserve differential identity (GF1--GF9).
--
-- This layer deliberately records the analytic inputs at their natural seams:
-- numerator chain rule, differentiated-triad specialization, near/far bounds,
-- quotient and logarithmic chain rules, and the concrete coercive-envelope
-- identification.  The public Navier--Stokes balance is then a theorem, not an
-- additional opaque field.
------------------------------------------------------------------------

record GammaFloorDifferentialData
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    gammaFloorReserve gammaDerivative : Time → Scalar A

    packetEnergy packetEnergyDerivative : Time → Scalar A
    packetNumerator packetNumeratorDerivative : Time → Scalar A
    differentiatedNumerator : Time → Scalar A

    nearNumerator farNumerator : Time → Scalar A
    nearNumeratorBudget farNumeratorBudget : Time → Scalar A
    tangentNorm tailDecay : Time → Scalar A

    gammaLogDerivative functionalGammaDerivative : Time → Scalar A
    gammaCoerciveEnvelope gammaDissipationRate gammaForcingRate :
      Time → Scalar A

    packetEnergyPositive : Time → Set
    gammaPositive : Time → Set
    timeDerivativeAdmissibleTangent : Time → Set

    -- GF1: chain rule for N_K(u(t)).
    packetNumeratorChainRule : ∀ τ →
      packetNumeratorDerivative τ ≡ differentiatedNumerator τ

    -- GF2: h = ∂_t u is a valid differentiated-triad tangent and its exact
    -- decomposition is the near/far split consumed below.
    differentiatedTriadAtTimeDerivative : ∀ τ →
      timeDerivativeAdmissibleTangent τ →
      differentiatedNumerator τ ≡
      _+_ A (nearNumerator τ) (farNumerator τ)

    -- GF3: concrete full-shell Schur estimate with its instantiated budget.
    nearShellNumeratorBound : ∀ τ →
      _≤_ A (nearNumerator τ) (nearNumeratorBudget τ)

    -- GF4: instantiated far-tail estimate
    -- |DN_far| ≤ ε(R) E_K ||∂_t u||_{X_K}; the product is represented by the
    -- selected concrete budget so this module remains carrier-parametric.
    farTailBudgetMeaning : ∀ τ →
      farNumeratorBudget τ ≡ tailDecay τ
    farTailNumeratorBound : ∀ τ →
      _≤_ A (farNumerator τ) (farNumeratorBudget τ)

    -- GF5: exact quotient rule for Γ_K = N_K / E_K.
    gammaQuotientDerivative : ∀ τ →
      packetEnergyPositive τ →
      gammaDerivative τ ≡ functionalGammaDerivative τ

    -- GF6: d(log Γ_K)/dt = Γ̇_K / Γ_K.
    logarithmicGammaDerivative : ∀ τ →
      gammaPositive τ →
      gammaLogDerivative τ ≡ gammaDerivative τ

    -- GF7: chain rule for -α_Γ log(Γ_K/γ_*).  Its selected scalar expression
    -- is the functional derivative used in the balance.
    gammaFloorBarrierChainRule : ∀ τ →
      gammaPositive τ →
      gammaFloorReserve τ ≡ gammaLogDerivative τ

    -- GF8: C_Γ is specifically the envelope which dominates the later
    -- Bernstein-weighted shell sum; it is not an arbitrary named rate.
    weightedBernsteinShellRate : Time → Scalar A
    gammaEnvelopeDominatesBernstein : ∀ τ →
      _≤_ A (weightedBernsteinShellRate τ) (gammaCoerciveEnvelope τ)

    concreteNearTailGammaBalance : ∀ τ →
      _+_ A (functionalGammaDerivative τ) (gammaCoerciveEnvelope τ) ≡
      _+_ A (gammaDissipationRate τ) (gammaForcingRate τ)

open GammaFloorDifferentialData public

-- GF9: the Γ reserve Navier--Stokes balance obtained from GF5 and GF8.
gammaFunctionalNavierStokesBalance :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (G : GammaFloorDifferentialData A Time) → ∀ τ →
  packetEnergyPositive G τ →
  _+_ A (gammaDerivative G τ) (gammaCoerciveEnvelope G τ) ≡
  _+_ A (gammaDissipationRate G τ) (gammaForcingRate G τ)
gammaFunctionalNavierStokesBalance {A = A} G τ energy>0 =
  subst
    (λ derivative →
      _+_ A derivative (gammaCoerciveEnvelope G τ) ≡
      _+_ A (gammaDissipationRate G τ) (gammaForcingRate G τ))
    (sym (gammaQuotientDerivative G τ energy>0))
    (concreteNearTailGammaBalance G τ)

gammaFloorDifferentialLeaf :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (G : GammaFloorDifferentialData A Time) →
  (positiveEnergy : ∀ τ → packetEnergyPositive G τ) →
  ReserveDifferentialLeaf A Time
gammaFloorDifferentialLeaf G positiveEnergy = record
  { reserve = gammaFloorReserve G
  ; reserveDerivative = gammaDerivative G
  ; functionalDerivative = functionalGammaDerivative G
  ; coerciveRate = gammaCoerciveEnvelope G
  ; dissipationRate = gammaDissipationRate G
  ; forcingRate = gammaForcingRate G
  ; reserveChainRule = gammaQuotientDerivative G _ (positiveEnergy _)
  ; functionalNavierStokesBalance = concreteNearTailGammaBalance G
  }

gamma-floor-reserve-differential-identity-concrete :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (G : GammaFloorDifferentialData A Time) →
  (positiveEnergy : ∀ τ → packetEnergyPositive G τ) → ∀ τ →
  _+_ A (gammaDerivative G τ) (gammaCoerciveEnvelope G τ) ≡
  _+_ A (gammaDissipationRate G τ) (gammaForcingRate G τ)
gamma-floor-reserve-differential-identity-concrete G positiveEnergy =
  reserve-differential-identity
    (gammaFloorDifferentialLeaf G positiveEnergy)

------------------------------------------------------------------------
-- Off-packet reserve differential identity (OP1--OP7).
------------------------------------------------------------------------

record OffPacketDifferentialData
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    offPacketReserve offPacketReserveDerivative : Time → Scalar A
    packetEnergyForRatio packetEnergyDerivativeForRatio : Time → Scalar A

    -- OP1: exact finite/cutoff shell sum defining E_off,K,R.
    offPacketEnergy : Time → Scalar A
    exactOffPacketShellEnergy : Time → Scalar A
    offPacketEnergyIsExactShellSum : ∀ τ →
      offPacketEnergy τ ≡ exactOffPacketShellEnergy τ

    offPacketEnergyDerivative offPacketDissipation shellTransferSum :
      Time → Scalar A

    viscosity νDoff nonlinearOffPacketTransfer : Time → Scalar A

    -- OP2: exact differentiated shell sum.
    offPacketEnergyNavierStokesDerivative : ∀ τ →
      offPacketEnergyDerivative τ ≡
      _+_ A (νDoff τ) (nonlinearOffPacketTransfer τ)

    -- OP3: all transfer incidences internal to the off region cancel; only
    -- boundary-crossing incidences remain.
    boundaryFlux : Time → Scalar A
    internalTransferCancellation : ∀ τ →
      shellTransferSum τ ≡ boundaryFlux τ
    nonlinearTransferIsShellTransferSum : ∀ τ →
      nonlinearOffPacketTransfer τ ≡ shellTransferSum τ

    packetEnergyForRatioPositive : Time → Set

    -- OP4: quotient rule for R_K,R = E_off,K,R / E_K.
    offPacketQuotientDerivative : ∀ τ →
      packetEnergyForRatioPositive τ →
      offPacketReserveDerivative τ ≡ offPacketEnergyDerivative τ

    -- OP5: both supported barriers.  The selected derivative below may be the
    -- linear α_R Ṙ or logarithmic α_R Ṙ/(η_*-R).
    linearOffPacketBarrierDerivative logarithmicOffPacketBarrierDerivative :
      Time → Scalar A
    linearOffPacketBarrierChainRule : ∀ τ →
      linearOffPacketBarrierDerivative τ ≡ offPacketReserveDerivative τ
    logarithmicOffPacketBarrierChainRule : ∀ τ →
      logarithmicOffPacketBarrierDerivative τ ≡ offPacketReserveDerivative τ

    selectedOffPacketFunctionalDerivative : Time → Scalar A
    selectedBarrierChainRule : ∀ τ →
      offPacketReserveDerivative τ ≡ selectedOffPacketFunctionalDerivative τ

    -- OP6: the inward estimate is assembled from the named analytic sources.
    remoteViscousDamping nearShellSchurControl farTailGeometricControl :
      Time → Scalar A
    denominatorLowerBound : Time → Scalar A
    offPacketCoerciveEnvelope offPacketDissipationRate offPacketForcingRate :
      Time → Scalar A

    offPacketCoerciveNonnegative : ∀ τ →
      _≤_ A (zero A) (offPacketCoerciveEnvelope τ)

    inwardFluxEstimate : ∀ τ →
      _+_ A
        (selectedOffPacketFunctionalDerivative τ)
        (offPacketCoerciveEnvelope τ)
      ≡
      _+_ A (offPacketDissipationRate τ) (offPacketForcingRate τ)

open OffPacketDifferentialData public

offPacketBoundaryFluxIdentity :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (O : OffPacketDifferentialData A Time) → ∀ τ →
  nonlinearOffPacketTransfer O τ ≡ boundaryFlux O τ
offPacketBoundaryFluxIdentity O τ =
  subst
    (λ transfer → nonlinearOffPacketTransfer O τ ≡ transfer)
    (internalTransferCancellation O τ)
    (nonlinearTransferIsShellTransferSum O τ)

offPacketFunctionalNavierStokesBalance :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (O : OffPacketDifferentialData A Time) → ∀ τ →
  packetEnergyForRatioPositive O τ →
  _+_ A
    (offPacketReserveDerivative O τ)
    (offPacketCoerciveEnvelope O τ)
  ≡
  _+_ A (offPacketDissipationRate O τ) (offPacketForcingRate O τ)
offPacketFunctionalNavierStokesBalance {A = A} O τ energy>0 =
  subst
    (λ derivative →
      _+_ A derivative (offPacketCoerciveEnvelope O τ) ≡
      _+_ A (offPacketDissipationRate O τ) (offPacketForcingRate O τ))
    (sym (selectedBarrierChainRule O τ))
    (inwardFluxEstimate O τ)

offPacketDifferentialLeaf :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (O : OffPacketDifferentialData A Time) →
  ReserveDifferentialLeaf A Time
offPacketDifferentialLeaf O = record
  { reserve = offPacketReserve O
  ; reserveDerivative = offPacketReserveDerivative O
  ; functionalDerivative = selectedOffPacketFunctionalDerivative O
  ; coerciveRate = offPacketCoerciveEnvelope O
  ; dissipationRate = offPacketDissipationRate O
  ; forcingRate = offPacketForcingRate O
  ; reserveChainRule = selectedBarrierChainRule O
  ; functionalNavierStokesBalance = inwardFluxEstimate O
  }

-- OP7: exact off-packet reserve identity by chain-rule substitution.
off-packet-reserve-differential-identity-concrete :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (O : OffPacketDifferentialData A Time) → ∀ τ →
  _+_ A
    (offPacketReserveDerivative O τ)
    (offPacketCoerciveEnvelope O τ)
  ≡
  _+_ A (offPacketDissipationRate O τ) (offPacketForcingRate O τ)
off-packet-reserve-differential-identity-concrete O =
  reserve-differential-identity (offPacketDifferentialLeaf O)
