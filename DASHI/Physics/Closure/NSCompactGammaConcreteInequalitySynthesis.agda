module DASHI.Physics.Closure.NSCompactGammaConcreteInequalitySynthesis where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaInequalityExpenditureProducer
open import DASHI.Physics.Closure.NSCompactGammaExactPotentialAndPacketBalance
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion
open import DASHI.Physics.Closure.NSCompactGammaConcreteBernsteinEnvelopeDomain

------------------------------------------------------------------------
-- Highest-alpha Route-B synthesis.
--
-- The concrete Fourier estimates naturally deliver one-sided component laws
--
--   D Phi_i + C_i <= D_i + F_i.
--
-- This module assembles the packet, Gamma-floor, and off-packet laws into the
-- total compact-Gamma inequality, integrates that inequality, transports the
-- concrete Bernstein/vorticity estimates, and invokes BKM only at the endpoint.
-- Exact component identities remain admissible through equalityImpliesInequality.
------------------------------------------------------------------------

record ReserveDifferentialInequalityLeaf
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    reserve reserveDerivative functionalDerivative : Time → Scalar A
    coerciveRate dissipationRate forcingRate : Time → Scalar A

    reserveChainRule : ∀ τ →
      reserveDerivative τ ≡ functionalDerivative τ

    functionalNavierStokesInequality : ∀ τ →
      _≤_ A
        (_+_ A (functionalDerivative τ) (coerciveRate τ))
        (_+_ A (dissipationRate τ) (forcingRate τ))

open ReserveDifferentialInequalityLeaf public

reserve-differential-inequality :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  (R : ReserveDifferentialInequalityLeaf A Time) → ∀ τ →
  _≤_ A
    (_+_ A (reserveDerivative R τ) (coerciveRate R τ))
    (_+_ A (dissipationRate R τ) (forcingRate R τ))
reserve-differential-inequality {A = A} R τ =
  subst
    (λ derivative →
      _≤_ A
        (_+_ A derivative (coerciveRate R τ))
        (_+_ A (dissipationRate R τ) (forcingRate R τ)))
    (sym (reserveChainRule R τ))
    (functionalNavierStokesInequality R τ)

exactReserveLeafToInequality :
  ∀ {t} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    {Time : Set t} →
  ReserveDifferentialLeaf A Time →
  ReserveDifferentialInequalityLeaf A Time
exactReserveLeafToInequality L R = record
  { reserve = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.reserve R
  ; reserveDerivative = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.reserveDerivative R
  ; functionalDerivative = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.functionalDerivative R
  ; coerciveRate = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.coerciveRate R
  ; dissipationRate = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.dissipationRate R
  ; forcingRate = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.forcingRate R
  ; reserveChainRule = DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.reserveChainRule R
  ; functionalNavierStokesInequality = λ τ →
      equalityImpliesInequality L
        (DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion.functionalNavierStokesBalance R τ)
  }

record ThreeWayAdditiveInequalityCalculus
    (A : AbsorptionArithmetic) : Set₁ where
  field
    combineThreeInequalities :
      ∀ {a₁ a₂ a₃ b₁ b₂ b₃ c₁ c₂ c₃ d₁ d₂ d₃} →
      _≤_ A (_+_ A a₁ b₁) (_+_ A c₁ d₁) →
      _≤_ A (_+_ A a₂ b₂) (_+_ A c₂ d₂) →
      _≤_ A (_+_ A a₃ b₃) (_+_ A c₃ d₃) →
      _≤_ A
        (_+_ A
          (_+_ A (_+_ A a₁ a₂) a₃)
          (_+_ A (_+_ A b₁ b₂) b₃))
        (_+_ A
          (_+_ A (_+_ A c₁ c₂) c₃)
          (_+_ A (_+_ A d₁ d₂) d₃))

open ThreeWayAdditiveInequalityCalculus public

record ConcreteReserveInequalityLeaves
    {t : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t) : Set (lsuc t) where
  field
    initialTime finalTime : Time
    packetLeaf gammaFloorLeaf offPacketLeaf :
      ReserveDifferentialInequalityLeaf A Time

    packetFinalNonnegative :
      _≤_ A (zero A) (reserve packetLeaf finalTime)
    gammaFinalNonnegative :
      _≤_ A (zero A) (reserve gammaFloorLeaf finalTime)
    offPacketFinalNonnegative :
      _≤_ A (zero A) (reserve offPacketLeaf finalTime)

open ConcreteReserveInequalityLeaves public

totalReservePotential :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveInequalityLeaves A Time → Time → Scalar A
totalReservePotential {A = A} R τ =
  _+_ A
    (_+_ A (reserve (packetLeaf R) τ) (reserve (gammaFloorLeaf R) τ))
    (reserve (offPacketLeaf R) τ)

totalReserveDerivative :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveInequalityLeaves A Time → Time → Scalar A
totalReserveDerivative {A = A} R τ =
  _+_ A
    (_+_ A
      (reserveDerivative (packetLeaf R) τ)
      (reserveDerivative (gammaFloorLeaf R) τ))
    (reserveDerivative (offPacketLeaf R) τ)

totalCoerciveRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveInequalityLeaves A Time → Time → Scalar A
totalCoerciveRate {A = A} R τ =
  _+_ A
    (_+_ A
      (coerciveRate (packetLeaf R) τ)
      (coerciveRate (gammaFloorLeaf R) τ))
    (coerciveRate (offPacketLeaf R) τ)

totalDissipationRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveInequalityLeaves A Time → Time → Scalar A
totalDissipationRate {A = A} R τ =
  _+_ A
    (_+_ A
      (dissipationRate (packetLeaf R) τ)
      (dissipationRate (gammaFloorLeaf R) τ))
    (dissipationRate (offPacketLeaf R) τ)

totalForcingRate :
  ∀ {t} {A : AbsorptionArithmetic} {Time : Set t} →
  ConcreteReserveInequalityLeaves A Time → Time → Scalar A
totalForcingRate {A = A} R τ =
  _+_ A
    (_+_ A
      (forcingRate (packetLeaf R) τ)
      (forcingRate (gammaFloorLeaf R) τ))
    (forcingRate (offPacketLeaf R) τ)

concrete-total-pointwise-inequality :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time) → ∀ τ →
  _≤_ A
    (_+_ A (totalReserveDerivative R τ) (totalCoerciveRate R τ))
    (_+_ A (totalDissipationRate R τ) (totalForcingRate R τ))
concrete-total-pointwise-inequality C R τ =
  combineThreeInequalities C
    (reserve-differential-inequality (packetLeaf R) τ)
    (reserve-differential-inequality (gammaFloorLeaf R) τ)
    (reserve-differential-inequality (offPacketLeaf R) τ)

------------------------------------------------------------------------
-- Inequality-native fundamental theorem and integral transport.
------------------------------------------------------------------------

record ConcreteInequalityIntegration
    {t : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t}
    (C : ThreeWayAdditiveInequalityCalculus A)
    (R : ConcreteReserveInequalityLeaves A Time) : Set (lsuc t) where
  field
    coerciveEnvelopeIntegral dissipationIntegral forcingIntegral : Scalar A
    dataRemainder forcingAndDataRemainder : Scalar A

    forcingAndDataMeaning :
      forcingAndDataRemainder ≡ _+_ A forcingIntegral dataRemainder

    fundamentalTheoremAndIntegralMonotonicity :
      (∀ τ →
        _≤_ A
          (_+_ A (totalReserveDerivative R τ) (totalCoerciveRate R τ))
          (_+_ A (totalDissipationRate R τ) (totalForcingRate R τ))) →
      _≤_ A
        (_+_ A
          (totalReservePotential R (finalTime R))
          (_+_ A coerciveEnvelopeIntegral dissipationIntegral))
        (_+_ A
          (totalReservePotential R (initialTime R))
          (_+_ A dissipationIntegral forcingAndDataRemainder))

open ConcreteInequalityIntegration public

asPointwiseInequalityExpenditure :
  ∀ {t} {A : AbsorptionArithmetic}
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time) →
  ConcreteInequalityIntegration A C R →
  PointwiseCompactGammaInequalityExpenditure A Time
asPointwiseInequalityExpenditure C R I = record
  { initialTime = initialTime R
  ; finalTime = finalTime R
  ; potential = totalReservePotential R
  ; potentialDerivative = totalReserveDerivative R
  ; coerciveEnvelopeRate = totalCoerciveRate R
  ; dissipationRate = totalDissipationRate R
  ; forcingRate = totalForcingRate R
  ; coerciveEnvelopeIntegral = coerciveEnvelopeIntegral I
  ; dissipationIntegral = dissipationIntegral I
  ; forcingTimeIntegral = forcingIntegral I
  ; dataRemainder = dataRemainder I
  ; forcingAndDataRemainder = forcingAndDataRemainder I
  ; forcingAndDataMeaning = forcingAndDataMeaning I
  ; pointwisePotentialInequality = concrete-total-pointwise-inequality C R
  ; integratePointwiseInequality = fundamentalTheoremAndIntegralMonotonicity I
  }

------------------------------------------------------------------------
-- Endpoint transport, using the concrete BE1--BE8 connection produced by the
-- Bernstein/domain module rather than accepting unrelated shell inequalities.
------------------------------------------------------------------------

record ConcreteInequalityClosureData
    {t l : Level}
    (A : AbsorptionArithmetic)
    (L : OrderedAdditiveInequalityLaws A)
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time)
    (I : ConcreteInequalityIntegration A C R) : Set (lsuc (t ⊔ l)) where
  field
    finalPotentialNonnegative :
      _≤_ A (zero A) (totalReservePotential R (finalTime R))

    weightedShellExpenditure vorticityExpenditure : Scalar A

    weightedShellBelowEnvelope :
      _≤_ A weightedShellExpenditure (coerciveEnvelopeIntegral I)

    vorticityBelowWeightedShell :
      _≤_ A vorticityExpenditure weightedShellExpenditure

    Continuation : Set l
    invokeBKMAtEndpoint :
      _≤_ A vorticityExpenditure
        (_+_ A
          (totalReservePotential R (initialTime R))
          (forcingAndDataRemainder I)) →
      Continuation

open ConcreteInequalityClosureData public

asInequalityTransport :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time)
    (I : ConcreteInequalityIntegration A C R) →
  ConcreteInequalityClosureData {l = l} A L C R I →
  InequalityCompactGammaTransport {l = l} A L
    (asPointwiseInequalityExpenditure C R I)
asInequalityTransport L C R I D = record
  { potentialFinalNonnegative = finalPotentialNonnegative D
  ; weightedShellExpenditure = weightedShellExpenditure D
  ; vorticityExpenditure = vorticityExpenditure D
  ; weightedShellBelowEnvelope = weightedShellBelowEnvelope D
  ; vorticityBelowWeightedShell = vorticityBelowWeightedShell D
  ; Continuation = Continuation D
  ; invokeBKMFromVorticityBound = invokeBKMAtEndpoint D
  }

concrete-inequality-finite-envelope-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time)
    (I : ConcreteInequalityIntegration A C R)
    (D : ConcreteInequalityClosureData {l = l} A L C R I) →
  _≤_ A
    (coerciveEnvelopeIntegral I)
    (_+_ A
      (totalReservePotential R (initialTime R))
      (forcingAndDataRemainder I))
concrete-inequality-finite-envelope-expenditure L C R I D =
  pointwise-compactGamma-finite-envelope-expenditure-inequality
    L
    (asPointwiseInequalityExpenditure C R I)
    (asInequalityTransport L C R I D)

concrete-inequality-finite-vorticity-expenditure :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time)
    (I : ConcreteInequalityIntegration A C R)
    (D : ConcreteInequalityClosureData {l = l} A L C R I) →
  _≤_ A
    (vorticityExpenditure D)
    (_+_ A
      (totalReservePotential R (initialTime R))
      (forcingAndDataRemainder I))
concrete-inequality-finite-vorticity-expenditure L C R I D =
  pointwise-compactGamma-finite-vorticity-expenditure-inequality
    L
    (asPointwiseInequalityExpenditure C R I)
    (asInequalityTransport L C R I D)

concrete-inequality-bkm-continuation :
  ∀ {t l} {A : AbsorptionArithmetic}
    (L : OrderedAdditiveInequalityLaws A)
    (C : ThreeWayAdditiveInequalityCalculus A)
    {Time : Set t}
    (R : ConcreteReserveInequalityLeaves A Time)
    (I : ConcreteInequalityIntegration A C R)
    (D : ConcreteInequalityClosureData {l = l} A L C R I) →
  Continuation D
concrete-inequality-bkm-continuation L C R I D =
  pointwise-compactGamma-bkm-continuation-inequality
    L
    (asPointwiseInequalityExpenditure C R I)
    (asInequalityTransport L C R I D)
