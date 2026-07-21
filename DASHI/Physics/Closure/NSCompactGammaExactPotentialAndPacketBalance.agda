module DASHI.Physics.Closure.NSCompactGammaExactPotentialAndPacketBalance where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans; sym)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion

------------------------------------------------------------------------
-- P0.1--P0.4: exact selected reserve formulas.
--
-- The selected off-packet reserve is linear:
--
--   Φoff(t) = αR R K R (u(t)).
--
-- Packet energy and Gamma use logarithmic floor barriers.
------------------------------------------------------------------------

record ExactPotentialArithmetic
    (A : AbsorptionArithmetic) : Set₁ where
  field
    _*_ _/_ : Scalar A → Scalar A → Scalar A
    negative : Scalar A → Scalar A
    negativeLog : Scalar A → Scalar A

open ExactPotentialArithmetic public

record CompactGammaPotentialData
    {t : Level}
    (A : AbsorptionArithmetic)
    (X : ExactPotentialArithmetic A)
    (Time : Set t) : Set (lsuc t) where
  field
    K R : Scalar A
    αE αΓ αR : Scalar A
    eFloor gammaFloor : Scalar A
    packetEnergy gammaFunctional offPacketRatio : Time → Scalar A

open CompactGammaPotentialData public

packetReserveFormula :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t} →
  CompactGammaPotentialData A X Time → Time → Scalar A
packetReserveFormula {X = X} P τ =
  _*_ X (αE P)
    (negativeLog X (_/_ X (packetEnergy P τ) (eFloor P)))

gammaFloorReserveFormula :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t} →
  CompactGammaPotentialData A X Time → Time → Scalar A
gammaFloorReserveFormula {X = X} P τ =
  _*_ X (αΓ P)
    (negativeLog X (_/_ X (gammaFunctional P τ) (gammaFloor P)))

offPacketReserveFormula :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t} →
  CompactGammaPotentialData A X Time → Time → Scalar A
offPacketReserveFormula {X = X} P τ =
  _*_ X (αR P) (offPacketRatio P τ)

selectedTotalPotential :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t} →
  CompactGammaPotentialData A X Time → Time → Scalar A
selectedTotalPotential {A = A} P τ =
  _+_ A
    (_+_ A (packetReserveFormula P τ) (gammaFloorReserveFormula P τ))
    (offPacketReserveFormula P τ)

packetReserveMeaning :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (P : CompactGammaPotentialData A X Time) (τ : Time) →
  packetReserveFormula P τ ≡
  _*_ X (αE P)
    (negativeLog X (_/_ X (packetEnergy P τ) (eFloor P)))
packetReserveMeaning P τ = refl

gammaFloorReserveMeaning :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (P : CompactGammaPotentialData A X Time) (τ : Time) →
  gammaFloorReserveFormula P τ ≡
  _*_ X (αΓ P)
    (negativeLog X (_/_ X (gammaFunctional P τ) (gammaFloor P)))
gammaFloorReserveMeaning P τ = refl

offPacketReserveMeaning :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (P : CompactGammaPotentialData A X Time) (τ : Time) →
  offPacketReserveFormula P τ ≡
  _*_ X (αR P) (offPacketRatio P τ)
offPacketReserveMeaning P τ = refl

totalPotentialMeaning :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (P : CompactGammaPotentialData A X Time) (τ : Time) →
  selectedTotalPotential P τ ≡
  _+_ A
    (_+_ A (packetReserveFormula P τ) (gammaFloorReserveFormula P τ))
    (offPacketReserveFormula P τ)
totalPotentialMeaning P τ = refl

------------------------------------------------------------------------
-- PE1--PE4: finite-shell differentiation and Galerkin substitution.
--
-- `nonlinearPacketIdentity` explicitly identifies the Fourier nonlinear sum
-- with the repository's canonical triad fold; it is not a second definition.
------------------------------------------------------------------------

record PacketFourierCalculus
    {t m : Level}
    (A : AbsorptionArithmetic)
    (Time : Set t)
    (Mode : Set m) : Set (lsuc (t ⊔ m)) where
  field
    retained : Mode → Set

    packetEnergy packetEnergyDerivative : Time → Scalar A
    packetState packetDerivative : Time → Scalar A
    realInner : Scalar A → Scalar A → Scalar A

    timeDerivativeCoeff viscousCoeff nonlinearCoeff :
      Mode → Time → Scalar A

    viscousPacketSum nonlinearPacketSum : Time → Scalar A
    negativePacketRate packetCoerciveRate canonicalTriadTransfer :
      Time → Scalar A

    -- PE1
    differentiatePacketEnergy : ∀ τ →
      packetEnergyDerivative τ ≡
      realInner (packetDerivative τ) (packetState τ)

    -- PE2
    galerkinFourierEquationAtMode : ∀ k τ →
      retained k →
      timeDerivativeCoeff k τ ≡
      _+_ A (viscousCoeff k τ) (nonlinearCoeff k τ)

    -- PE3
    viscousPacketIdentity : ∀ τ →
      viscousPacketSum τ ≡ negativePacketRate τ

    -- PE4
    nonlinearPacketIdentity : ∀ τ →
      nonlinearPacketSum τ ≡ canonicalTriadTransfer τ

    differentiatedEnergySplits : ∀ τ →
      packetEnergyDerivative τ ≡
      _+_ A (viscousPacketSum τ) (nonlinearPacketSum τ)

    -- The equality obtained by rewriting the preceding three facts.
    differentiatedEnergyNormalized : ∀ τ →
      packetEnergyDerivative τ ≡
      _+_ A (negativePacketRate τ) (canonicalTriadTransfer τ)

open PacketFourierCalculus public

------------------------------------------------------------------------
-- PE5: exact packet balance.
--
-- Ring normalization is explicit because AbsorptionArithmetic intentionally
-- does not itself provide additive inverses or cancellation.
------------------------------------------------------------------------

record PacketBalanceNormalization
    {t m : Level}
    (A : AbsorptionArithmetic)
    {Time : Set t} {Mode : Set m}
    (P : PacketFourierCalculus A Time Mode) : Set (lsuc (t ⊔ m)) where
  field
    normalizePacketBalance : ∀ τ →
      packetEnergyDerivative P τ ≡
        _+_ A (negativePacketRate P τ) (canonicalTriadTransfer P τ) →
      _+_ A (packetEnergyDerivative P τ) (packetCoerciveRate P τ) ≡
        _+_ A (canonicalTriadTransfer P τ) (zero A)

open PacketBalanceNormalization public

packetNavierStokesFunctionalBalance :
  ∀ {t m} {A : AbsorptionArithmetic}
    {Time : Set t} {Mode : Set m}
    (P : PacketFourierCalculus A Time Mode) →
  PacketBalanceNormalization A P → ∀ τ →
  _+_ A (packetEnergyDerivative P τ) (packetCoerciveRate P τ) ≡
    _+_ A (canonicalTriadTransfer P τ) (zero A)
packetNavierStokesFunctionalBalance P N τ =
  normalizePacketBalance N τ (differentiatedEnergyNormalized P τ)

------------------------------------------------------------------------
-- PE6: logarithmic packet-barrier chain rule.
------------------------------------------------------------------------

record PacketLogBarrierChainRule
    {t : Level}
    (A : AbsorptionArithmetic)
    (X : ExactPotentialArithmetic A)
    (Time : Set t) : Set (lsuc t) where
  field
    αE eFloor : Scalar A
    packetEnergy packetEnergyDerivative : Time → Scalar A
    packetEnergyPositive : Time → Set
    packetEnergyDifferentiable : Time → Set
    packetReserveDerivative : Time → Scalar A

    realNegativeLogChainRule : ∀ τ →
      packetEnergyPositive τ →
      packetEnergyDifferentiable τ →
      packetReserveDerivative τ ≡
      _/_ X
        (_*_ X (negative X αE) (packetEnergyDerivative τ))
        (packetEnergy τ)

open PacketLogBarrierChainRule public

packetReserveChainRule :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t} →
  (B : PacketLogBarrierChainRule A X Time) → ∀ τ →
  packetEnergyPositive B τ →
  packetEnergyDifferentiable B τ →
  packetReserveDerivative B τ ≡
  _/_ X
    (_*_ X (negative X (αE B)) (packetEnergyDerivative B τ))
    (packetEnergy B τ)
packetReserveChainRule B τ positive differentiable =
  realNegativeLogChainRule B τ positive differentiable

------------------------------------------------------------------------
-- PE7: packet-reserve differential identity.
--
-- A selected scaling lemma maps PE5 through -αE / E.  The existing generic
-- reserve theorem then performs only the final equality transport.
------------------------------------------------------------------------

record PacketReserveRateDecomposition
    {t : Level}
    (A : AbsorptionArithmetic)
    (X : ExactPotentialArithmetic A)
    (Time : Set t)
    (B : PacketLogBarrierChainRule A X Time) : Set (lsuc t) where
  field
    packetCoerciveRate packetDissipationRate packetForcingRate :
      Time → Scalar A
    scaledPacketFunctionalDerivative : Time → Scalar A

    scaledDerivativeMeaning : ∀ τ →
      scaledPacketFunctionalDerivative τ ≡
      _/_ X
        (_*_ X (negative X (αE B)) (packetEnergyDerivative B τ))
        (packetEnergy B τ)

    scaledPacketBalance : ∀ τ →
      _+_ A
        (scaledPacketFunctionalDerivative τ)
        (packetCoerciveRate τ)
      ≡
      _+_ A
        (packetDissipationRate τ)
        (packetForcingRate τ)

open PacketReserveRateDecomposition public

packetReserveLeaf :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (B : PacketLogBarrierChainRule A X Time)
    (D : PacketReserveRateDecomposition A X Time B) →
    (∀ τ → packetEnergyPositive B τ) →
    (∀ τ → packetEnergyDifferentiable B τ) →
  ReserveDifferentialLeaf A Time
packetReserveLeaf {X = X} B D positive differentiable = record
  { reserve = λ τ →
      _*_ X (αE B)
        (negativeLog X (_/_ X (packetEnergy B τ) (eFloor B)))
  ; reserveDerivative = packetReserveDerivative B
  ; functionalDerivative = scaledPacketFunctionalDerivative D
  ; coerciveRate = packetCoerciveRate D
  ; dissipationRate = packetDissipationRate D
  ; forcingRate = packetForcingRate D
  ; reserveChainRule = λ τ →
      trans
        (packetReserveChainRule B τ (positive τ) (differentiable τ))
        (sym (scaledDerivativeMeaning D τ))
  ; functionalNavierStokesBalance = scaledPacketBalance D
  }

packet-reserve-differential-identity-exact :
  ∀ {t} {A : AbsorptionArithmetic}
    {X : ExactPotentialArithmetic A} {Time : Set t}
    (B : PacketLogBarrierChainRule A X Time)
    (D : PacketReserveRateDecomposition A X Time B)
    (positive : ∀ τ → packetEnergyPositive B τ)
    (differentiable : ∀ τ → packetEnergyDifferentiable B τ) → ∀ τ →
  _+_ A
    (packetReserveDerivative B τ)
    (packetCoerciveRate D τ)
  ≡
  _+_ A
    (packetDissipationRate D τ)
    (packetForcingRate D τ)
packet-reserve-differential-identity-exact B D positive differentiable =
  reserve-differential-identity
    (packetReserveLeaf B D positive differentiable)
