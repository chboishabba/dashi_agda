module DASHI.Physics.Closure.NSCompactGammaConcreteDyadicScalarCertificate where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)

------------------------------------------------------------------------
-- Exact nonnegative dyadic arithmetic at denominator eight.
--
-- A value n denotes n / 8.  This is sufficient for the canonical tuple
-- (8, 1/4, 1/4, 1/2, 2, 2, 1) and for a completely literal finite
-- absorption certificate.  No postulate, floating point computation, or
-- opaque Set-valued feasibility field occurs in this module.
------------------------------------------------------------------------

infix 4 _≤ᴺ_

data _≤ᴺ_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ᴺ n
  s≤s : ∀ {m n} → m ≤ᴺ n → suc m ≤ᴺ suc n

≤ᴺ-refl : ∀ n → n ≤ᴺ n
≤ᴺ-refl zero = z≤n
≤ᴺ-refl (suc n) = s≤s (≤ᴺ-refl n)

≤ᴺ-trans : ∀ {a b c} → a ≤ᴺ b → b ≤ᴺ c → a ≤ᴺ c
≤ᴺ-trans z≤n q = z≤n
≤ᴺ-trans (s≤s p) (s≤s q) = s≤s (≤ᴺ-trans p q)

oneᴺ twoᴺ fourᴺ eightᴺ sixteenᴺ : Nat
oneᴺ = suc zero
twoᴺ = suc oneᴺ
fourᴺ = twoᴺ + twoᴺ
eightᴺ = fourᴺ + fourᴺ
sixteenᴺ = eightᴺ + eightᴺ

quarterᴰ halfᴰ oneᴰ twoᴰ : Nat
quarterᴰ = twoᴺ
halfᴰ = fourᴺ
oneᴰ = eightᴺ
twoᴰ = sixteenᴺ

quarterPositiveᴰ : suc zero ≤ᴺ quarterᴰ
quarterPositiveᴰ = s≤s z≤n

halfPositiveᴰ : suc zero ≤ᴺ halfᴰ
halfPositiveᴰ = s≤s z≤n

halfStrictBarrierᴰ : suc halfᴰ ≤ᴺ oneᴰ
halfStrictBarrierᴰ =
  s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

------------------------------------------------------------------------
-- Literal R = 8 tail budget.
--
-- `baseWeightedCoefficient` is deliberately not called `cNear`: the cubic
-- near-triad term has no universal positive sign.  This coefficient belongs to
-- the positive dissipative/reserve term exposed by `AbsorbedGammaRoute`.
------------------------------------------------------------------------

canonicalRadius : Nat
canonicalRadius = eightᴺ

epsilonLowAtEight epsilonHighAtEight epsilonTailAtEight : Nat
epsilonLowAtEight = oneᴺ
epsilonHighAtEight = oneᴺ
epsilonTailAtEight = epsilonLowAtEight + epsilonHighAtEight

baseWeightedCoefficient halfBaseWeightedCoefficient : Nat
baseWeightedCoefficient = eightᴺ
halfBaseWeightedCoefficient = fourᴺ

epsilonTailMeaningAtEight :
  epsilonTailAtEight ≡ epsilonLowAtEight + epsilonHighAtEight
epsilonTailMeaningAtEight = refl

radiusEightControlsTailᴰ :
  epsilonTailAtEight ≤ᴺ halfBaseWeightedCoefficient
radiusEightControlsTailᴰ = s≤s (s≤s z≤n)

------------------------------------------------------------------------
-- Exact component gain/loss certificate.
------------------------------------------------------------------------

packetGain gammaGain offPacketGain : Nat
packetGain = fourᴺ
gammaGain = fourᴺ
offPacketGain = fourᴺ

packetLoss gammaLoss offPacketLoss : Nat
packetLoss = eightᴺ
gammaLoss = eightᴺ
offPacketLoss = twoᴺ

packetWeightTwoAbsorbsᴰ : packetLoss ≤ᴺ twoᴺ * packetGain
packetWeightTwoAbsorbsᴰ = ≤ᴺ-refl packetLoss

gammaWeightTwoAbsorbsᴰ : gammaLoss ≤ᴺ twoᴺ * gammaGain
gammaWeightTwoAbsorbsᴰ = ≤ᴺ-refl gammaLoss

offPacketWeightOneAbsorbsᴰ : offPacketLoss ≤ᴺ offPacketGain
offPacketWeightOneAbsorbsᴰ = s≤s (s≤s z≤n)

canonicalTotalGain canonicalTotalLoss canonicalCoerciveRemainder : Nat
canonicalTotalGain =
  twoᴺ * packetGain + twoᴺ * gammaGain + offPacketGain
canonicalTotalLoss = packetLoss + gammaLoss + offPacketLoss
canonicalCoerciveRemainder = twoᴺ

canonicalGainSplits :
  canonicalTotalGain ≡ canonicalTotalLoss + canonicalCoerciveRemainder
canonicalGainSplits = refl

canonicalTotalCoerciveCoefficientPositiveᴰ :
  suc zero ≤ᴺ canonicalCoerciveRemainder
canonicalTotalCoerciveCoefficientPositiveᴰ = s≤s z≤n

record ConcreteCanonicalScalarCertificate : Set where
  field
    quarter-positive : suc zero ≤ᴺ quarterᴰ
    half-positive : suc zero ≤ᴺ halfᴰ
    half-strict-barrier : suc halfᴰ ≤ᴺ oneᴰ
    radius-eight-tail-absorption :
      epsilonTailAtEight ≤ᴺ halfBaseWeightedCoefficient
    packet-weight-two-absorbs : packetLoss ≤ᴺ twoᴺ * packetGain
    gamma-weight-two-absorbs : gammaLoss ≤ᴺ twoᴺ * gammaGain
    off-packet-weight-one-absorbs : offPacketLoss ≤ᴺ offPacketGain
    positive-total-remainder : suc zero ≤ᴺ canonicalCoerciveRemainder

canonicalScalarCertificate : ConcreteCanonicalScalarCertificate
canonicalScalarCertificate = record
  { quarter-positive = quarterPositiveᴰ
  ; half-positive = halfPositiveᴰ
  ; half-strict-barrier = halfStrictBarrierᴰ
  ; radius-eight-tail-absorption = radiusEightControlsTailᴰ
  ; packet-weight-two-absorbs = packetWeightTwoAbsorbsᴰ
  ; gamma-weight-two-absorbs = gammaWeightTwoAbsorbsᴰ
  ; off-packet-weight-one-absorbs = offPacketWeightOneAbsorbsᴰ
  ; positive-total-remainder = canonicalTotalCoerciveCoefficientPositiveᴰ
  }

------------------------------------------------------------------------
-- Exact remaining quantitative bridge.  The Fourier layer must prove that
-- its normalized low/high constants fit the certified eighth-unit budgets.
------------------------------------------------------------------------

record RadiusEightAnalyticBounds : Set where
  field
    normalizedLowTailAtEight : Nat
    normalizedHighTailAtEight : Nat
    low-fits-certified-budget : normalizedLowTailAtEight ≤ᴺ epsilonLowAtEight
    high-fits-certified-budget : normalizedHighTailAtEight ≤ᴺ epsilonHighAtEight

open RadiusEightAnalyticBounds public

analyticBoundsGiveRadiusEightAbsorption :
  (B : RadiusEightAnalyticBounds) →
  normalizedLowTailAtEight B + normalizedHighTailAtEight B
    ≤ᴺ halfBaseWeightedCoefficient
analyticBoundsGiveRadiusEightAbsorption B =
  ≤ᴺ-+-combine
    (low-fits-certified-budget B)
    (high-fits-certified-budget B)
    radiusEightControlsTailᴰ
  where
  ≤ᴺ-step-r : ∀ {m n} → m ≤ᴺ n → m ≤ᴺ suc n
  ≤ᴺ-step-r z≤n = z≤n
  ≤ᴺ-step-r (s≤s p) = s≤s (≤ᴺ-step-r p)

  ≤ᴺ-+-mono : ∀ {a b c d} → a ≤ᴺ b → c ≤ᴺ d → a + c ≤ᴺ b + d
  ≤ᴺ-+-mono {zero} {zero} z≤n q = q
  ≤ᴺ-+-mono {zero} {suc b} z≤n q = ≤ᴺ-step-r (≤ᴺ-+-mono {zero} {b} z≤n q)
  ≤ᴺ-+-mono (s≤s p) q = s≤s (≤ᴺ-+-mono p q)

  ≤ᴺ-+-combine :
    ∀ {a b c d e} →
    a ≤ᴺ b → c ≤ᴺ d → b + d ≤ᴺ e → a + c ≤ᴺ e
  ≤ᴺ-+-combine p q r = ≤ᴺ-trans (≤ᴺ-+-mono p q) r
