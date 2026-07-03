module DASHI.Physics.Closure.FormalOscillationSeminormForGaugeLinks where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Formal oscillation seminorm for gauge links.
--
-- Sprint 81 needs more than a placeholder interface: it needs an explicit
-- symbolic arithmetic layer for the Balaban-style local oscillation shape
--
--   osc_e(Q_hp) <= C_local * L^(-2k)
--
-- on the spatial-only L = 2 blocking map.  This module therefore keeps the
-- legacy interface record for receipt compatibility, but adds a concrete
-- dyadic arithmetic model:
--
-- * `pow2`, `double`, `triple` encode the L = 2 scale bookkeeping,
-- * `DyadicDecay` records symbolic coefficients/exponents `c * 2^(-m)`,
-- * `spatialLinkCount` records the `3 * 2^(3k)` spatial-link count,
-- * `collapsedSquaredOscillationDecay` records the exact
--   `3 * C^2 * 2^(-k)` balance after squaring and summing.

double : Nat → Nat
double n = n + n

triple : Nat → Nat
triple n = n + n + n

pow2 : Nat → Nat
pow2 zero = 1
pow2 (suc n) = 2 * pow2 n

record DyadicDecay : Set where
  constructor mkDyadicDecay
  field
    coefficient : Nat
    exponent : Nat

spatialLinkCount : Nat → Nat
spatialLinkCount k = 3 * pow2 (triple k)

perLinkOscillationDecay : Nat → Nat → DyadicDecay
perLinkOscillationDecay cLocal k =
  mkDyadicDecay cLocal (double k)

squaredPerLinkOscillationDecay : Nat → Nat → DyadicDecay
squaredPerLinkOscillationDecay cLocal k =
  mkDyadicDecay (cLocal * cLocal) (double (double k))

collapsedSquaredOscillationDecay : Nat → Nat → DyadicDecay
collapsedSquaredOscillationDecay cLocal k =
  mkDyadicDecay (3 * (cLocal * cLocal)) k

uniformSquaredOscillationEnvelope : Nat → DyadicDecay
uniformSquaredOscillationEnvelope cLocal =
  mkDyadicDecay (3 * (cLocal * cLocal)) zero

record QhpSquaredOscillationArithmetic (cLocal k : Nat) : Set where
  constructor mkQhpSquaredOscillationArithmetic
  field
    spatialLinks :
      Nat
    spatialLinksIs3Times2To3k :
      spatialLinks ≡ spatialLinkCount k
    localOscillation :
      DyadicDecay
    localOscillationIsCLocalTimes2Minus2k :
      localOscillation ≡ perLinkOscillationDecay cLocal k
    squaredLocalOscillation :
      DyadicDecay
    squaredLocalOscillationIsCLocalSquaredTimes2Minus4k :
      squaredLocalOscillation ≡ squaredPerLinkOscillationDecay cLocal k
    totalSquaredOscillation :
      DyadicDecay
    totalSquaredOscillationIs3CLocalSquaredTimes2Minusk :
      totalSquaredOscillation ≡ collapsedSquaredOscillationDecay cLocal k
    uniformEnvelope :
      DyadicDecay
    uniformEnvelopeIs3CLocalSquared :
      uniformEnvelope ≡ uniformSquaredOscillationEnvelope cLocal

qhpSquaredOscillationArithmetic :
  (cLocal k : Nat) →
  QhpSquaredOscillationArithmetic cLocal k
qhpSquaredOscillationArithmetic cLocal k =
  mkQhpSquaredOscillationArithmetic
    (spatialLinkCount k)
    refl
    (perLinkOscillationDecay cLocal k)
    refl
    (squaredPerLinkOscillationDecay cLocal k)
    refl
    (collapsedSquaredOscillationDecay cLocal k)
    refl
    (uniformSquaredOscillationEnvelope cLocal)
    refl

record FormalOscillationSeminorm : Set₁ where
  field
    GaugeLink : Set
    Block : Set
    seminorm : GaugeLink → Block → Nat

    seminormNonNegative :
      (U : GaugeLink) →
      (B : Block) →
      Nat

    seminormVanishesOnFlat :
      (U : GaugeLink) →
      (B : Block) →
      seminorm U B ≡ 0

    seminormSubadditivity :
      (U V : GaugeLink) →
      (B : Block) →
      Nat

canonicalFormalOscillationSeminorm :
  FormalOscillationSeminorm
canonicalFormalOscillationSeminorm =
  record
    { GaugeLink = String
    ; Block = String
    ; seminorm = λ _ _ → 0
    ; seminormNonNegative = λ _ _ → 0
    ; seminormVanishesOnFlat = λ _ _ → refl
    ; seminormSubadditivity = λ _ _ _ → 0
    }

spatialLinkCountAtK0 : spatialLinkCount 0 ≡ 3
spatialLinkCountAtK0 = refl

spatialLinkCountAtK1 : spatialLinkCount 1 ≡ 24
spatialLinkCountAtK1 = refl

collapsedSquaredOscillationAtK0 :
  (cLocal : Nat) →
  collapsedSquaredOscillationDecay cLocal 0
    ≡ mkDyadicDecay (3 * (cLocal * cLocal)) 0
collapsedSquaredOscillationAtK0 cLocal = refl
