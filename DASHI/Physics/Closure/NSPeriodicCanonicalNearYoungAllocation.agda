module DASHI.Physics.Closure.NSPeriodicCanonicalNearYoungAllocation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact denominator-sixteen Young allocation.
--
-- The near interaction is split into LH, HL and HH placements.  The selected
-- dissipative payments are
--
--   LH = 1/16,  HL = 1/16,  HH = 1/8 = 2/16,
--
-- and therefore consume exactly 1/4 of the normalized viscosity budget.  This
-- module proves only the scalar allocation.  The Fourier product estimates must
-- still place their actual factors into these three shares.
------------------------------------------------------------------------

oneSixteenth oneEighth oneQuarter oneHalf oneWhole : Nat
oneSixteenth = suc zero
oneEighth = oneSixteenth + oneSixteenth
oneQuarter = oneEighth + oneEighth
oneHalf = oneQuarter + oneQuarter
oneWhole = oneHalf + oneHalf

lowHighYoungPayment highLowYoungPayment highHighYoungPayment : Nat
lowHighYoungPayment = oneSixteenth
highLowYoungPayment = oneSixteenth
highHighYoungPayment = oneEighth

nearYoungPayment : Nat
nearYoungPayment =
  lowHighYoungPayment + highLowYoungPayment + highHighYoungPayment

lowHighPaymentIsOneSixteenth :
  lowHighYoungPayment ≡ oneSixteenth
lowHighPaymentIsOneSixteenth = refl

highLowPaymentIsOneSixteenth :
  highLowYoungPayment ≡ oneSixteenth
highLowPaymentIsOneSixteenth = refl

highHighPaymentIsOneEighth :
  highHighYoungPayment ≡ oneEighth
highHighPaymentIsOneEighth = refl

nearPaymentsSumToQuarter : nearYoungPayment ≡ oneQuarter
nearPaymentsSumToQuarter = refl

quarterPlusQuarterIsHalf : oneQuarter + oneQuarter ≡ oneHalf
quarterPlusQuarterIsHalf = refl

halfPlusHalfIsWhole : oneHalf + oneHalf ≡ oneWhole
halfPlusHalfIsWhole = refl

record CanonicalNearYoungAllocation : Set where
  field
    low-high-share : lowHighYoungPayment ≡ oneSixteenth
    high-low-share : highLowYoungPayment ≡ oneSixteenth
    high-high-share : highHighYoungPayment ≡ oneEighth
    total-near-share : nearYoungPayment ≡ oneQuarter

canonicalNearYoungAllocation : CanonicalNearYoungAllocation
canonicalNearYoungAllocation = record
  { low-high-share = lowHighPaymentIsOneSixteenth
  ; high-low-share = highLowPaymentIsOneSixteenth
  ; high-high-share = highHighPaymentIsOneEighth
  ; total-near-share = nearPaymentsSumToQuarter
  }

------------------------------------------------------------------------
-- Interpretation in the official ordered additive carrier.
------------------------------------------------------------------------

record SixteenthBudgetInterpretation
    (A : AbsorptionArithmetic) : Set₁ where
  field
    interpret16 : Nat → Scalar A

    interpretZero : interpret16 zero ≡ zero A
    interpretAdd : ∀ m n →
      interpret16 (m + n) ≡ _+_ A (interpret16 m) (interpret16 n)

open SixteenthBudgetInterpretation public

interpretedLowHigh interpretedHighLow interpretedHighHigh
  interpretedNearPayment interpretedQuarter :
  ∀ {A : AbsorptionArithmetic} →
  SixteenthBudgetInterpretation A → Scalar A
interpretedLowHigh I = interpret16 I lowHighYoungPayment
interpretedHighLow I = interpret16 I highLowYoungPayment
interpretedHighHigh I = interpret16 I highHighYoungPayment
interpretedNearPayment I = interpret16 I nearYoungPayment
interpretedQuarter I = interpret16 I oneQuarter

interpretedNearPaymentDecomposes :
  ∀ {A : AbsorptionArithmetic}
    (I : SixteenthBudgetInterpretation A) →
  interpretedNearPayment I
  ≡
  _+_ A
    (_+_ A (interpretedLowHigh I) (interpretedHighLow I))
    (interpretedHighHigh I)
interpretedNearPaymentDecomposes {A = A} I =
  trans
    (interpretAdd I
      (lowHighYoungPayment + highLowYoungPayment)
      highHighYoungPayment)
    (cong
      (λ firstTwo → _+_ A firstTwo (interpretedHighHigh I))
      (interpretAdd I lowHighYoungPayment highLowYoungPayment))

interpretedNearPaymentIsQuarter :
  ∀ {A : AbsorptionArithmetic}
    (I : SixteenthBudgetInterpretation A) →
  interpretedNearPayment I ≡ interpretedQuarter I
interpretedNearPaymentIsQuarter I =
  cong (interpret16 I) nearPaymentsSumToQuarter

record CanonicalNearPaymentFit
    {A : AbsorptionArithmetic}
    (I : SixteenthBudgetInterpretation A)
    (lowHighTerm highLowTerm highHighTerm : Scalar A) : Set₁ where
  field
    lowHighFits : _≤_ A lowHighTerm (interpretedLowHigh I)
    highLowFits : _≤_ A highLowTerm (interpretedHighLow I)
    highHighFits : _≤_ A highHighTerm (interpretedHighHigh I)

open CanonicalNearPaymentFit public

canonicalNearComponentsFitQuarter :
  ∀ {A : AbsorptionArithmetic}
    {I : SixteenthBudgetInterpretation A}
    {lowHighTerm highLowTerm highHighTerm} →
  CanonicalNearPaymentFit I lowHighTerm highLowTerm highHighTerm →
  _≤_ A
    (_+_ A (_+_ A lowHighTerm highLowTerm) highHighTerm)
    (interpretedQuarter I)
canonicalNearComponentsFitQuarter
  {A = A} {I = I}
  {lowHighTerm = lowHighTerm}
  {highLowTerm = highLowTerm}
  {highHighTerm = highHighTerm} F =
  substUpper
    (interpretedNearPaymentIsQuarter I)
    (substUpper
      (interpretedNearPaymentDecomposes I)
      componentBound)
  where
  componentBound :
    _≤_ A
      (_+_ A (_+_ A lowHighTerm highLowTerm) highHighTerm)
      (_+_ A
        (_+_ A (interpretedLowHigh I) (interpretedHighLow I))
        (interpretedHighHigh I))
  componentBound =
    ≤-trans A
      (additionMonotoneRight A
        (≤-trans A
          (additionMonotoneRight A (lowHighFits F))
          (additionMonotoneLeft A (highLowFits F))))
      (additionMonotoneLeft A (highHighFits F))

  substUpper : ∀ {x y z : Scalar A} →
    y ≡ z → _≤_ A x y → _≤_ A x z
  substUpper refl proof = proof

------------------------------------------------------------------------
-- Status: the Young-share feasibility problem is closed exactly.  The remaining
-- near leaf is the cutoff-uniform Fourier estimate placing LH/HL/HH into these
-- fixed shares (plus the separately tracked residual envelope).
------------------------------------------------------------------------

canonicalNearYoungAllocationLevel : ProofLevel
canonicalNearYoungAllocationLevel = machineChecked
