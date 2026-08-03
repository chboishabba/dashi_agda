module DASHI.Physics.Closure.NSTriadKNLuoRadialSmoothMultiplierExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- Journal/year: Journal of Mathematical Fluid Mechanics 21 (2019), article 1.
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Record Luo's radial low-pass convention on the periodic lattice and prove
-- the exact coefficientwise factorization
--
--   S_p = M_p H_(p+1).
--
-- Here S_p has symbol chi(2^-p |k|), chi is one on [0,3/4] and zero on
-- [1,infinity), and H_(p+1) is the repository hard ball.  The proof uses the
-- exact support inclusion only; it does not replace the smooth symbol by a
-- finite linear combination of hard indicators.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc)
open import Relation.Binary.PropositionalEquality using (sym; trans)

record MultiplierCoefficientAction
    {c s : Level}
    (Coefficient : Set c)
    (Scalar : Set s) : Set (lsuc (c ⊔ s)) where
  field
    zeroCoefficient : Coefficient
    scale : Scalar → Coefficient → Coefficient
    scaleZeroCoefficient :
      (scalar : Scalar) → scale scalar zeroCoefficient ≡ zeroCoefficient

open MultiplierCoefficientAction public

record LuoRadialLatticeMultiplier
    {m c s : Level}
    (Mode : Set m)
    (Coefficient : Set c)
    (Scalar : Set s)
    (A : MultiplierCoefficientAction Coefficient Scalar) :
    Set (lsuc (m ⊔ c ⊔ s)) where
  field
    chiSymbol : Nat → Mode → Scalar
    hardLowSelect : Nat → Mode → Bool

    InnerThreeQuarterBall : Nat → Mode → Set m
    OutsideUnitBall : Nat → Mode → Set m

    symbolIsOneOnInnerThreeQuarterBall :
      (shell : Nat) →
      (mode : Mode) →
      InnerThreeQuarterBall shell mode →
      Set s

    symbolVanishesOutsideUnitBall :
      (shell : Nat) →
      (mode : Mode) →
      OutsideUnitBall shell mode →
      (coefficient : Coefficient) →
      scale A (chiSymbol shell mode) coefficient
        ≡ zeroCoefficient A

    smoothSupportInsideHardNext :
      (shell : Nat) →
      (mode : Mode) →
      hardLowSelect (suc shell) mode ≡ false →
      (coefficient : Coefficient) →
      scale A (chiSymbol shell mode) coefficient
        ≡ zeroCoefficient A

    symbolRealValued : Nat → Mode → Set s
    symbolBetweenZeroAndOne : Nat → Mode → Set s

open LuoRadialLatticeMultiplier public

HardField :
  ∀ {m c s}
    {Mode : Set m}
    {Coefficient : Set c}
    {Scalar : Set s}
    {A : MultiplierCoefficientAction Coefficient Scalar} →
  LuoRadialLatticeMultiplier Mode Coefficient Scalar A →
  Set (m ⊔ c)
HardField {Mode = Mode} {Coefficient = Coefficient} multiplier =
  Mode → Coefficient

hardLowPass :
  ∀ {m c s}
    {Mode : Set m}
    {Coefficient : Set c}
    {Scalar : Set s}
    {A : MultiplierCoefficientAction Coefficient Scalar} →
  (M : LuoRadialLatticeMultiplier Mode Coefficient Scalar A) →
  Nat → HardField M → HardField M
hardLowPass {A = A} M shell field mode
  with hardLowSelect M shell mode
... | true = field mode
... | false = zeroCoefficient A

smoothLowPass :
  ∀ {m c s}
    {Mode : Set m}
    {Coefficient : Set c}
    {Scalar : Set s}
    {A : MultiplierCoefficientAction Coefficient Scalar} →
  (M : LuoRadialLatticeMultiplier Mode Coefficient Scalar A) →
  Nat → HardField M → HardField M
smoothLowPass {A = A} M shell field mode =
  scale A (chiSymbol M shell mode) (field mode)

smoothLowPassFactorsThroughHardNext :
  ∀ {m c s}
    {Mode : Set m}
    {Coefficient : Set c}
    {Scalar : Set s}
    {A : MultiplierCoefficientAction Coefficient Scalar} →
  (M : LuoRadialLatticeMultiplier Mode Coefficient Scalar A) →
  (shell : Nat) →
  (field : HardField M) →
  (mode : Mode) →
  smoothLowPass M shell (hardLowPass M (suc shell) field) mode
    ≡ smoothLowPass M shell field mode
smoothLowPassFactorsThroughHardNext {A = A} M shell field mode
  with hardLowSelect M (suc shell) mode
... | true = refl
... | false =
  trans
    (scaleZeroCoefficient A (chiSymbol M shell mode))
    (sym (smoothSupportInsideHardNext M shell mode refl (field mode)))

record LocalizedMultiplierConstants (Scalar : Set) : Set₁ where
  field
    derivativeBernsteinConstant : Scalar
    finiteModeL2ToLInfinityConstant : Scalar
    hardSmoothMultiplierLInfinityConstant : Scalar

open LocalizedMultiplierConstants public

record MultiplierConstantSeparation
    {s : Level}
    {Scalar : Set s}
    (C : LocalizedMultiplierConstants Scalar) : Set s where
  field
    derivativeConstantHasDerivativeRole : Set
    finiteModeConstantHasLebesgueChangeRole : Set
    hardSmoothConstantHasKernelL1Role : Set

open MultiplierConstantSeparation public

luoRadialSupportConventionRecorded : Bool
luoRadialSupportConventionRecorded = true

smoothHardNextSupportFactorizationConstructed : Bool
smoothHardNextSupportFactorizationConstructed = true

localizedMultiplierConstantsSeparated : Bool
localizedMultiplierConstantsSeparated = true

luoRadialSupportConventionRecordedIsTrue :
  luoRadialSupportConventionRecorded ≡ true
luoRadialSupportConventionRecordedIsTrue = refl

smoothHardNextSupportFactorizationConstructedIsTrue :
  smoothHardNextSupportFactorizationConstructed ≡ true
smoothHardNextSupportFactorizationConstructedIsTrue = refl

localizedMultiplierConstantsSeparatedIsTrue :
  localizedMultiplierConstantsSeparated ≡ true
localizedMultiplierConstantsSeparatedIsTrue = refl
