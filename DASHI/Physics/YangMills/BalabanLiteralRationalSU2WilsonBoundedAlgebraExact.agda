{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanLiteralRationalSU2WilsonBoundedAlgebraExact where

------------------------------------------------------------------------
-- CONCRETE S2 ANALYSIS: LITERAL RATIONAL SU(2) WILSON FUNCTIONS FORM A
-- POINTWISE-UNIT-BOUNDED MULTIPLICATIVE ALGEBRA.
--
-- This is the non-opaque mathematical boundedness theorem missing underneath
-- the old T5 `BoundedObservable` interface.  A configuration is the existing
-- periodic rational-SU(2) bond carrier.  A path observable evaluates the
-- normalized real trace of the actual typed path holonomy.  Since path
-- holonomy remains a RationalUnitQuaternion, the exact trace theorem gives
-- |W_C(U)| <= 1 pointwise.  Identity and products remain pointwise bounded.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _*_; _≤_; -_; ∣_∣; NonNegative; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)
import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4RationalSU2BondCarrierExact as Carrier
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonLargeFieldGapExact as SU2
import DASHI.Physics.YangMills.BalabanSU2RationalWilsonTraceBoundExact as Trace

record RationalWilsonPath (n : Nat) : Set where
  constructor wilsonPath
  field
    base : Periodic.PeriodicBlock n
    directions : List SignedAxis4

open RationalWilsonPath public

RationalWilsonObservable : Nat → Set
RationalWilsonObservable n = Carrier.RationalSU2BondData n → ℚ

literalWilsonPathObservable :
  ∀ {n} → RationalWilsonPath n → RationalWilsonObservable n
literalWilsonPathObservable path configuration =
  SU2.realPart
    (Bond.pathHolonomy
      (Carrier.realization configuration)
      (base path)
      (directions path))

PointwiseUnitBounded :
  ∀ {n} → RationalWilsonObservable n → Set
PointwiseUnitBounded observable =
  ∀ configuration → ∣ observable configuration ∣ ≤ 1ℚ

absBoundFromTwoSided :
  ∀ {x : ℚ} → - 1ℚ ≤ x → x ≤ 1ℚ → ∣ x ∣ ≤ 1ℚ
absBoundFromTwoSided {x} lower upper with ℚP.≤-total 0ℚ x
... | inj₁ xNN =
  subst (_≤ 1ℚ) (sym (ℚP.0≤p⇒∣p∣≡p xNN)) upper
... | inj₂ xNP =
  let
    negUpperRaw = ℚP.neg-antimono-≤ lower
    negUpper : - x ≤ 1ℚ
    negUpper = negUpperRaw

    negXNNRaw = ℚP.neg-antimono-≤ xNP
    negXNN : 0ℚ ≤ - x
    negXNN = negXNNRaw

    absNegative : ∣ x ∣ ≡ - x
    absNegative =
      Relation.Binary.PropositionalEquality.trans
        (sym (ℚP.∣-p∣≡∣p∣ x))
        (ℚP.0≤p⇒∣p∣≡p negXNN)
  in
  subst (_≤ 1ℚ) (sym absNegative) negUpper

literalWilsonPathPointwiseUnitBounded :
  ∀ {n} (path : RationalWilsonPath n) →
  PointwiseUnitBounded (literalWilsonPathObservable path)
literalWilsonPathPointwiseUnitBounded path configuration =
  let
    holonomy =
      Bond.pathHolonomy
        (Carrier.realization configuration)
        (base path)
        (directions path)
  in
  absBoundFromTwoSided
    (Trace.normalizedTraceLowerBound holonomy)
    (Trace.normalizedTraceUpperBound holonomy)

oneObservable : ∀ {n} → RationalWilsonObservable n
oneObservable _ = 1ℚ

multiplyObservable :
  ∀ {n} →
  RationalWilsonObservable n →
  RationalWilsonObservable n →
  RationalWilsonObservable n
multiplyObservable left right configuration =
  left configuration * right configuration

oneNonnegative : 0ℚ ≤ 1ℚ
oneNonnegative = ℚP.0≤∣p∣ 1ℚ

oneObservablePointwiseUnitBounded :
  ∀ {n} → PointwiseUnitBounded (oneObservable {n})
oneObservablePointwiseUnitBounded configuration =
  subst (_≤ 1ℚ)
    (sym (ℚP.0≤p⇒∣p∣≡p oneNonnegative))
    ℚP.≤-refl

absoluteProductBound :
  ∀ {left right leftBound rightBound : ℚ} →
  ∣ left ∣ ≤ leftBound →
  ∣ right ∣ ≤ rightBound →
  0ℚ ≤ leftBound →
  0ℚ ≤ rightBound →
  ∣ left * right ∣ ≤ leftBound * rightBound
absoluteProductBound
    {left} {right} {leftBound} {rightBound}
    leftBounded rightBounded leftBoundNN rightBoundNN =
  let
    instance
      absRightNN : NonNegative ∣ right ∣
      absRightNN = ℚP.∣-∣-nonNeg right

      leftBoundNonnegative : NonNegative leftBound
      leftBoundNonnegative = nonNegative leftBoundNN

    first :
      ∣ left ∣ * ∣ right ∣ ≤ leftBound * ∣ right ∣
    first = ℚP.*-monoʳ-≤-nonNeg ∣ right ∣ leftBounded

    second :
      leftBound * ∣ right ∣ ≤ leftBound * rightBound
    second = ℚP.*-monoˡ-≤-nonNeg leftBound rightBounded
  in
  subst
    (λ lower → lower ≤ leftBound * rightBound)
    (sym (ℚP.∣p*q∣≡∣p∣*∣q∣ left right))
    (ℚP.≤-trans first second)

multiplyPointwiseUnitBounded :
  ∀ {n}
    {left right : RationalWilsonObservable n} →
  PointwiseUnitBounded left →
  PointwiseUnitBounded right →
  PointwiseUnitBounded (multiplyObservable left right)
multiplyPointwiseUnitBounded leftBounded rightBounded configuration =
  subst (_≤ 1ℚ)
    (ℚP.*-identityʳ 1ℚ)
    (absoluteProductBound
      (leftBounded configuration)
      (rightBounded configuration)
      oneNonnegative
      oneNonnegative)

literalRationalSU2WilsonFunctionBoundLevel : ProofLevel
literalRationalSU2WilsonFunctionBoundLevel = machineChecked

literalRationalSU2WilsonBoundedAlgebraLevel : ProofLevel
literalRationalSU2WilsonBoundedAlgebraLevel = machineChecked
