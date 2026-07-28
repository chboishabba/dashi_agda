module DASHI.Physics.Closure.NSTriadKNConstructiveRealPowerBridge where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Errett Bishop; Douglas Bridges; Zachary Murray; DASHI repository
-- contributors.
-- Title: "Constructive-real bridge for non-integral dyadic Sobolev powers and
-- geometric shell sums".
-- Venue/year: Constructive Analysis, Springer, 1985; Constructive Analysis in
-- the Agda Proof Assistant, 2022; DASHI formal development, 2026.
-- DOI: 10.1007/978-3-642-61667-9;
-- 10.48550/arXiv.2205.08354; the repository adapter has no DOI.
-- Source snapshot: z-murray/honours-project-constructive-analysis-in-agda,
-- thesis commit 5cd6d3d023279518213f3e58879bfc867bb2503c.
-- Uses: ordered constructive reals, rational embedding, positive powers,
-- dyadic exponent laws, and convergent geometric series.
-- Relationship: identifies the exact external implementation intended for the
-- H^s layer. It does not silently equate rational finite-cutoff inequalities
-- with non-integral real powers, and it remains fail-closed until module names,
-- Agda version and the required power/series laws are checked in the
-- authoritative build.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

record ConstructiveRealPowerCarrier
    {r q : Level} : Set (lsuc (r ⊔ q)) where
  field
    Real : Set r
    Rational : Set q

    zero one two : Real
    rationalEmbed : Rational → Real
    add multiply subtract : Real → Real → Real
    _≤_ _<_ : Real → Real → Set r

    power : Real → Real → Real
    natPower : Real → Nat → Real
    dyadicShellPower : Real → Nat → Real

    orderReflexive : ∀ value → value ≤ value
    orderTransitive : ∀ {a b c} → a ≤ b → b ≤ c → a ≤ c
    orderAntisymmetric : ∀ {a b} → a ≤ b → b ≤ a → a ≡ b

    rationalEmbedOrderPreserving : Set (r ⊔ q)
    rationalFiniteSumPreserving : Set (r ⊔ q)
    rationalFiniteProductPreserving : Set (r ⊔ q)

    twoPositive : zero < two
    powerPositive : ∀ base exponent → zero < base → zero < power base exponent
    powerAddExponent : ∀ base first second → zero < base →
      power base (add first second)
      ≡ multiply (power base first) (power base second)

    dyadicShellMeaning : ∀ exponent shell →
      dyadicShellPower exponent shell
      ≡ power two (multiply exponent (natPower two shell))

    geometricTail : Real → Nat → Real
    geometricTailBound : ∀ ratio start →
      zero ≤ ratio → ratio < one →
      zero ≤ geometricTail ratio start
    geometricSeriesConverges : ∀ ratio →
      zero ≤ ratio → ratio < one → Set r

open ConstructiveRealPowerCarrier public

record Stage3SobolevPowerAdapter
    {r q : Level}
    (C : ConstructiveRealPowerCarrier {r} {q}) : Set (lsuc (r ⊔ q)) where
  field
    fiveHalves three : Real C
    openSobolevExponent : Real C → Set r

    openIntervalMeaning : ∀ exponent →
      openSobolevExponent exponent →
      _<_ C fiveHalves exponent × _<_ C exponent three

    lowDecayExponent : Real C → Real C
    gapDecayDirectFirst : Real C → Real C
    gapDecayLowDerivative : Real C → Real C

    lowDecayPositive : ∀ exponent →
      openSobolevExponent exponent →
      _<_ C (zero C) (lowDecayExponent exponent)

    directGapDecayPositive : ∀ exponent →
      openSobolevExponent exponent →
      _<_ C (zero C) (gapDecayDirectFirst exponent)

    lowDerivativeGapDecayPositive : ∀ exponent →
      openSobolevExponent exponent →
      _<_ C (zero C) (gapDecayLowDerivative exponent)

    directFirstGapSeriesSummable : ∀ exponent →
      openSobolevExponent exponent → Set r

    allFourFavourableGapSeriesSummable : ∀ exponent →
      openSobolevExponent exponent → Set r

open Stage3SobolevPowerAdapter public

murrayConstructiveAnalysisSourcePinned : Bool
murrayConstructiveAnalysisSourcePinned = true

murrayConstructiveAnalysisSourcePinnedIsTrue :
  murrayConstructiveAnalysisSourcePinned ≡ true
murrayConstructiveAnalysisSourcePinnedIsTrue = refl

constructiveRealNamespaceCompatibilityChecked : Bool
constructiveRealNamespaceCompatibilityChecked = false

constructiveRealNamespaceCompatibilityCheckedIsFalse :
  constructiveRealNamespaceCompatibilityChecked ≡ false
constructiveRealNamespaceCompatibilityCheckedIsFalse = refl

stage3ConstructiveRealPowerAdapterClosed : Bool
stage3ConstructiveRealPowerAdapterClosed = false

stage3ConstructiveRealPowerAdapterClosedIsFalse :
  stage3ConstructiveRealPowerAdapterClosed ≡ false
stage3ConstructiveRealPowerAdapterClosedIsFalse = refl
