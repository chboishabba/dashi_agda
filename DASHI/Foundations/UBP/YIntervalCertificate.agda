module DASHI.Foundations.UBP.YIntervalCertificate where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Rational using (ℚ; _+_; _-_; _*_; _/_; _<_; _≤_)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Foundations.UBP.ExternalRepositoryProvenance as Provenance

------------------------------------------------------------------------
-- Exact target / rational implementation / certified interval hierarchy.
--
-- The actual constructive-real π theorem remains an explicit input.  This
-- module prevents a finite rational convergent from being identified with π
-- while providing the exact shape needed to transport every affine TAX claim
-- uniformly over a certified interval.
------------------------------------------------------------------------

record PiApprox (ExactReal : Set) : Set₁ where
  field
    piExact : ExactReal
    convergentIndex : Nat
    numerator : ℚ
    denominator : ℚ
    epsilon : ℚ
    rationalApproximation : ℚ
    rationalApproximationDefinition :
      rationalApproximation ≡ numerator / denominator
    epsilonPositive : 0 < epsilon
    absoluteErrorBelowEpsilon : Set
    continuedFractionErrorReceipt : absoluteErrorBelowEpsilon

open PiApprox public

record YInterval (ExactReal : Set) (piApprox : PiApprox ExactReal) : Set₁ where
  field
    yExact : ExactReal
    y50 : ℚ
    epsilon50 : ℚ
    lower : ℚ
    upper : ℚ
    lowerDefinition : lower ≡ y50 - epsilon50
    upperDefinition : upper ≡ y50 + epsilon50
    epsilon50Positive : 0 < epsilon50
    exactYDefinition : Set
    y50Definition :
      y50
      ≡ rationalApproximation piApprox
        / (rationalApproximation piApprox * rationalApproximation piApprox + 2)
    containsExactY : Set
    containmentReceipt : containsExactY
    exactYIsIrrational : Set
    irrationalityReceipt : exactYIsIrrational

open YInterval public

record RationalInterval : Set where
  constructor rationalInterval
  field
    lo : ℚ
    hi : ℚ
    ordered : lo ≤ hi

open RationalInterval public

record AffineObservableIntervalTransport
    (ExactReal : Set)
    (piApprox : PiApprox ExactReal)
    (interval : YInterval ExactReal piApprox) : Set₁ where
  field
    support : ℚ
    normSquared : ℚ
    supportNonnegative : 0 ≤ support
    taxAt : ℚ → ℚ
    taxDefinition :
      (y : ℚ) →
      taxAt y ≡ support * y + normSquared / 8
    taxBounds : RationalInterval
    lowerTaxDefinition :
      lo taxBounds ≡ support * lower interval + normSquared / 8
    upperTaxDefinition :
      hi taxBounds ≡ support * upper interval + normSquared / 8
    uniformBound :
      (candidateY : ℚ) →
      lower interval ≤ candidateY →
      candidateY ≤ upper interval →
      lo taxBounds ≤ taxAt candidateY
    uniformUpperBound :
      (candidateY : ℚ) →
      lower interval ≤ candidateY →
      candidateY ≤ upper interval →
      taxAt candidateY ≤ hi taxBounds

open AffineObservableIntervalTransport public

record ObserverConstantIntervalStatus : Set where
  constructor observerConstantIntervalStatus
  field
    externalRepositoryURL : String
    externalAuthor : String
    sourcePath : String
    exactTargetSeparatedFromY50 : Bool
    exactTargetSeparatedFromY50IsTrue : exactTargetSeparatedFromY50 ≡ true
    continuedFractionCertificateRequired : Bool
    continuedFractionCertificateRequiredIsTrue :
      continuedFractionCertificateRequired ≡ true
    concreteP50Q50ImportedHere : Bool
    concreteP50Q50ImportedHereIsFalse : concreteP50Q50ImportedHere ≡ false
    exactPiConstructedHere : Bool
    exactPiConstructedHereIsFalse : exactPiConstructedHere ≡ false
    uniformAffineTransportAvailable : Bool
    uniformAffineTransportAvailableIsTrue :
      uniformAffineTransportAvailable ≡ true
    reading : String

open ObserverConstantIntervalStatus public

canonicalObserverConstantIntervalStatus : ObserverConstantIntervalStatus
canonicalObserverConstantIntervalStatus =
  observerConstantIntervalStatus
    Provenance.ubpRepositoryURL
    Provenance.ubpAuthorName
    "core_studio_v4.0/core/ubp_unified_v5.py"
    true refl
    true refl
    false refl
    false refl
    true refl
    "PiApprox and YInterval require the actual convergent and constructive-real containment proof; affine TAX statements can then be transported uniformly"

yIntervalGenericReceipt : GenericReceipt.GenericReceipt
yIntervalGenericReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "observer constant interval certificate"
    "DASHI.Foundations.UBP.YIntervalCertificate"
    "canonicalObserverConstantIntervalStatus"
    "the exact target, rational Y50, continued-fraction error, certified interval, irrationality receipt, and uniform affine-observable transport are separated"
    "the concrete p50/q50 values, exact pi construction, monotone transfer, and interval containment proof remain explicit obligations"
    "agda -i . DASHI/Foundations/UBP/YIntervalCertificate.agda"

yIntervalGenericReceiptNonPromoting :
  GenericReceipt.promotesClaim yIntervalGenericReceipt ≡ false
yIntervalGenericReceiptNonPromoting =
  GenericReceipt.promotesClaimIsFalse yIntervalGenericReceipt
