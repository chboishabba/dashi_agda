{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityLorentzianF2ContinuationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _≤_)
import DASHI.Physics.Foundations.CMP119AntigravityEuclideanLorentzianF2FirewallExact as Firewall

------------------------------------------------------------------------
-- AG-S3 / EXPLICIT EUCLIDEAN -> LORENTZIAN F^2 CONTINUATION RECEIPT
--
-- This does not assert Wick rotation for CMP119.  It names the exact
-- same-object data needed before the Euclidean Wilson/Haar F^2 observable can
-- be consumed by the Lorentzian trace anomaly.
------------------------------------------------------------------------

record LorentzianF2ContinuationReceipt : Set where
  field
    electricSquare : ℚ
    magneticSquare : ℚ

    electricSquareNonnegative : 0ℚ ≤ electricSquare
    magneticSquareNonnegative : 0ℚ ≤ magneticSquare

    selectedEuclideanF2 : ℚ
    selectedLorentzianF2 : ℚ

    euclideanSameObject :
      selectedEuclideanF2
      ≡ Firewall.euclideanF2 electricSquare magneticSquare

    lorentzianSameObject :
      selectedLorentzianF2
      ≡ Firewall.lorentzianF2 electricSquare magneticSquare

    -- Physical continuation/provenance token.  This is not compiler-created:
    -- it asserts that both selected observables are the Euclidean and
    -- Lorentzian continuations of the SAME renormalized gauge-field operator.
    sameRenormalizedOperator : Set
    sameRenormalizedOperatorWitness : sameRenormalizedOperator

open LorentzianF2ContinuationReceipt public

continuationSeparatesEuclideanAndLorentzianValues : Bool
continuationSeparatesEuclideanAndLorentzianValues = true

continuationSeparatesEuclideanAndLorentzianValuesIsTrue :
  continuationSeparatesEuclideanAndLorentzianValues ≡ true
continuationSeparatesEuclideanAndLorentzianValuesIsTrue = refl

euclideanPositivityAloneConstructsContinuation : Bool
euclideanPositivityAloneConstructsContinuation = false

euclideanPositivityAloneConstructsContinuationIsFalse :
  euclideanPositivityAloneConstructsContinuation ≡ false
euclideanPositivityAloneConstructsContinuationIsFalse = refl
