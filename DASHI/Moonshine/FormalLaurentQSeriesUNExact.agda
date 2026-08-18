module DASHI.Moonshine.FormalLaurentQSeriesUNExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CORRECTION
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Their modular functions include normalized Hauptmoduls with principal part
-- q^{-1}.  Therefore the correct formal coefficient carrier for Section 2/3 is
-- indexed by Z, not Nat.
--
-- Equation (2.4) still has the exact coefficient law
--
--   c_n(f | U_N) = c_{nN}(f)
--
-- for signed Laurent indices n.
--
-- DASHI CONTRIBUTION
--
-- Construct that signed formal carrier and U_N coefficient selector.  The
-- earlier Nat-indexed FormalQSeries operator remains useful for holomorphic
-- oldforms, but is not promoted to the modular-function carrier used here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Integer using (ℤ; +_; -[1+_])
  renaming (_*_ to _*ℤ_)
import Data.Integer.Tactic.RingSolver as ℤRing

------------------------------------------------------------------------
-- Signed Laurent coefficient carrier.
------------------------------------------------------------------------

FormalLaurentQSeries : Set
FormalLaurentQSeries = ℤ → ℤ

------------------------------------------------------------------------
-- Coefficient-selection U_N.
------------------------------------------------------------------------

UN : Nat → FormalLaurentQSeries → FormalLaurentQSeries
UN N f n = f ((+ N) *ℤ n)

unCoefficient :
  (N : Nat) → (f : FormalLaurentQSeries) → (n : ℤ) →
  UN N f n ≡ f ((+ N) *ℤ n)
unCoefficient N f n = refl

uOneIdentityAt :
  (f : FormalLaurentQSeries) → (n : ℤ) →
  UN 1 f n ≡ f n
uOneIdentityAt f n = cong f (ℤRing.solve (n ∷ []))

uCompositionAt :
  (M N : Nat) → (f : FormalLaurentQSeries) → (n : ℤ) →
  UN M (UN N f) n ≡ UN (N * M) f n
uCompositionAt M N f n =
  cong f (ℤRing.solve ((+ N) ∷ (+ M) ∷ n ∷ []))

uCompositionCommutesAt :
  (M N : Nat) → (f : FormalLaurentQSeries) → (n : ℤ) →
  UN M (UN N f) n ≡ UN N (UN M f) n
uCompositionCommutesAt M N f n =
  trans
    (uCompositionAt M N f n)
    (sym (uCompositionAt N M f n))

------------------------------------------------------------------------
-- Normalized Hauptmodul principal-part observations.
------------------------------------------------------------------------

minusOne : ℤ
minusOne = -[1+ 0 ]

zeroIndex : ℤ
zeroIndex = + 0

oneIndex : ℤ
oneIndex = + 1

record NormalizedPrincipalPart (f : FormalLaurentQSeries) : Set where
  field
    coefficientMinusOne : f minusOne ≡ + 1
    constantCoefficient : f zeroIndex ≡ + 0

open NormalizedPrincipalPart public

------------------------------------------------------------------------
-- U_N moves the source coefficient at -N onto output coefficient -1.
-- This is exactly why a level-lowered modular function can acquire/read a
-- principal part from a deeper negative source coefficient.
------------------------------------------------------------------------

uNMinusOneReadsMinusN :
  (N : Nat) → (f : FormalLaurentQSeries) →
  UN N f minusOne ≡ f (-[1+ (N - 1) ])
uNMinusOneReadsMinusN 0 f = refl
uNMinusOneReadsMinusN (suc N) f =
  cong f (ℤRing.solve ((+ (suc N)) ∷ []))

------------------------------------------------------------------------
-- Same coefficientwise-equality discipline as the Nat-indexed operator.
------------------------------------------------------------------------

uPointwiseCong :
  (N : Nat) → (f g : FormalLaurentQSeries) →
  ((n : ℤ) → f n ≡ g n) →
  (n : ℤ) → UN N f n ≡ UN N g n
uPointwiseCong N f g pointwise n = pointwise ((+ N) *ℤ n)

record FormalLaurentQSeriesUNBoundary : Set where
  field
    signedLaurentCarrierConstructed : Bool
    principalPartMinusOneRepresentable : Bool
    signedUNCoefficientSelectionConstructed : Bool
    compositionProvedCoefficientwise : Bool
    normalizedPrincipalPartObserverConstructed : Bool
    NatIndexedOldformCarrierReusedAsModularFunctionCarrier : Bool
    analyticModularityProvedHere : Bool

canonicalFormalLaurentQSeriesUNBoundary : FormalLaurentQSeriesUNBoundary
canonicalFormalLaurentQSeriesUNBoundary = record
  { signedLaurentCarrierConstructed = true
  ; principalPartMinusOneRepresentable = true
  ; signedUNCoefficientSelectionConstructed = true
  ; compositionProvedCoefficientwise = true
  ; normalizedPrincipalPartObserverConstructed = true
  ; NatIndexedOldformCarrierReusedAsModularFunctionCarrier = false
  ; analyticModularityProvedHere = false
  }
