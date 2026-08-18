module DASHI.Moonshine.FormalQSeriesUNLevelLoweringExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135 (2026).
-- DOI: 10.48550/arXiv.2602.09135.
--
-- Their coefficient-normalized U_N operator satisfies
--
--   c_n(f | U_N) = c_{nN}(f).
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", GTM 228, Springer, 2005.
-- DOI: 10.1007/978-0-387-27226-9.
-- Classical q-expansion operator context.
--
-- DASHI CONTRIBUTION
--
-- Construct the exact FORMAL q-series coefficient-selection operator on the
-- repository's existing carrier
--
--   FormalQSeries = Nat -> Z.
--
-- This file proves only coefficient algebra:
--
--   (U_N f)_n = f_{Nn},
--   U_M U_N = U_{NM},
--   U_1 = id,
--   U_N preserves coefficientwise equality,
--   U_N sends support to the N-divisible subsequence.
--
-- It deliberately does NOT claim the analytic/modular theorem that U_p lowers
-- a specified modular-function level.  That source-facing theorem is isolated
-- in DuncanSwisherUNModularLevelAuthorityExact.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Integer using (ℤ)
open import Data.Nat using (_*_)
import Data.Nat.Properties as NatP

import DASHI.Moonshine.FormalQSeriesOldformDegeneracyHeckeExact as Q

------------------------------------------------------------------------
-- Exact coefficient-selection operator.
------------------------------------------------------------------------

UN : Nat → Q.FormalQSeries → Q.FormalQSeries
UN N f n = f (N * n)

unCoefficient :
  (N : Nat) → (f : Q.FormalQSeries) → (n : Nat) →
  UN N f n ≡ f (N * n)
unCoefficient N f n = refl

------------------------------------------------------------------------
-- Extensional equality helper for formal q-series.
------------------------------------------------------------------------

seriesExt :
  (f g : Q.FormalQSeries) →
  ((n : Nat) → f n ≡ g n) →
  f ≡ g
seriesExt f g pointwise = funext pointwise

------------------------------------------------------------------------
-- Identity and composition.
------------------------------------------------------------------------

uOneIdentity :
  (f : Q.FormalQSeries) → UN 1 f ≡ f
uOneIdentity f =
  seriesExt (UN 1 f) f (λ n → cong f (NatP.*-identityˡ n))

uComposition :
  (M N : Nat) → (f : Q.FormalQSeries) →
  UN M (UN N f) ≡ UN (N * M) f
uComposition M N f =
  seriesExt (UN M (UN N f)) (UN (N * M) f)
    (λ n → cong f (sym (NatP.*-assoc N M n)))

uCompositionCommutesOnIndices :
  (M N : Nat) → (f : Q.FormalQSeries) →
  UN M (UN N f) ≡ UN N (UN M f)
uCompositionCommutesOnIndices M N f =
  trans
    (uComposition M N f)
    (trans
      (cong (λ k → UN k f) (NatP.*-comm N M))
      (sym (uComposition N M f)))

------------------------------------------------------------------------
-- Equality transport.
------------------------------------------------------------------------

uCong :
  (N : Nat) → {f g : Q.FormalQSeries} →
  f ≡ g → UN N f ≡ UN N g
uCong N equality = cong (UN N) equality

uPointwiseCong :
  (N : Nat) → (f g : Q.FormalQSeries) →
  ((n : Nat) → f n ≡ g n) →
  (n : Nat) → UN N f n ≡ UN N g n
uPointwiseCong N f g pointwise n = pointwise (N * n)

------------------------------------------------------------------------
-- Support readout.  U_N does not invent a coefficient: every output is the
-- source coefficient on the explicit N-multiple index.
------------------------------------------------------------------------

record UNCoefficientOrigin
    (N : Nat) (f : Q.FormalQSeries) (n : Nat) : Set where
  field
    sourceIndex : Nat
    sourceIndexIsNMultiple : sourceIndex ≡ N * n
    outputIsSourceCoefficient : UN N f n ≡ f sourceIndex

open UNCoefficientOrigin public

coefficientOrigin :
  (N : Nat) → (f : Q.FormalQSeries) → (n : Nat) →
  UNCoefficientOrigin N f n
coefficientOrigin N f n = record
  { sourceIndex = N * n
  ; sourceIndexIsNMultiple = refl
  ; outputIsSourceCoefficient = refl
  }

------------------------------------------------------------------------
-- Boundary: coefficient selection is constructed; modularity/level lowering is
-- intentionally a separate analytic theorem.
------------------------------------------------------------------------

record FormalQSeriesUNBoundary : Set where
  field
    coefficientSelectionConstructed : Bool
    uOneIdentityProved : Bool
    compositionProved : Bool
    commutingIndexSelectionsProved : Bool
    coefficientOriginProved : Bool
    modularFunctionLevelLoweringProvedHere : Bool
    etaOrHauptmodulAnalyticObjectConstructedHere : Bool

canonicalFormalQSeriesUNBoundary : FormalQSeriesUNBoundary
canonicalFormalQSeriesUNBoundary = record
  { coefficientSelectionConstructed = true
  ; uOneIdentityProved = true
  ; compositionProved = true
  ; commutingIndexSelectionsProved = true
  ; coefficientOriginProved = true
  ; modularFunctionLevelLoweringProvedHere = false
  ; etaOrHauptmodulAnalyticObjectConstructedHere = false
  }
