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
-- All operator equalities are deliberately stated COEFFICIENTWISE.  This is
-- the native observation consumed by the source argument and avoids importing
-- function extensionality merely to package pointwise equal q-series.
--
-- This file proves only coefficient algebra:
--
--   (U_N f)_n = f_{Nn},
--   U_M U_N = U_{NM} coefficientwise,
--   U_1 = id coefficientwise,
--   coefficientwise equality is preserved,
--   every U_N coefficient has an explicit N-multiple source index.
--
-- It deliberately does NOT claim the analytic/modular theorem that U_p lowers
-- a specified modular-function level.  That source-facing theorem is isolated
-- separately.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
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
-- Identity and composition, coefficientwise.
------------------------------------------------------------------------

uOneIdentityAt :
  (f : Q.FormalQSeries) → (n : Nat) → UN 1 f n ≡ f n
uOneIdentityAt f n = cong f (NatP.*-identityˡ n)

uCompositionAt :
  (M N : Nat) → (f : Q.FormalQSeries) → (n : Nat) →
  UN M (UN N f) n ≡ UN (N * M) f n
uCompositionAt M N f n =
  cong f (sym (NatP.*-assoc N M n))

uCompositionCommutesOnIndicesAt :
  (M N : Nat) → (f : Q.FormalQSeries) → (n : Nat) →
  UN M (UN N f) n ≡ UN N (UN M f) n
uCompositionCommutesOnIndicesAt M N f n =
  trans
    (uCompositionAt M N f n)
    (trans
      (cong (λ k → f (k * n)) (NatP.*-comm N M))
      (sym (uCompositionAt N M f n)))

------------------------------------------------------------------------
-- Equality transport.
------------------------------------------------------------------------

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
    uOneIdentityProvedCoefficientwise : Bool
    compositionProvedCoefficientwise : Bool
    commutingIndexSelectionsProvedCoefficientwise : Bool
    coefficientOriginProved : Bool
    functionExtensionalityImported : Bool
    modularFunctionLevelLoweringProvedHere : Bool
    etaOrHauptmodulAnalyticObjectConstructedHere : Bool

canonicalFormalQSeriesUNBoundary : FormalQSeriesUNBoundary
canonicalFormalQSeriesUNBoundary = record
  { coefficientSelectionConstructed = true
  ; uOneIdentityProvedCoefficientwise = true
  ; compositionProvedCoefficientwise = true
  ; commutingIndexSelectionsProvedCoefficientwise = true
  ; coefficientOriginProved = true
  ; functionExtensionalityImported = false
  ; modularFunctionLevelLoweringProvedHere = false
  ; etaOrHauptmodulAnalyticObjectConstructedHere = false
  }
