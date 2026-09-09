module DASHI.GameTheory.FiniteMixedNashReceiptBindingExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.GameTheory.StrategicInteractionCoreExact as Game
import DASHI.GameTheory.FiniteMixedStrategyExpectedUtilityExact as Mixed
import DASHI.GameTheory.FiniteMixedNashProductCorrectionExact as Correction

------------------------------------------------------------------------
-- EXACT FINITE-NORMAL-FORM BINDING
--
-- Source alignment may name a particular finite player/strategy enumeration.
-- The resulting existence theorem must return an equilibrium for that exact
-- receipt, not merely an equilibrium carrying some unrelated finite receipt.
------------------------------------------------------------------------

record StandardFiniteMixedNashForReceipt
    (G : Game.StrategicGame)
    (U : Mixed.FiniteExpectedUtilitySurface G)
    (finiteReceipt : Correction.FiniteNormalFormReceipt G) : Set₁ where
  constructor standard-finite-mixed-nash-for-receipt
  field
    equilibrium : Correction.StandardFiniteMixedNashEquilibrium G U
    exactFiniteNormalForm :
      Correction.StandardFiniteMixedNashEquilibrium.finiteNormalForm equilibrium
      ≡ finiteReceipt

open StandardFiniteMixedNashForReceipt public

boundEquilibrium :
  ∀ {G U finiteReceipt} →
  StandardFiniteMixedNashForReceipt G U finiteReceipt →
  Correction.StandardFiniteMixedNashEquilibrium G U
boundEquilibrium = equilibrium

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data AnyFiniteReceiptMeansAlignedReceiptPermission : Set where

data ReceiptEqualityMeansEnumerationCanBeIgnoredPermission : Set where

arbitraryFiniteReceiptDoesNotPayAlignedReceipt :
  AnyFiniteReceiptMeansAlignedReceiptPermission → ⊥
arbitraryFiniteReceiptDoesNotPayAlignedReceipt ()

receiptBindingIsNotPermissionToIgnoreEnumeration :
  ReceiptEqualityMeansEnumerationCanBeIgnoredPermission → ⊥
receiptBindingIsNotPermissionToIgnoreEnumeration ()

record FiniteMixedNashReceiptBindingBoundary : Set where
  constructor finite-mixed-nash-receipt-binding-boundary
  field
    exactFiniteReceiptBound : Bool
    arbitraryReceiptAcceptedAsAligned : Bool
    equilibriumCarrierReused : Bool

canonicalFiniteMixedNashReceiptBindingBoundary : FiniteMixedNashReceiptBindingBoundary
canonicalFiniteMixedNashReceiptBindingBoundary =
  finite-mixed-nash-receipt-binding-boundary true false true
