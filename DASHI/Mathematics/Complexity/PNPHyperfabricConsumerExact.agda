module DASHI.Mathematics.Complexity.PNPHyperfabricConsumerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Reasoning.HistoryTimeIndexedConsumerFibreExact as HT
import DASHI.Core.GovernedIndexedResidualCubeExact as Q

-- Specialization of the EXISTING history/time hyperfabric. No new residual
-- carrier, resolution or independent abstract proof architecture.
module Actual (X Time Key Decision Version : Set)
  (key : Time → X → Key)
  (consumer : Time → X → Decision)
  (version : Time → Version) where

  surface : HT.HistoryTimeConsumerFibreSurface
  surface = HT.historyTimeConsumerFibreSurface
    X Time X Decision Version
    (λ x t y → key t y ≡ key t x)
    (λ x t → consumer t)
    (λ x t → version t)
    "original same-key fibre" "actual consumer at epoch" "consumer version"

  -- The anchor is the history coordinate, the epoch is the time coordinate.
  preserves : (t : Time) → Set
  preserves t = ∀ x y → key t x ≡ key t y → consumer t x ≡ consumer t y

  closesAll : (t : Time) → Set
  closesAll t = ∀ x → HT.ConsumerClosedAt surface x t

  preservesToClosure : ∀ t → preserves t → closesAll t
  preservesToClosure t h x y z hy hz = h y z (trans hy (sym hz))

  closureToPreserves : ∀ t → closesAll t → preserves t
  closureToPreserves t h x y eq = h x x y refl (sym eq)

  obstruction : ∀ t x y → key t x ≡ key t y →
    (consumer t x ≡ consumer t y → ⊥) →
    HT.ConsumerClosedAt surface x t → ⊥
  obstruction t x y eq ne closed = ne (closed x y refl (sym eq))

  -- Same surface at each existing five-index cube coordinate. Cross-index
  -- consumer revision or commuting faces still require their own receipts.
  indexedClosure : ∀ {Depth Frob : Set} →
    Q.Index X Time Depth Frob Version → Set
  indexedClosure k = HT.ConsumerClosedAt surface (Q.Index.history k) (Q.Index.time k)

  indexedVersionAligned : ∀ {Depth Frob : Set} →
    Q.Index X Time Depth Frob Version → Set
  indexedVersionAligned k = Q.Index.version k ≡ version (Q.Index.time k)
