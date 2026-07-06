module DASHI.Physics.Closure.NSTriadKNAdversarialClosureDependency where

open import Agda.Builtin.Bool using (Bool)

open import DASHI.Physics.Closure.NSTriadKNAdversarialRowClosureDependency
  as RowDependency
  using (adversarialRowN2BoundAvailable)
open import DASHI.Physics.Closure.NSTriadKNAdversarialColumnClosureDependency
  as ColumnDependency
  using (adversarialColumnN1BoundAvailable)
open import DASHI.Physics.Closure.NSTriadKNAdversarialWeightedProductBridge
  as WeightedBridge
  using ( adversarialWeightedProductFromRowColumnAvailable
        )

------------------------------------------------------------------------
-- Adversarial closure-dependency placeholder.
--
-- This module names the proof authority chain the adversarial lane will need:
--
--   adversarialRowN2Bound
--     ↓
--   adversarialColumnN1Bound
--     ↓
--   adversarialWeightedProductFromRowColumn
--     ↓
--   adversarialWeightedProductBoundClosed
--
-- Unlike forced-tail, none of these are inhabited yet.

record NSTriadKNAdversarialClosureDependency : Set where
  field
    rowN2BoundAvailable : Bool
    columnN1BoundAvailable : Bool
    weightedProductAvailable : Bool

open NSTriadKNAdversarialClosureDependency public

currentNSTriadKNAdversarialClosureDependency :
  NSTriadKNAdversarialClosureDependency
currentNSTriadKNAdversarialClosureDependency = record
  { rowN2BoundAvailable = adversarialRowN2BoundAvailable
  ; columnN1BoundAvailable = adversarialColumnN1BoundAvailable
  ; weightedProductAvailable = adversarialWeightedProductFromRowColumnAvailable
  }

adversarialWeightedProductBoundClosed : Bool
adversarialWeightedProductBoundClosed =
  adversarialWeightedProductFromRowColumnAvailable
