module DASHI.Physics.Foundations.BalabanR144SpatialC3CovarianceCompilerValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Foundations.BalabanR144SpatialC3CovarianceCompilerExact as C3Compiler

-- RED-first contract: spatial C3 covariance must be a theorem compiled from
-- the already-canonical R144 B4 covariance witness, not another physical leaf.

spatialC3CompilesFromCanonicalB4 :
  C3Compiler.spatialC3CovarianceCompilesFromCanonicalB4 ≡ true
spatialC3CompilesFromCanonicalB4 = refl

noIndependentSpatialC3PhysicalReceipt :
  C3Compiler.independentSpatialC3PhysicalReceiptRequired ≡ false
noIndependentSpatialC3PhysicalReceipt = refl

preferredA1LeafCountUnchanged :
  C3Compiler.spatialC3AddsAnotherTerminalA1Leaf ≡ false
preferredA1LeafCountUnchanged = refl
