module DASHI.Physics.Chemistry.AtomicPeriodicTable369AlanineChiralEmpiricalValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AlanineChiralEmpiricalExact as A

------------------------------------------------------------------------
-- RED/GREEN validation root for the first real same-coarse chiral pair.
------------------------------------------------------------------------

identityRegression :
  A.AlanineChiralEmpiricalBoundary.sameMolecularFormula
    A.canonicalAlanineChiralEmpiricalBoundary
  ≡ true
  × A.AlanineChiralEmpiricalBoundary.enantiomerRelationPaid
    A.canonicalAlanineChiralEmpiricalBoundary
  ≡ true
identityRegression = refl , refl

opticalRegression :
  A.AlanineChiralEmpiricalBoundary.crystalOpticalRotationSeparatesEnantiomers
    A.canonicalAlanineChiralEmpiricalBoundary
  ≡ true
  × A.AlanineChiralEmpiricalBoundary.opticalRotationSignIndependentOfEnvironment
    A.canonicalAlanineChiralEmpiricalBoundary
  ≡ false
opticalRegression = refl , refl

promotionRegression :
  A.AlanineChiralEmpiricalBoundary.empiricalPairProvesUniversalChiralResponse
    A.canonicalAlanineChiralEmpiricalBoundary
  ≡ false
promotionRegression = refl
