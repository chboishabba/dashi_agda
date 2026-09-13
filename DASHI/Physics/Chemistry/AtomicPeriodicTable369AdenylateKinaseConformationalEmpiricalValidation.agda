module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalValidation where

open import DASHI.Core.Prelude

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as A

------------------------------------------------------------------------
-- RED/GREEN validation root for the first same-sequence protein structural
-- pair.  This owner must remain distinct from generic protein-conformation
-- possibility: the pair is paid by specific PDB / primary-source receipts.
------------------------------------------------------------------------

identityRegression :
  A.AdenylateKinaseEmpiricalBoundary.samePolypeptideSequence
    A.canonicalAdenylateKinaseEmpiricalBoundary
  ≡ true
  × A.AdenylateKinaseEmpiricalBoundary.openClosedStructuralPairPaid
    A.canonicalAdenylateKinaseEmpiricalBoundary
  ≡ true
identityRegression = refl , refl

nonfactorabilityRegression :
  A.AdenylateKinaseEmpiricalBoundary.conformationFactorsThroughSequenceAlone
    A.canonicalAdenylateKinaseEmpiricalBoundary
  ≡ false
  × A.AdenylateKinaseEmpiricalBoundary.environmentContextRequired
    A.canonicalAdenylateKinaseEmpiricalBoundary
  ≡ true
nonfactorabilityRegression = refl , refl

promotionRegression :
  A.AdenylateKinaseEmpiricalBoundary.twoPDBEntriesProveUniversalFoldingMechanism
    A.canonicalAdenylateKinaseEmpiricalBoundary
  ≡ false
promotionRegression = refl
