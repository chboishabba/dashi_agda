module DASHI.Physics.Closure.NSTriadKNConcreteNonResidualActualRelation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Unit using (⊤)

import DASHI.Physics.Closure.NSTriadKNConcretePairIncidenceKernelAdapter as Adapter
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Concrete non-residual relation as an actual rectangular relation view.
--
-- This removes the arbitrary relation-data input for the three available
-- concrete families.  It does not add the missing residual contribution or
-- identify this count-only relation with the physical amplitude kernel.
------------------------------------------------------------------------

concreteNonResidualActualRelationData :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (shellIndex : Nat) →
  Relation.ActualPairIncidenceRelationData
    residueNormModel shellIndex
concreteNonResidualActualRelationData residueNormModel shellIndex =
  Relation.mkActualPairIncidenceRelationData
    (Relation.ConcreteNonResidualFiniteIndex shellIndex)
    (Relation.ConcreteNonResidualTailIndex shellIndex)
    (Relation.ConcreteNonResidualTriadIncidence shellIndex)
    Relation.concreteNonResidualSourceIndex
    Relation.concreteNonResidualTargetIndex
    Relation.concreteNonResidualRetainedPositiveSector
    Relation.concreteNonResidualPairIncidenceCount
    ⊤

concreteNonResidualActualRelationDataKernelAgreement :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) →
  (t : Relation.ConcreteNonResidualTailIndex shellIndex) →
  Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
    (concreteNonResidualActualRelationData
      residueNormModel shellIndex)
    f t
  ≡ Relation.concreteNonResidualPairIncidenceCount f t
concreteNonResidualActualRelationDataKernelAgreement _ _ = refl

------------------------------------------------------------------------
-- The corresponding rectangular kernel view.  The view is count-based;
-- weighted physical amplitudes still enter only through the later scalar
-- retained-fiber bridge.
------------------------------------------------------------------------

concreteNonResidualActualBipartiteKernelView :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (shellIndex : Nat) →
  Adapter.ActualBipartiteKernelView residueNormModel shellIndex
concreteNonResidualActualBipartiteKernelView residueNormModel shellIndex =
  Adapter.mkActualBipartiteKernelView
    (concreteNonResidualActualRelationData residueNormModel shellIndex)
    Adapter.finiteProfile
    Adapter.tailProfile

concreteNonResidualActualBipartiteKernelViewKernelAgreement :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  (f : Relation.ConcreteNonResidualFiniteIndex shellIndex) →
  (t : Relation.ConcreteNonResidualTailIndex shellIndex) →
  Adapter.actualRelationKernel
    (concreteNonResidualActualBipartiteKernelView
      residueNormModel shellIndex)
    f t
  ≡ Relation.concreteNonResidualPairIncidenceCount f t
concreteNonResidualActualBipartiteKernelViewKernelAgreement _ _ = refl
