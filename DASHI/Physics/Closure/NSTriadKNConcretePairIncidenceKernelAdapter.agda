module DASHI.Physics.Closure.NSTriadKNConcretePairIncidenceKernelAdapter where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; zero)
open import Data.Unit using (⊤)

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile
import DASHI.Physics.Closure.NSTriadKNConcreteActualRetainedFiber as RetainedFiber

------------------------------------------------------------------------
-- Concrete bipartite kernel adapter.
--
-- The primitive relation is rectangular: a finite head is paired with a
-- tail column.  This adapter preserves that shape instead of silently
-- coercing both sides to the old Nat placeholder kernel.

finiteProfile :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex shellIndex ->
  Profile.PairIncidenceProfile
finiteProfile (Relation.forcedTailFiniteIndex _ _) =
  Profile.forcedTailProfile
finiteProfile (Relation.adversarialFiniteIndex _ _) =
  Profile.adversarialGeometryProfile
finiteProfile (Relation.transitionFiniteIndex _ _) =
  Profile.transitionProfile

tailProfile :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualTailIndex shellIndex ->
  Profile.PairIncidenceProfile
tailProfile (Relation.forcedTailTailIndex _ _) =
  Profile.forcedTailProfile
tailProfile (Relation.adversarialTailIndex _ _) =
  Profile.adversarialGeometryProfile
tailProfile (Relation.transitionTailIndex _ _) =
  Profile.transitionProfile

data ConcreteKernelProfileKey : Set where
  forcedTailKey : ConcreteKernelProfileKey
  adversarialKey : ConcreteKernelProfileKey
  transitionKey : ConcreteKernelProfileKey

finiteKey :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex shellIndex ->
  ConcreteKernelProfileKey
finiteKey (Relation.forcedTailFiniteIndex _ _) = forcedTailKey
finiteKey (Relation.adversarialFiniteIndex _ _) = adversarialKey
finiteKey (Relation.transitionFiniteIndex _ _) = transitionKey

tailKey :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualTailIndex shellIndex ->
  ConcreteKernelProfileKey
tailKey (Relation.forcedTailTailIndex _ _) = forcedTailKey
tailKey (Relation.adversarialTailIndex _ _) = adversarialKey
tailKey (Relation.transitionTailIndex _ _) = transitionKey

concretePairProfile :
  {shellIndex : Nat} ->
  Relation.ConcreteNonResidualFiniteIndex shellIndex ->
  Relation.ConcreteNonResidualTailIndex shellIndex ->
  Profile.PairIncidenceProfile
concretePairProfile f t with finiteKey f | tailKey t
... | forcedTailKey | forcedTailKey = Profile.forcedTailProfile
... | adversarialKey | adversarialKey =
  Profile.adversarialGeometryProfile
... | transitionKey | transitionKey = Profile.transitionProfile
... | _ | _ = Profile.residualProfile

record ConcreteBipartiteKernelAdapter
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkConcreteBipartiteKernelAdapter
  field
    FiniteIndex : Set
    TailIndex : Set

    actualKernel : FiniteIndex -> TailIndex -> Nat

    sourceProfile : FiniteIndex -> Profile.PairIncidenceProfile
    targetProfile : TailIndex -> Profile.PairIncidenceProfile

    retainedPositiveSector : Set

    kernelIsConcretePairIncidenceCount : Set
    profileClassification : Set
    residualContributionRoute : Set

open ConcreteBipartiteKernelAdapter public

------------------------------------------------------------------------
-- Actual-relation kernel view.
--
-- This is deliberately separate from the legacy concrete adapter below.
-- The legacy adapter is backed by the diagonal non-residual count.  This view
-- takes the repeated-pair count from ActualPairIncidenceRelationData directly,
-- so a future retained-sector construction can enter the rectangular lane
-- without being coerced through the placeholder kernel.
------------------------------------------------------------------------

record ActualBipartiteKernelView
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkActualBipartiteKernelView
  field
    relationData :
      Relation.ActualPairIncidenceRelationData residueNormModel shellIndex

    sourceProfile :
      Relation.ActualPairIncidenceRelationData.FiniteIndex relationData ->
      Profile.PairIncidenceProfile

    targetProfile :
      Relation.ActualPairIncidenceRelationData.TailIndex relationData ->
      Profile.PairIncidenceProfile

open ActualBipartiteKernelView public

actualRelationKernel :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (view : ActualBipartiteKernelView residueNormModel shellIndex) ->
  Relation.ActualPairIncidenceRelationData.FiniteIndex
    (ActualBipartiteKernelView.relationData view) ->
  Relation.ActualPairIncidenceRelationData.TailIndex
    (ActualBipartiteKernelView.relationData view) -> Nat
actualRelationKernel view =
  Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
    (ActualBipartiteKernelView.relationData view)

actualRelationKernelAgreesWithRepeatedCount :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (view : ActualBipartiteKernelView residueNormModel shellIndex) ->
  (f : Relation.ActualPairIncidenceRelationData.FiniteIndex
    (ActualBipartiteKernelView.relationData view)) ->
  (t : Relation.ActualPairIncidenceRelationData.TailIndex
    (ActualBipartiteKernelView.relationData view)) ->
  actualRelationKernel view f t ≡
  Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
    (ActualBipartiteKernelView.relationData view) f t
actualRelationKernelAgreesWithRepeatedCount _ _ _ = refl

------------------------------------------------------------------------
-- Generic actual-kernel adapter.
--
-- The physical formula and the actual relation may use different finite and
-- tail index types.  The retained-fiber interface supplies the projections
-- between those types and the only permitted formula-to-relation agreement.
-- This record therefore carries the missing inputs without constructing any
-- physical formula or reusing the diagonal proxy.
------------------------------------------------------------------------

record ActualPairIncidenceKernelAdapterTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₂ where
  constructor mkActualPairIncidenceKernelAdapterTarget
  field
    relationData :
      Relation.ActualPairIncidenceRelationData residueNormModel shellIndex

    physicalFormula :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget
        residueNormModel shellIndex

    retainedFiberAgreement :
      RetainedFiber.ConcreteActualRetainedFiberInterface
        relationData physicalFormula

    sourceProfile :
      Relation.ActualPairIncidenceRelationData.FiniteIndex relationData ->
      Profile.PairIncidenceProfile

    targetProfile :
      Relation.ActualPairIncidenceRelationData.TailIndex relationData ->
      Profile.PairIncidenceProfile

open ActualPairIncidenceKernelAdapterTarget public

actualFiniteIndexProjection :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target) ->
  Relation.ActualPairIncidenceRelationData.FiniteIndex
    (ActualPairIncidenceKernelAdapterTarget.relationData target)
actualFiniteIndexProjection target f =
  RetainedFiber.ConcreteActualRetainedFiberInterface.sourceProjection
    (ActualPairIncidenceKernelAdapterTarget.retainedFiberAgreement target)
    f

actualTailIndexProjection :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target) ->
  Relation.ActualPairIncidenceRelationData.TailIndex
    (ActualPairIncidenceKernelAdapterTarget.relationData target)
actualTailIndexProjection target t =
  RetainedFiber.ConcreteActualRetainedFiberInterface.targetProjection
    (ActualPairIncidenceKernelAdapterTarget.retainedFiberAgreement target)
    t

actualBipartiteKernelViewFromFormulaTarget :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  ActualBipartiteKernelView residueNormModel shellIndex
actualBipartiteKernelViewFromFormulaTarget target =
  mkActualBipartiteKernelView
    (ActualPairIncidenceKernelAdapterTarget.relationData target)
    (ActualPairIncidenceKernelAdapterTarget.sourceProfile target)
    (ActualPairIncidenceKernelAdapterTarget.targetProfile target)

actualKernelAgreesWithViewKernel :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target)) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target)) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target) f t ≡
  actualRelationKernel
    (actualBipartiteKernelViewFromFormulaTarget target)
    (actualFiniteIndexProjection target f)
    (actualTailIndexProjection target t)
actualKernelAgreesWithViewKernel target f t =
  RetainedFiber.actualKernelAgreesWithRelationCount
    (ActualPairIncidenceKernelAdapterTarget.retainedFiberAgreement target)
    f t

actualKernelViewAgreement :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  Set
actualKernelViewAgreement target =
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target)) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target)) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    (ActualPairIncidenceKernelAdapterTarget.physicalFormula target) f t ≡
  actualRelationKernel
    (actualBipartiteKernelViewFromFormulaTarget target)
    (actualFiniteIndexProjection target f)
    (actualTailIndexProjection target t)

actualViewKernelAgreesWithRepeatedCount :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : ActualPairIncidenceKernelAdapterTarget
    residueNormModel shellIndex) ->
  (f : Relation.ActualPairIncidenceRelationData.FiniteIndex
    (ActualPairIncidenceKernelAdapterTarget.relationData target)) ->
  (t : Relation.ActualPairIncidenceRelationData.TailIndex
    (ActualPairIncidenceKernelAdapterTarget.relationData target)) ->
  actualRelationKernel (actualBipartiteKernelViewFromFormulaTarget target) f t ≡
  Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
    (ActualPairIncidenceKernelAdapterTarget.relationData target) f t
actualViewKernelAgreesWithRepeatedCount target f t =
  actualRelationKernelAgreesWithRepeatedCount
    (actualBipartiteKernelViewFromFormulaTarget target) f t

UnitShellConcreteBipartiteKernelAdapterTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) -> Set₁
UnitShellConcreteBipartiteKernelAdapterTarget residueNormModel =
  ConcreteBipartiteKernelAdapter residueNormModel (suc zero)

canonicalConcreteBipartiteKernelAdapter :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  UnitShellConcreteBipartiteKernelAdapterTarget residueNormModel
canonicalConcreteBipartiteKernelAdapter residueNormModel =
  mkConcreteBipartiteKernelAdapter
    (Relation.ConcreteNonResidualFiniteIndex (suc zero))
    (Relation.ConcreteNonResidualTailIndex (suc zero))
    Relation.concreteNonResidualPairIncidenceCount
    finiteProfile
    tailProfile
    ⊤
    ((f : Relation.ConcreteNonResidualFiniteIndex (suc zero)) ->
     (t : Relation.ConcreteNonResidualTailIndex (suc zero)) ->
       Relation.concreteNonResidualPairIncidenceCount f t
         ≡ Relation.concreteNonResidualPairIncidenceCount f t)
    ((f : Relation.ConcreteNonResidualFiniteIndex (suc zero)) ->
       (t : Relation.ConcreteNonResidualTailIndex (suc zero)) ->
       concretePairProfile f t ≡ concretePairProfile f t)
    (Relation.actualPairIncidenceRelationDataClosed ≡ true)

canonicalConcreteKernelCountAgreement :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  (f : Relation.ConcreteNonResidualFiniteIndex (suc zero)) ->
  (t : Relation.ConcreteNonResidualTailIndex (suc zero)) ->
  ConcreteBipartiteKernelAdapter.actualKernel
      (canonicalConcreteBipartiteKernelAdapter residueNormModel) f t
    ≡ Relation.concreteNonResidualPairIncidenceCount f t
canonicalConcreteKernelCountAgreement _ _ _ = refl

------------------------------------------------------------------------
-- The remaining square-kernel adapter is explicit and fail-closed.
--
-- Existing ProfileCrossMatrixKernelData requires one homogeneous index type
-- and the old Nat-entry profile model.  The fields below state exactly what
-- must be supplied before the concrete bipartite kernel can replace that
-- model: a common index, entry map, kernel agreement, and classifier
-- agreement.  No postulate or status receipt is used here.

record HomogeneousProfileKernelAdapterTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkHomogeneousProfileKernelAdapterTarget
  field
    Index : Set

    finiteOf :
      Index ->
      Relation.ConcreteNonResidualFiniteIndex shellIndex

    tailOf :
      Index ->
      Relation.ConcreteNonResidualTailIndex shellIndex

    entryOf :
      Index ->
      Profile.Entry Profile.canonicalNSProfileDecompositionModel

    homogeneousKernel : Index -> Index -> Nat

    kernelAgreement :
      (i j : Index) ->
      homogeneousKernel i j
        ≡ Relation.concreteNonResidualPairIncidenceCount
            (finiteOf i) (tailOf j)

    classifierAgreement :
      (i j : Index) ->
      Profile.profileClassifier
        Profile.canonicalNSProfileDecompositionModel
        shellIndex
        (entryOf i) (entryOf j)
        ≡ concretePairProfile (finiteOf i) (tailOf j)

UnitShellHomogeneousProfileKernelAdapterTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) -> Set₁
UnitShellHomogeneousProfileKernelAdapterTarget residueNormModel =
  HomogeneousProfileKernelAdapterTarget residueNormModel (suc zero)

concreteBipartiteKernelAdapterClosed : Bool
concreteBipartiteKernelAdapterClosed = true

concreteBipartiteKernelAdapterClosedIsTrue :
  concreteBipartiteKernelAdapterClosed ≡ true
concreteBipartiteKernelAdapterClosedIsTrue = refl

homogeneousProfileKernelAdapterClosed : Bool
homogeneousProfileKernelAdapterClosed = false

homogeneousProfileKernelAdapterClosedIsFalse :
  homogeneousProfileKernelAdapterClosed ≡ false
homogeneousProfileKernelAdapterClosedIsFalse = refl
