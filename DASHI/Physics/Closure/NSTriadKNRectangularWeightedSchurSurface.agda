module DASHI.Physics.Closure.NSTriadKNRectangularWeightedSchurSurface where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_≤_; _*_
                            )

import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
import DASHI.Physics.Closure.NSTriadKNConcretePairIncidenceKernelAdapter as Concrete
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition as Profile

------------------------------------------------------------------------
-- Rectangular kernel surface.
--
-- The finite and tail index sets are intentionally distinct.  This is the
-- correct shape for a pair-incidence kernel K : FiniteIndex -> TailIndex ->
-- Nat and is the input required by a genuine row/column Schur argument.

record RectangularKernelData
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkRectangularKernelData
  field
    FiniteIndex : Set
    TailIndex : Set

    kernel : FiniteIndex -> TailIndex -> Nat

    sourceProfile : FiniteIndex -> Profile.PairIncidenceProfile
    targetProfile : TailIndex -> Profile.PairIncidenceProfile

    kernelIsConcretePairIncidenceCount : Set
    profileClassification : Set
    residualContributionRoute : Set

open RectangularKernelData public

RectangularKernelDataTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) -> Set₁
RectangularKernelDataTarget residueNormModel =
  RectangularKernelData residueNormModel 1

rectangularKernelDataFromConcreteAdapter :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  Concrete.ConcreteBipartiteKernelAdapter residueNormModel shellIndex ->
  RectangularKernelData residueNormModel shellIndex
rectangularKernelDataFromConcreteAdapter adapter =
  mkRectangularKernelData
    (Concrete.ConcreteBipartiteKernelAdapter.FiniteIndex adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.TailIndex adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.actualKernel adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.sourceProfile adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.targetProfile adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.kernelIsConcretePairIncidenceCount
      adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.profileClassification adapter)
    (Concrete.ConcreteBipartiteKernelAdapter.residualContributionRoute adapter)

------------------------------------------------------------------------
-- Actual-relation rectangular bridge.
--
-- Unlike the canonical adapter above, this bridge derives the kernel from an
-- ActualPairIncidenceRelationData view.  The three evidence arguments remain
-- explicit because the rectangular surface still has legacy Set-valued
-- metadata fields; no canonical evidence is fabricated here.
------------------------------------------------------------------------

actualRectangularKernelDataFromView :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (view : Concrete.ActualBipartiteKernelView residueNormModel shellIndex) ->
  (kernelEvidence : Set) ->
  (profileEvidence : Set) ->
  (residualRoute : Set) ->
  RectangularKernelData residueNormModel shellIndex
actualRectangularKernelDataFromView
  {shellIndex = shellIndex}
  view kernelEvidence profileEvidence residualRoute =
  mkRectangularKernelData
    (Relation.ActualPairIncidenceRelationData.FiniteIndex
      (Concrete.ActualBipartiteKernelView.relationData view))
    (Relation.ActualPairIncidenceRelationData.TailIndex
      (Concrete.ActualBipartiteKernelView.relationData view))
    (Concrete.actualRelationKernel view)
    (Concrete.ActualBipartiteKernelView.sourceProfile view)
    (Concrete.ActualBipartiteKernelView.targetProfile view)
    kernelEvidence
    profileEvidence
    residualRoute

actualRectangularKernelDataFromFormulaTargetWithEvidence :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target :
    Concrete.ActualPairIncidenceKernelAdapterTarget
      residueNormModel shellIndex) ->
  (kernelEvidence : Set) ->
  (profileEvidence : Set) ->
  (residualRoute : Set) ->
  RectangularKernelData residueNormModel shellIndex
actualRectangularKernelDataFromFormulaTargetWithEvidence
  target kernelEvidence profileEvidence residualRoute =
  actualRectangularKernelDataFromView
    (Concrete.actualBipartiteKernelViewFromFormulaTarget target)
    kernelEvidence
    profileEvidence
    residualRoute

actualRectangularKernelDataFromFormulaTarget :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target :
    Concrete.ActualPairIncidenceKernelAdapterTarget
      residueNormModel shellIndex) ->
  (profileEvidence : Set) ->
  (residualRoute : Set) ->
  RectangularKernelData residueNormModel shellIndex
actualRectangularKernelDataFromFormulaTarget
  target profileEvidence residualRoute =
  actualRectangularKernelDataFromFormulaTargetWithEvidence
    target
    (Concrete.actualKernelViewAgreement target)
    profileEvidence
    residualRoute

actualRectangularKernelAgreesWithPhysicalFormula :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target :
    Concrete.ActualPairIncidenceKernelAdapterTarget
      residueNormModel shellIndex) ->
  (profileEvidence : Set) ->
  (residualRoute : Set) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    (Concrete.ActualPairIncidenceKernelAdapterTarget.physicalFormula
      target)) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    (Concrete.ActualPairIncidenceKernelAdapterTarget.physicalFormula
      target)) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    (Concrete.ActualPairIncidenceKernelAdapterTarget.physicalFormula target)
    f t ≡
  RectangularKernelData.kernel
    (actualRectangularKernelDataFromFormulaTarget
      target profileEvidence residualRoute)
    (Concrete.actualFiniteIndexProjection target f)
    (Concrete.actualTailIndexProjection target t)
actualRectangularKernelAgreesWithPhysicalFormula target
  profileEvidence residualRoute f t =
  Concrete.actualKernelAgreesWithViewKernel target f t

canonicalRectangularKernelData :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  RectangularKernelDataTarget residueNormModel
canonicalRectangularKernelData residueNormModel =
  rectangularKernelDataFromConcreteAdapter
    (Concrete.canonicalConcreteBipartiteKernelAdapter residueNormModel)

------------------------------------------------------------------------
-- Actual Schur theorem target.
--
-- These fields are deliberately quantitative.  No default row/column values
-- are supplied: the target cannot close until the concrete weighted sums and
-- the operator/quadratic-form bridge are proved.

record RectangularWeightedSchurBoundTarget
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkRectangularWeightedSchurBoundTarget
  field
    kernelData : RectangularKernelData residueNormModel shellIndex

    sourceWeight :
      RectangularKernelData.FiniteIndex kernelData -> Nat

    targetWeight :
      RectangularKernelData.TailIndex kernelData -> Nat

    rowBound : Nat
    columnBound : Nat
    productTarget : Nat

    rowContributionCandidate :
      RectangularKernelData.FiniteIndex kernelData -> Nat

    columnContributionCandidate :
      RectangularKernelData.TailIndex kernelData -> Nat

    weightedRowBound :
      (i : RectangularKernelData.FiniteIndex kernelData) ->
      rowContributionCandidate i ≤ rowBound

    weightedColumnBound :
      (j : RectangularKernelData.TailIndex kernelData) ->
      columnContributionCandidate j ≤ columnBound

    weightedProductBound : rowBound * columnBound ≤ productTarget

    operatorNormBound : Set
    quadraticFormBound : Set

open RectangularWeightedSchurBoundTarget public

RectangularWeightedSchurBoundTargetAtUnitShell :
  (residueNormModel : ResidueNorm.ResidueNormModel) -> Set₁
RectangularWeightedSchurBoundTargetAtUnitShell residueNormModel =
  RectangularWeightedSchurBoundTarget residueNormModel 1

------------------------------------------------------------------------
-- The boundary is now machine-readable: the concrete rectangular kernel is
-- closed, while the analytic Schur/operator target remains open.

rectangularKernelDataClosed : Bool
rectangularKernelDataClosed = true

rectangularKernelDataClosedIsTrue : rectangularKernelDataClosed ≡ true
rectangularKernelDataClosedIsTrue = refl

rectangularWeightedSchurBoundClosed : Bool
rectangularWeightedSchurBoundClosed = false

rectangularWeightedSchurBoundClosedIsFalse :
  rectangularWeightedSchurBoundClosed ≡ false
rectangularWeightedSchurBoundClosedIsFalse = refl
