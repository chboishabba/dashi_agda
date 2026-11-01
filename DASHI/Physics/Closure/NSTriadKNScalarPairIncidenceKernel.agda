module DASHI.Physics.Closure.NSTriadKNScalarPairIncidenceKernel where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Scalar-valued kernel surface.
--
-- The Nat-valued formula target is deliberately not reused as the scalar
-- kernel.  This surface lives on the exact finite carriers and takes its
-- aggregate from the scalar retained-triad fiber interface.
------------------------------------------------------------------------

record ScalarPairIncidenceKernelSurface
    {S : Exact.ExactScalarOperations}
    (surface : Exact.FiniteTriadModeSurface S)
    (profile : Exact.AdmissibleAmplitudeProfile surface)
    (SourceIndex TargetIndex : Exact.FiniteCarrier)
    (sourceIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex)
    (targetIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex)
    (retainedPositiveSector : Exact.TriadOf surface → Set)
    (fiberInterface :
      Exact.ExactRetainedTriadFiberInterface
        surface
        profile
        SourceIndex
        TargetIndex
        sourceIndex
        targetIndex
        retainedPositiveSector) : Setω where
  constructor mkScalarPairIncidenceKernelSurface
  field
    scalarKernel :
      Exact.FiniteCarrier.Carrier SourceIndex →
      Exact.FiniteCarrier.Carrier TargetIndex →
      Exact.ExactScalarOperations.Carrier S

    scalarKernelAgreesWithFiberAggregate :
      (f : Exact.FiniteCarrier.Carrier SourceIndex) →
      (t : Exact.FiniteCarrier.Carrier TargetIndex) →
      scalarKernel f t ≡
      Exact.ExactRetainedTriadFiberInterface.fiberAggregate
        fiberInterface f t

open ScalarPairIncidenceKernelSurface public

------------------------------------------------------------------------
-- The weighted-fiber normal form is a theorem of the scalar surface.  It
-- uses the exact interface's finite-sum law and does not assume Nat/scalar
-- addition compatibility.
------------------------------------------------------------------------

scalarKernelAgreesWithExactWeightedFiber :
  {S : Exact.ExactScalarOperations} →
  {surface : Exact.FiniteTriadModeSurface S} →
  {profile : Exact.AdmissibleAmplitudeProfile surface} →
  {SourceIndex TargetIndex : Exact.FiniteCarrier} →
  {sourceIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex} →
  {targetIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex} →
  {retainedPositiveSector : Exact.TriadOf surface → Set} →
  {fiberInterface :
    Exact.ExactRetainedTriadFiberInterface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector} →
  (kernelSurface :
    ScalarPairIncidenceKernelSurface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector
      fiberInterface) →
  (f : Exact.FiniteCarrier.Carrier SourceIndex) →
  (t : Exact.FiniteCarrier.Carrier TargetIndex) →
  scalarKernel kernelSurface f t ≡
  Exact.weightedListSum {S = S}
    (Exact.ExactRetainedTriadFiberInterface.triadWeight fiberInterface)
    (Exact.ExactRetainedTriadFiberInterface.fiber fiberInterface f t)
scalarKernelAgreesWithExactWeightedFiber
  {fiberInterface = fiberInterface} kernelSurface f t =
  trans
    (ScalarPairIncidenceKernelSurface.scalarKernelAgreesWithFiberAggregate
      kernelSurface f t)
    (Exact.ExactRetainedTriadFiberInterface.fiberAggregateIsFiniteWeightedSum
      fiberInterface f t)

------------------------------------------------------------------------
-- A canonical scalar representation can be formed only after an exact
-- retained-fiber interface has been supplied.  This is not a physical
-- inhabitant: the interface itself remains an explicit upstream input.
------------------------------------------------------------------------

scalarKernelSurfaceFromExactFiber :
  {S : Exact.ExactScalarOperations} →
  (surface : Exact.FiniteTriadModeSurface S) →
  (profile : Exact.AdmissibleAmplitudeProfile surface) →
  (SourceIndex TargetIndex : Exact.FiniteCarrier) →
  (sourceIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex) →
  (targetIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex) →
  (retainedPositiveSector : Exact.TriadOf surface → Set) →
  (fiberInterface :
    Exact.ExactRetainedTriadFiberInterface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector) →
  ScalarPairIncidenceKernelSurface
    surface
    profile
    SourceIndex
    TargetIndex
    sourceIndex
    targetIndex
    retainedPositiveSector
    fiberInterface
scalarKernelSurfaceFromExactFiber
  surface profile SourceIndex TargetIndex sourceIndex targetIndex
  retainedPositiveSector fiberInterface =
  mkScalarPairIncidenceKernelSurface
    (Exact.ExactRetainedTriadFiberInterface.fiberAggregate fiberInterface)
    (λ f t → refl)

------------------------------------------------------------------------
-- Explicit Nat/scalar boundary.
--
-- The physical formula remains the existing Nat-valued target.  This record
-- states the exact comparison needed to put that Nat kernel on the scalar
-- surface.  It is intentionally a field-bearing boundary, not a fabricated
-- physical bridge.
------------------------------------------------------------------------

record NatToScalarPairIncidenceKernelComparison
    {S : Exact.ExactScalarOperations}
    (surface : Exact.FiniteTriadModeSurface S)
    (profile : Exact.AdmissibleAmplitudeProfile surface)
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (relationData :
      Relation.ActualPairIncidenceRelationData
        residueNormModel shellIndex)
    (physicalFormula :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget
        residueNormModel shellIndex)
    (SourceIndex TargetIndex : Exact.FiniteCarrier)
    (sourceIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex)
    (targetIndex :
      Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex)
    (retainedPositiveSector : Exact.TriadOf surface → Set)
    (fiberInterface :
      Exact.ExactRetainedTriadFiberInterface
        surface
        profile
        SourceIndex
        TargetIndex
        sourceIndex
        targetIndex
        retainedPositiveSector)
    (kernelSurface :
      ScalarPairIncidenceKernelSurface
        surface
        profile
        SourceIndex
        TargetIndex
        sourceIndex
        targetIndex
        retainedPositiveSector
        fiberInterface)
    (bridge :
      Exact.ActualPairIncidenceKernelFormulaBridge
        surface
        profile
        relationData
        physicalFormula
        SourceIndex
        TargetIndex
        sourceIndex
        targetIndex
        retainedPositiveSector
        fiberInterface) : Setω where
  constructor mkNatToScalarPairIncidenceKernelComparison
  field
    natKernelAgreesWithScalarKernel :
      (f :
        KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
          physicalFormula) →
      (t :
        KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
          physicalFormula) →
      Exact.ExactScalarOperations.natToScalar S
        (KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
          physicalFormula f t)
        ≡
      scalarKernel kernelSurface
        (Exact.ActualPairIncidenceKernelFormulaBridge.sourceProjection
          bridge f)
        (Exact.ActualPairIncidenceKernelFormulaBridge.targetProjection
          bridge t)

------------------------------------------------------------------------
-- Conditional composition from the existing physical bridge.
--
-- This constructor is useful to scalar Schur consumers, but it cannot be
-- called until the physical bridge and exact retained-fiber interface have
-- actually been supplied.
------------------------------------------------------------------------

natToScalarPairIncidenceKernelComparisonFromBridge :
  {S : Exact.ExactScalarOperations} →
  (surface : Exact.FiniteTriadModeSurface S) →
  (profile : Exact.AdmissibleAmplitudeProfile surface) →
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  (relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex) →
  (physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex) →
  (SourceIndex TargetIndex : Exact.FiniteCarrier) →
  (sourceIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier SourceIndex) →
  (targetIndex :
    Exact.TriadOf surface → Exact.FiniteCarrier.Carrier TargetIndex) →
  (retainedPositiveSector : Exact.TriadOf surface → Set) →
  (fiberInterface :
    Exact.ExactRetainedTriadFiberInterface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector) →
  (kernelSurface :
    ScalarPairIncidenceKernelSurface
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector
      fiberInterface) →
  (bridge :
    Exact.ActualPairIncidenceKernelFormulaBridge
      surface
      profile
      relationData
      physicalFormula
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector
      fiberInterface) →
  NatToScalarPairIncidenceKernelComparison
    surface
    profile
    relationData
    physicalFormula
    SourceIndex
    TargetIndex
    sourceIndex
    targetIndex
    retainedPositiveSector
    fiberInterface
    kernelSurface
    bridge
natToScalarPairIncidenceKernelComparisonFromBridge
  surface profile relationData physicalFormula
  SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector
  fiberInterface kernelSurface bridge =
  mkNatToScalarPairIncidenceKernelComparison
    (λ f t →
      trans
        (Exact.ActualPairIncidenceKernelFormulaBridge.physicalKernelAgreesWithExactFiberAggregate
          bridge f t)
        (sym
          (ScalarPairIncidenceKernelSurface.scalarKernelAgreesWithFiberAggregate
            kernelSurface
            (Exact.ActualPairIncidenceKernelFormulaBridge.sourceProjection
              bridge f)
            (Exact.ActualPairIncidenceKernelFormulaBridge.targetProjection
              bridge t))))
