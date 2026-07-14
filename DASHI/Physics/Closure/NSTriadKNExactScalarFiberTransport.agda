module DASHI.Physics.Closure.NSTriadKNExactScalarFiberTransport where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNExactAlgebraicRetainedTriadFiber as Exact
import DASHI.Physics.Closure.NSTriadKNExactScalarNatEmbedding as Embedding
import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- A Nat presentation for the scalar weights on an exact retained fiber.
------------------------------------------------------------------------

record NatTriadWeightPresentation
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
  constructor mkNatTriadWeightPresentation
  field
    natWeight : Exact.TriadOf surface → Nat

    scalarWeightAgrees :
      (τ : Exact.TriadOf surface) →
      Exact.ExactRetainedTriadFiberInterface.triadWeight
        fiberInterface τ
        ≡
      Exact.ExactScalarOperations.natToScalar S (natWeight τ)

------------------------------------------------------------------------
-- The reusable fiber transport.  The only scalar arithmetic used here is
-- supplied by NatToScalarAdditive; the retained fiber and its aggregate are
-- supplied by the exact interface.
------------------------------------------------------------------------

fiberAggregateEqualsNatToScalarNatWeightedListSum :
  {S : Exact.ExactScalarOperations} →
  (laws : Embedding.NatToScalarAdditive S) →
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
  (presentation :
    NatTriadWeightPresentation
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
  Exact.ExactRetainedTriadFiberInterface.fiberAggregate
    fiberInterface f t
    ≡
  Exact.ExactScalarOperations.natToScalar S
    (Embedding.natListSum
      (NatTriadWeightPresentation.natWeight presentation)
      (Exact.ExactRetainedTriadFiberInterface.fiber fiberInterface f t))
fiberAggregateEqualsNatToScalarNatWeightedListSum
  laws surface profile SourceIndex TargetIndex sourceIndex targetIndex
  retainedPositiveSector fiberInterface presentation f t =
  trans
    (Exact.ExactRetainedTriadFiberInterface.fiberAggregateIsFiniteWeightedSum
      fiberInterface f t)
    (Embedding.natToScalarWeightedListSumFromAgreement
      laws
      (Exact.ExactRetainedTriadFiberInterface.triadWeight fiberInterface)
      (NatTriadWeightPresentation.natWeight presentation)
      (NatTriadWeightPresentation.scalarWeightAgrees presentation)
      (Exact.ExactRetainedTriadFiberInterface.fiber fiberInterface f t))

------------------------------------------------------------------------
-- Physical transport.  The bridge remains an explicit input: this module
-- supplies no physical triad map, projection, or kernel equality.
------------------------------------------------------------------------

physicalKernelEqualsNatToScalarNatWeightedListSum :
  {S : Exact.ExactScalarOperations} →
  (laws : Embedding.NatToScalarAdditive S) →
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
  (presentation :
    NatTriadWeightPresentation
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
  Exact.ExactScalarOperations.natToScalar S
    (Embedding.natListSum
      (NatTriadWeightPresentation.natWeight presentation)
      (Exact.ExactRetainedTriadFiberInterface.fiber fiberInterface
        (Exact.ActualPairIncidenceKernelFormulaBridge.sourceProjection
          bridge f)
        (Exact.ActualPairIncidenceKernelFormulaBridge.targetProjection
          bridge t)))
physicalKernelEqualsNatToScalarNatWeightedListSum
  laws surface profile relationData physicalFormula
  SourceIndex TargetIndex sourceIndex targetIndex retainedPositiveSector
  fiberInterface presentation bridge f t =
  trans
    (Exact.ActualPairIncidenceKernelFormulaBridge.physicalKernelAgreesWithExactFiberAggregate
      bridge f t)
    (fiberAggregateEqualsNatToScalarNatWeightedListSum
      laws
      surface
      profile
      SourceIndex
      TargetIndex
      sourceIndex
      targetIndex
      retainedPositiveSector
      fiberInterface
      presentation
      (Exact.ActualPairIncidenceKernelFormulaBridge.sourceProjection
        bridge f)
      (Exact.ActualPairIncidenceKernelFormulaBridge.targetProjection
        bridge t))
