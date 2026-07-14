module DASHI.Physics.Closure.NSTriadKNConcreteActualRetainedFiber where

open import Relation.Binary.PropositionalEquality using (_≡_; trans)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNPairIncidenceKernelFormula as KernelFormula
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm

------------------------------------------------------------------------
-- Typed boundary for the missing retained-sector construction.
--
-- The relation and physical-formula records deliberately expose independent
-- finite and tail index types.  The projections below are therefore part of
-- the interface: an inhabitant must say how the physical-formula indices are
-- represented by the actual relation indices.  The retained count is taken
-- from the physical target's finite weighted fiber aggregate; no independent
-- Nat-valued proxy count is admitted here.
------------------------------------------------------------------------

record ConcreteActualRetainedFiberInterface
    {residueNormModel : ResidueNorm.ResidueNormModel}
    {shellIndex : Nat}
    (relationData :
      Relation.ActualPairIncidenceRelationData
        residueNormModel shellIndex)
    (physicalFormula :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget
        residueNormModel shellIndex) : Set₂ where
  constructor mkConcreteActualRetainedFiberInterface
  field
    sourceProjection :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
        physicalFormula ->
      Relation.ActualPairIncidenceRelationData.FiniteIndex
        relationData

    targetProjection :
      KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
        physicalFormula ->
      Relation.ActualPairIncidenceRelationData.TailIndex
        relationData

    finiteFiberCountAgreesWithRelation :
      (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
        physicalFormula) ->
      (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
        physicalFormula) ->
      KernelFormula.RetainedTriadFiberEnumerationInputs.fiberAggregate
        (KernelFormula.ActualPairIncidenceKernelFormulaTarget.enumeration
          physicalFormula)
        f t ≡
      Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
        relationData
        (sourceProjection f)
        (targetProjection t)

open ConcreteActualRetainedFiberInterface public

------------------------------------------------------------------------
-- The target alias is intentionally only a type.  In particular, this file
-- does not construct a relationData, physicalFormula, projection, enumeration,
-- or agreement witness and does not alter any downstream gate.
------------------------------------------------------------------------

ConcreteActualRetainedFiberTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) ->
  (shellIndex : Nat) ->
  (relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex) ->
  (physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex) -> Set₂
ConcreteActualRetainedFiberTarget residueNormModel shellIndex
  relationData physicalFormula =
  ConcreteActualRetainedFiberInterface relationData physicalFormula

------------------------------------------------------------------------
-- Conditional consequences: these are projections/compositions from an
-- interface inhabitant.  They do not construct the physical target, its
-- retained fiber, or any proxy-to-physical equality.
------------------------------------------------------------------------

actualKernelAgreesWithFiniteFiberAggregate :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  {relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex} ->
  {physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex} ->
  (interface :
    ConcreteActualRetainedFiberInterface relationData physicalFormula) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    physicalFormula) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    physicalFormula) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    physicalFormula f t ≡
  KernelFormula.RetainedTriadFiberEnumerationInputs.fiberAggregate
    (KernelFormula.ActualPairIncidenceKernelFormulaTarget.enumeration
      physicalFormula)
    f t
actualKernelAgreesWithFiniteFiberAggregate
  {physicalFormula = physicalFormula} interface f t =
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernelFormula
    physicalFormula f t

actualKernelAgreesWithFiniteWeightedFiber :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  {relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex} ->
  {physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex} ->
  (interface :
    ConcreteActualRetainedFiberInterface relationData physicalFormula) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    physicalFormula) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    physicalFormula) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    physicalFormula f t ≡
  KernelFormula.weightedListSum
    (KernelFormula.ActualPairIncidenceKernelFormulaTarget.triadWeight
      physicalFormula)
    (KernelFormula.RetainedTriadFiberEnumerationInputs.fiber
      (KernelFormula.ActualPairIncidenceKernelFormulaTarget.enumeration
        physicalFormula)
      f t)
actualKernelAgreesWithFiniteWeightedFiber
  {physicalFormula = physicalFormula} interface f t =
  trans
    (actualKernelAgreesWithFiniteFiberAggregate interface f t)
    (KernelFormula.RetainedTriadFiberEnumerationInputs.fiberAggregateIsFiniteWeightedSum
      (KernelFormula.ActualPairIncidenceKernelFormulaTarget.enumeration
        physicalFormula) f t)

actualKernelAgreesWithRelationCount :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  {relationData :
    Relation.ActualPairIncidenceRelationData
      residueNormModel shellIndex} ->
  {physicalFormula :
    KernelFormula.ActualPairIncidenceKernelFormulaTarget
      residueNormModel shellIndex} ->
  (interface :
    ConcreteActualRetainedFiberInterface relationData physicalFormula) ->
  (f : KernelFormula.ActualPairIncidenceKernelFormulaTarget.FiniteIndex
    physicalFormula) ->
  (t : KernelFormula.ActualPairIncidenceKernelFormulaTarget.TailIndex
    physicalFormula) ->
  KernelFormula.ActualPairIncidenceKernelFormulaTarget.actualKernel
    physicalFormula f t ≡
  Relation.ActualPairIncidenceRelationData.repeatedPairIncidenceCount
    relationData
    (ConcreteActualRetainedFiberInterface.sourceProjection interface f)
    (ConcreteActualRetainedFiberInterface.targetProjection interface t)
actualKernelAgreesWithRelationCount interface f t =
  trans
    (actualKernelAgreesWithFiniteFiberAggregate interface f t)
    (ConcreteActualRetainedFiberInterface.finiteFiberCountAgreesWithRelation
      interface f t)
