module DASHI.Physics.Closure.NSTriadKNForcedTailWeightedDecayInvestigation where

------------------------------------------------------------------------
-- Highest-value forced-tail weighted-decay investigation.
--
-- This module is deliberately adjacent to, rather than merged into, the
-- existing Schur surface.  It separates three facts that are currently
-- easy to conflate:
--
--   1. the concrete triad kernel has a scaled pointwise ceiling;
--   2. finite weighted row/column sums reduce to classwise ceiling budgets;
--   3. the physical retained-sector kernel has been identified with that
--      proxy fold.
--
-- (1) and the algebra in (2) are available.  The identification in (3) is
-- not available in the current relation surface, so no actual N^-2 theorem
-- is claimed here.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)
open import Data.Nat using (_≤_)
open import Data.Nat.Properties using (≤-reflexive; ≤-trans)

import DASHI.Physics.Closure.NSTriadKNConcreteWeightedSchurDecay as Concrete
import DASHI.Physics.Closure.NSTriadKNConcreteWeightedFiberFolds as Folds
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteIncidenceType as Incidence
import DASHI.Physics.Closure.NSTriadKNForcedTailConcreteNatBounds as NatBounds
import DASHI.Physics.Closure.NSTriadKNForcedTailPrimitiveEstimates as ForcedTail
import DASHI.Physics.Closure.NSTriadKNPairIncidenceRelation as Relation

------------------------------------------------------------------------
-- Available actual premise: pointwise scaled kernel ceiling.
------------------------------------------------------------------------

record ForcedTailActualKernelCeiling (N : Nat)
    (c : ForcedTail.ForcedTailClass) : Set₁ where
  constructor mkForcedTailActualKernelCeiling
  field
    ceiling :
      (τ : Incidence.ForcedTailTriadIncidence c N) →
      Incidence.actualForcedTailKernelWeight N τ ≤
        ForcedTail.forcedTailClassProductN2Constant c

open ForcedTailActualKernelCeiling public

canonicalForcedTailActualKernelCeiling :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  ForcedTailActualKernelCeiling N c
canonicalForcedTailActualKernelCeiling =
  mkForcedTailActualKernelCeiling
    (λ τ -> Incidence.forcedTailActualEnvelopeClassBound _ τ)

------------------------------------------------------------------------
-- Available classwise arithmetic premise.
--
-- This is the division-free N^2-scaled count/magnitude arithmetic.  It is
-- useful downstream, but it does not by itself identify a physical kernel
-- row or column sum.
------------------------------------------------------------------------

forcedTailClassN2ScaledArithmetic :
  (c : ForcedTail.ForcedTailClass) ->
  (N : Nat) ->
  NatBounds.forcedTailN2ScaledLHS c N ≤
    NatBounds.forcedTailN2ScaledRHS c N
forcedTailClassN2ScaledArithmetic = NatBounds.forcedTailN2ScaledArithmetic

------------------------------------------------------------------------
-- Typed proxy-decay premises for one concrete forced-tail class.
--
-- The row and column budgets are stated against the exact finite sums used
-- by NSTriadKNConcreteWeightedSchurDecay.  They are therefore honest
-- interfaces: the bridge below proves the decay theorem from these fields,
-- rather than hiding them behind a status flag.
------------------------------------------------------------------------

record ForcedTailClassWeightedDecayPremises (N : Nat)
    (c : ForcedTail.ForcedTailClass) : Set₁ where
  constructor mkForcedTailClassWeightedDecayPremises
  field
    sourceWeight :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat

    targetWeight :
      Relation.ConcreteNonResidualTailIndex N -> Nat

    rowConstant : Nat
    columnConstant : Nat

    rowCeiling :
      (h : Incidence.ForcedTailHead c N) -> Nat

    rowPointwise :
      (h : Incidence.ForcedTailHead c N) ->
      (i : Incidence.ForcedTailTail c N) ->
      targetWeight (Relation.forcedTailTailIndex c i) ≤ rowCeiling h

    rowBudget :
      (h : Incidence.ForcedTailHead c N) ->
      Relation.forcedTailPairIncidenceCount c c *
        (rowCeiling h * ForcedTail.forcedTailTailCountBound c N) ≤
      rowConstant * sourceWeight (Relation.forcedTailFiniteIndex c h)

    columnCeiling :
      (h : Incidence.ForcedTailTail c N) -> Nat

    columnPointwise :
      (h : Incidence.ForcedTailTail c N) ->
      (i : Incidence.ForcedTailHead c N) ->
      sourceWeight (Relation.forcedTailFiniteIndex c i) ≤ columnCeiling h

    columnBudget :
      (h : Incidence.ForcedTailTail c N) ->
      Relation.forcedTailPairIncidenceCount c c *
        (columnCeiling h * ForcedTail.forcedTailHeadCountBound c N) ≤
      columnConstant * targetWeight (Relation.forcedTailTailIndex c h)

    actualKernelCeiling : ForcedTailActualKernelCeiling N c

open ForcedTailClassWeightedDecayPremises public

------------------------------------------------------------------------
-- Per-class weighted decay target and constructive bridge.
------------------------------------------------------------------------

record ForcedTailClassWeightedDecayTarget (N : Nat)
    (c : ForcedTail.ForcedTailClass) : Set₁ where
  constructor mkForcedTailClassWeightedDecayTarget
  field
    sourceWeight :
      Relation.ConcreteNonResidualFiniteIndex N -> Nat

    targetWeight :
      Relation.ConcreteNonResidualTailIndex N -> Nat

    rowConstant : Nat
    columnConstant : Nat

    actualKernelCeiling : ForcedTailActualKernelCeiling N c

    weightedRowDecay :
      (h : Incidence.ForcedTailHead c N) ->
      Folds.weightedConcreteRowSum targetWeight
        (Relation.forcedTailFiniteIndex c h) ≤
      rowConstant * sourceWeight (Relation.forcedTailFiniteIndex c h)

    weightedColumnDecay :
      (h : Incidence.ForcedTailTail c N) ->
      Folds.weightedConcreteColumnSum sourceWeight
        (Relation.forcedTailTailIndex c h) ≤
      columnConstant * targetWeight (Relation.forcedTailTailIndex c h)

forcedTailClassWeightedDecayTargetFromPremises :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  (premises : ForcedTailClassWeightedDecayPremises N c) ->
  ForcedTailClassWeightedDecayTarget N c
forcedTailClassWeightedDecayTargetFromPremises
  {N = N} {c = c} premises =
  mkForcedTailClassWeightedDecayTarget
    (sourceWeight premises)
    (targetWeight premises)
    (rowConstant premises)
    (columnConstant premises)
    (actualKernelCeiling premises)
    rowDecay
    columnDecay
  where
  rowDecay :
    (h : Incidence.ForcedTailHead c N) ->
    Folds.weightedConcreteRowSum
      (targetWeight premises)
      (Relation.forcedTailFiniteIndex c h) ≤
    rowConstant premises *
      sourceWeight premises (Relation.forcedTailFiniteIndex c h)
  rowDecay h =
    ≤-trans
      (Concrete.forcedTailWeightedRowDecayFromCeiling
        (targetWeight premises)
        _
        h
        (rowCeiling premises h)
        (rowPointwise premises h))
      (rowBudget premises h)

  columnDecay :
    (h : Incidence.ForcedTailTail c N) ->
    Folds.weightedConcreteColumnSum
      (sourceWeight premises)
      (Relation.forcedTailTailIndex c h) ≤
    columnConstant premises *
      targetWeight premises (Relation.forcedTailTailIndex c h)
  columnDecay h =
    ≤-trans
      (Concrete.forcedTailWeightedColumnDecayFromCeiling
        (sourceWeight premises)
        _
        h
        (columnCeiling premises h)
        (columnPointwise premises h))
      (columnBudget premises h)

------------------------------------------------------------------------
-- Exact physical-kernel boundary.
--
-- A physical route needs a row/column sum and an equality to the proxy fold.
-- The current PairIncidenceRelation exposes only the tagged proxy count and
-- explicitly leaves the retained-sector/actual-count construction open.
-- This record is the smallest typed bridge needed to consume a per-class
-- target above without pretending that the proxy fold is already physical.
------------------------------------------------------------------------

record ForcedTailPhysicalKernelFoldBridge (N : Nat)
    (c : ForcedTail.ForcedTailClass)
    (premises : ForcedTailClassWeightedDecayPremises N c) : Set₁ where
  constructor mkForcedTailPhysicalKernelFoldBridge
  field
    physicalRowSum : Incidence.ForcedTailHead c N -> Nat
    physicalColumnSum : Incidence.ForcedTailTail c N -> Nat

    physicalRowAgreesWithProxyFold :
      (h : Incidence.ForcedTailHead c N) ->
      physicalRowSum h ≡
      Folds.weightedConcreteRowSum (targetWeight premises)
        (Relation.forcedTailFiniteIndex c h)

    physicalColumnAgreesWithProxyFold :
      (h : Incidence.ForcedTailTail c N) ->
      physicalColumnSum h ≡
      Folds.weightedConcreteColumnSum (sourceWeight premises)
        (Relation.forcedTailTailIndex c h)

open ForcedTailPhysicalKernelFoldBridge public

record ForcedTailClassPhysicalWeightedDecayTarget (N : Nat)
    (c : ForcedTail.ForcedTailClass)
    (premises : ForcedTailClassWeightedDecayPremises N c)
    (bridge : ForcedTailPhysicalKernelFoldBridge N c premises) : Set₁ where
  constructor mkForcedTailClassPhysicalWeightedDecayTarget
  field
    physicalRowDecay :
      (h : Incidence.ForcedTailHead c N) ->
      physicalRowSum bridge h ≤
      rowConstant premises *
        sourceWeight premises (Relation.forcedTailFiniteIndex c h)

    physicalColumnDecay :
      (h : Incidence.ForcedTailTail c N) ->
      physicalColumnSum bridge h ≤
      columnConstant premises *
        targetWeight premises (Relation.forcedTailTailIndex c h)

------------------------------------------------------------------------
-- The physical record above is intentionally only a boundary declaration:
-- no canonical bridge is supplied.  The usable transport below consumes an
-- explicit bridge and has no hidden inhabitant.
------------------------------------------------------------------------

forcedTailClassPhysicalWeightedDecayTargetFromBridge :
  {N : Nat} ->
  {c : ForcedTail.ForcedTailClass} ->
  (premises : ForcedTailClassWeightedDecayPremises N c) ->
  (bridge : ForcedTailPhysicalKernelFoldBridge N c premises) ->
  ForcedTailClassPhysicalWeightedDecayTarget N c premises bridge
forcedTailClassPhysicalWeightedDecayTargetFromBridge
  {N = N} {c = c} premises bridge =
  mkForcedTailClassPhysicalWeightedDecayTarget rowDecay columnDecay
  where
  rowDecay :
    (h : Incidence.ForcedTailHead c N) ->
    physicalRowSum bridge h ≤
    rowConstant premises *
      sourceWeight premises (Relation.forcedTailFiniteIndex c h)
  rowDecay h =
    ≤-trans
      (≤-reflexive (physicalRowAgreesWithProxyFold bridge h))
      (≤-trans
        (Concrete.forcedTailWeightedRowDecayFromCeiling
          (targetWeight premises)
          c
          h
          (rowCeiling premises h)
          (rowPointwise premises h))
        (rowBudget premises h))

  columnDecay :
    (h : Incidence.ForcedTailTail c N) ->
    physicalColumnSum bridge h ≤
    columnConstant premises *
      targetWeight premises (Relation.forcedTailTailIndex c h)
  columnDecay h =
    ≤-trans
      (≤-reflexive (physicalColumnAgreesWithProxyFold bridge h))
      (≤-trans
        (Concrete.forcedTailWeightedColumnDecayFromCeiling
          (sourceWeight premises)
          c
          h
          (columnCeiling premises h)
          (columnPointwise premises h))
        (columnBudget premises h))

------------------------------------------------------------------------
-- Boundary statement (prose is intentionally kept next to the types).
--
-- The last transport is not a completed physical theorem: it transports
-- both row and column bounds only after an explicit physical/proxy equality
-- is supplied through ForcedTailPhysicalKernelFoldBridge.
--
-- Missing premises for a genuine forced-tail N^-2 weighted-decay theorem:
--
--   * an actual retained-sector count formula agreeing with the physical
--     repeated-pair relation;
--   * an actual-kernel finite-fiber sum agreeing with the concrete weighted
--     proxy fold; and
--   * classwise budgets whose constants are in the intended N^-2 scaling,
--     not merely Nat ceilings.
--
-- The imported pi-product bound supplies the pointwise scaled ceiling used
-- above, but it does not supply any of those three bridges.
------------------------------------------------------------------------
