{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2NodeCouplingCoordinateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteSourceTrajectoryExact as Source
import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteNodeCouplingExact as Node
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CORRECTED EARLY SAME-OBJECT COORDINATE
--
-- A2 is indexed by source/RG nodes.  The literal plaquette producer is indexed
-- by one-step edges.  Therefore A2 must be identified with the NODE-ALIGNED
-- coupling compiled by LiteralPlaquetteNodeCoupling, not with
-- producer.coupling at the same natural number.
------------------------------------------------------------------------

record A2NodeCouplingCoordinate
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    {plaquette : Plaquette.PhysicalRunningCouplingData Nat}
    {coherence : Source.LiteralPlaquetteUVChainCoherence plaquette}
    (nodeCoupling : Node.LiteralPlaquetteNodeCoupling plaquette coherence) : Set₁ where
  field
    a2CouplingIsSourceNodeCoupling :
      ∀ j → j ℕ.< cutoff →
      Direct.coupling
        (Quartic.direct (A2.quartic (Present.a2 present))) j
      ≡ Node.sourceCoupling nodeCoupling j

open A2NodeCouplingCoordinate public

sourceNodeCouplingBelowA2Cap :
  ∀ {HistoryCarrier Cell cutoff present plaquette coherence nodeCoupling} →
  A2NodeCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present nodeCoupling →
  ∀ j → j ℕ.< cutoff →
  Node.sourceCoupling nodeCoupling j
  ≤ Quartic.couplingCap (A2.quartic (Present.a2 present))
sourceNodeCouplingBelowA2Cap
    {present = present} coordinate j j<cutoff =
  let
    quartic = A2.quartic (Present.a2 present)
    raw = Quartic.couplingBelowCap quartic j j<cutoff
  in
  subst
    (λ lower → lower ≤ Quartic.couplingCap quartic)
    (a2CouplingIsSourceNodeCoupling coordinate j j<cutoff)
    raw

sourceNodeCouplingBelowCanonicalRowA :
  ∀ {HistoryCarrier Cell cutoff present plaquette coherence nodeCoupling} →
  A2NodeCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present nodeCoupling →
  ∀ j → j ℕ.< cutoff →
  Node.sourceCoupling nodeCoupling j
  ≤ RowA.canonicalQuarticResponseGamma (Unified.rowAConstantsFromA2 present)
sourceNodeCouplingBelowCanonicalRowA
    {present = present} coordinate j j<cutoff =
  subst
    (λ upper → Node.sourceCoupling _ j ≤ upper)
    (Unified.a2CapIsRowAGamma present)
    (sourceNodeCouplingBelowA2Cap coordinate j j<cutoff)

sameIndexProducerCouplingA2WeldPreferred : Bool
sameIndexProducerCouplingA2WeldPreferred = false

nodeAlignedA2CouplingWeldPreferred : Bool
nodeAlignedA2CouplingWeldPreferred = true

sameIndexProducerCouplingA2WeldPreferredIsFalse :
  sameIndexProducerCouplingA2WeldPreferred ≡ false
sameIndexProducerCouplingA2WeldPreferredIsFalse = refl

nodeAlignedA2CouplingWeldPreferredIsTrue :
  nodeAlignedA2CouplingWeldPreferred ≡ true
nodeAlignedA2CouplingWeldPreferredIsTrue = refl

a2NodeCouplingCapCompilerLevel : ProofLevel
a2NodeCouplingCapCompilerLevel = machineChecked

-- Physical same-object wall after the indexing correction:
-- A2's generated-action coupling must be the exact source-node coupling, whose
-- successor nodes are producer CURRENT couplings from the preceding edge.
literalA2CouplingIsNodeAlignedSourceCouplingLevel : ProofLevel
literalA2CouplingIsNodeAlignedSourceCouplingLevel = conditional
