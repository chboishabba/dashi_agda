{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2CMP109SourceCouplingExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119AntigravityCMP109SourceCouplingCoordinateExact as SourceCoupling
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.YangMills.BalabanYM4SourceNormalizedCouplingRecurrenceExact as Flow
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- PRE-CMP122 A2 -> PRIMARY CMP109 SOURCE COUPLING
------------------------------------------------------------------------

record A2CMP109SourceCouplingCoordinate
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    {trajectory : Flow.SourceNormalizedCouplingTrajectory}
    (source : SourceCoupling.CMP109SourceCouplingCoordinate trajectory) : Set₁ where
  field
    a2CouplingIsCMP109SourceCoupling :
      ∀ j → j ℕ.< cutoff →
      Direct.coupling
        (Quartic.direct (A2.quartic (Present.a2 present))) j
      ≡ SourceCoupling.sourceCoupling source j

open A2CMP109SourceCouplingCoordinate public

sourceCouplingBelowA2Cap :
  ∀ {HistoryCarrier Cell cutoff present trajectory source} →
  A2CMP109SourceCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present source →
  ∀ j → j ℕ.< cutoff →
  SourceCoupling.sourceCoupling source j
  ≤ Quartic.couplingCap (A2.quartic (Present.a2 present))
sourceCouplingBelowA2Cap {present = present} coordinate j j<cutoff =
  subst
    (λ lower →
      lower ≤ Quartic.couplingCap (A2.quartic (Present.a2 present)))
    (a2CouplingIsCMP109SourceCoupling coordinate j j<cutoff)
    (Quartic.couplingBelowCap
      (A2.quartic (Present.a2 present))
      j j<cutoff)

sourceCouplingBelowCanonicalRowA :
  ∀ {HistoryCarrier Cell cutoff present trajectory source} →
  A2CMP109SourceCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present source →
  ∀ j → j ℕ.< cutoff →
  SourceCoupling.sourceCoupling source j
  ≤ RowA.canonicalQuarticResponseGamma (Unified.rowAConstantsFromA2 present)
sourceCouplingBelowCanonicalRowA
    {present = present} coordinate j j<cutoff =
  subst
    (λ upper → SourceCoupling.sourceCoupling _ j ≤ upper)
    (Unified.a2CapIsRowAGamma present)
    (sourceCouplingBelowA2Cap coordinate j j<cutoff)

cmp122DensityRequiredForA2CMP109CouplingWeld : Bool
cmp122DensityRequiredForA2CMP109CouplingWeld = false

canonicalRowACapFollowsFromA2CMP109Weld : Bool
canonicalRowACapFollowsFromA2CMP109Weld = true

cmp122DensityRequiredForA2CMP109CouplingWeldIsFalse :
  cmp122DensityRequiredForA2CMP109CouplingWeld ≡ false
cmp122DensityRequiredForA2CMP109CouplingWeldIsFalse = refl

canonicalRowACapFollowsFromA2CMP109WeldIsTrue :
  canonicalRowACapFollowsFromA2CMP109Weld ≡ true
canonicalRowACapFollowsFromA2CMP109WeldIsTrue = refl

a2CMP109SourceCouplingCompilerLevel : ProofLevel
a2CMP109SourceCouplingCompilerLevel = machineChecked

literalA2CouplingIsCMP109SourceCouplingLevel : ProofLevel
literalA2CouplingIsCMP109SourceCouplingLevel = conditional
