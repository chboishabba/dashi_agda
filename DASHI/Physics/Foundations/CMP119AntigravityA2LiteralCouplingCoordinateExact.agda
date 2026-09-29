{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityA2LiteralCouplingCoordinateExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as ℕ
open import Data.Rational.Base using (_≤_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Foundations.CMP119AntigravityLiteralPlaquetteTerminalHistoryExact as Literal
import DASHI.Physics.YangMills.BalabanClayT4LocalizedPlaquetteCoefficientProducerExact as Plaquette
import DASHI.Physics.YangMills.BalabanClayPresentCutPhysicalCompilerRound122Exact as Present
import DASHI.Physics.YangMills.BalabanYM4WardQuarticResponseProducerAdapterExact as A2
import DASHI.Physics.YangMills.BalabanYM4QuarticSourceSensitivityBudgetExact as Quartic
import DASHI.Physics.YangMills.BalabanYM4ShootingSensitivityFromCubicDriftExact as Direct
import DASHI.Physics.YangMills.BalabanYM4QuarticResponseCanonicalChoiceExact as RowA
import DASHI.Physics.Foundations.CMP119AntigravityUnifiedA2RowACapExact as Unified
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- EARLY SAME-OBJECT COORDINATE: A2 COUPLING = LITERAL PLAQUETTE COUPLING
--
-- This carrier deliberately sits BEFORE BetaDrivenCompleteDensityInputs.
-- It breaks the previous construction cycle:
--
--   terminal threshold -> beta density -> unified A2 history -> Row-A cap
--       ^                                                   |
--       |___________________________________________________|
--
-- The actual physical identity needed is earlier and simpler:
--
--   Direct.coupling(A2,j) = literal plaquette coupling(j).
--
-- Once that one equality is supplied, the already-owned A2 cap and canonical
-- cap equality prove the literal coupling is below the SAME Row-A gamma.
------------------------------------------------------------------------

record A2LiteralCouplingCoordinate
    {HistoryCarrier Cell : Set}
    {cutoff : Nat}
    (present : Present.PresentCutPhysicalSourceInputs HistoryCarrier Cell cutoff)
    (plaquette : Plaquette.PhysicalRunningCouplingData Nat) : Set₁ where
  field
    a2CouplingIsLiteral :
      ∀ j → j ℕ.< cutoff →
      Direct.coupling
        (Quartic.direct (A2.quartic (Present.a2 present))) j
      ≡ Literal.literalCouplingAt plaquette j

open A2LiteralCouplingCoordinate public

literalCouplingBelowA2Cap :
  ∀ {HistoryCarrier Cell cutoff present plaquette} →
  A2LiteralCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present plaquette →
  ∀ j → j ℕ.< cutoff →
  Literal.literalCouplingAt plaquette j
  ≤ Quartic.couplingCap (A2.quartic (Present.a2 present))
literalCouplingBelowA2Cap
    {present = present} coordinate j j<cutoff =
  let
    quartic = A2.quartic (Present.a2 present)
    raw =
      Quartic.couplingBelowCap quartic j j<cutoff
  in
  subst
    (λ lower → lower ≤ Quartic.couplingCap quartic)
    (a2CouplingIsLiteral coordinate j j<cutoff)
    raw

literalCouplingBelowCanonicalRowA :
  ∀ {HistoryCarrier Cell cutoff present plaquette} →
  A2LiteralCouplingCoordinate
    {HistoryCarrier = HistoryCarrier} {Cell = Cell} {cutoff = cutoff}
    present plaquette →
  ∀ j → j ℕ.< cutoff →
  Literal.literalCouplingAt plaquette j
  ≤ RowA.canonicalQuarticResponseGamma (Unified.rowAConstantsFromA2 present)
literalCouplingBelowCanonicalRowA
    {present = present} coordinate j j<cutoff =
  subst
    (λ upper → Literal.literalCouplingAt _ j ≤ upper)
    (Unified.a2CapIsRowAGamma present)
    (literalCouplingBelowA2Cap coordinate j j<cutoff)

densityPackageRequiredToStateA2LiteralCouplingIdentity : Bool
densityPackageRequiredToStateA2LiteralCouplingIdentity = false

rowACapFollowsFromA2LiteralCouplingIdentity : Bool
rowACapFollowsFromA2LiteralCouplingIdentity = true

densityPackageRequiredToStateA2LiteralCouplingIdentityIsFalse :
  densityPackageRequiredToStateA2LiteralCouplingIdentity ≡ false
densityPackageRequiredToStateA2LiteralCouplingIdentityIsFalse = refl

rowACapFollowsFromA2LiteralCouplingIdentityIsTrue :
  rowACapFollowsFromA2LiteralCouplingIdentity ≡ true
rowACapFollowsFromA2LiteralCouplingIdentityIsTrue = refl

a2LiteralCouplingCapCompilerLevel : ProofLevel
a2LiteralCouplingCapCompilerLevel = machineChecked

-- This is now the source-facing same-object wall for the Row-A/S4 coupling:
-- identify the physical A2 shooting coupling with the literal plaquette
-- coupling before either is repackaged as a CMP122 beta-history coordinate.
literalA2CouplingIsLiteralPlaquetteCouplingLevel : ProofLevel
literalA2CouplingIsLiteralPlaquetteCouplingLevel = conditional
