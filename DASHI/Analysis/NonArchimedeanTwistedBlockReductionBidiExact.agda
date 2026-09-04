module DASHI.Analysis.NonArchimedeanTwistedBlockReductionBidiExact where

------------------------------------------------------------------------
-- Twisted-block reduction BIDI boundary.
--
-- Source audit of `TwistedBlockPow.lean` shows a precise split:
-- `TwistedBlockPowConjecture` states the concrete spatial theorem, while
-- `twisted_block_pow_of_monomial_scale_n` is an unconditional reduction for
-- an arbitrary monomial model supplied with period and orbit-weight receipts.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

record TwistedBlockReductionStatus : Set where
  constructor twistedBlockReductionStatus
  field
    genericMonomialPowerTheoremOwned : Bool
    concreteSpatialPowerStatementExists : Bool
    concreteSpatialPowerStatementIsDefinitionConjecture : Bool
    concreteSpatialEqualsGenericMonomialOwned : Bool
    concreteCycleReceiptOwnedAtReductionSite : Bool
    concreteWeightReceiptOwnedAtReductionSite : Bool
    genericReductionProvesConcreteSpatialWithoutWeld : Bool

canonicalTwistedBlockReductionStatus : TwistedBlockReductionStatus
canonicalTwistedBlockReductionStatus =
  twistedBlockReductionStatus true true true false false false false


data SpatialPowerObligation : Set where
  monomialSameObjectWeld : SpatialPowerObligation
  fullPeriodReceipt : SpatialPowerObligation
  fullOrbitWeightReceipt : SpatialPowerObligation
  genericPowerReduction : SpatialPowerObligation

record ConcreteSpatialPowerCutset : Set where
  constructor concreteSpatialPowerCutset
  field
    sameObject : SpatialPowerObligation
    period : SpatialPowerObligation
    weight : SpatialPowerObligation
    reduction : SpatialPowerObligation

canonicalConcreteSpatialPowerCutset : ConcreteSpatialPowerCutset
canonicalConcreteSpatialPowerCutset =
  concreteSpatialPowerCutset
    monomialSameObjectWeld
    fullPeriodReceipt
    fullOrbitWeightReceipt
    genericPowerReduction

record SpatialPowerPromotionReceipt : Set where
  constructor spatialPowerPromotionReceipt
  field
    sameObjectOwned : Bool
    periodOwned : Bool
    weightOwned : Bool
    reductionOwned : Bool

promotionAllowed : SpatialPowerPromotionReceipt → Bool
promotionAllowed (spatialPowerPromotionReceipt true true true true) = true
promotionAllowed _ = false

sourceCurrentReceipt : SpatialPowerPromotionReceipt
sourceCurrentReceipt =
  spatialPowerPromotionReceipt false false false true

sourceCurrentSpatialPowerBlocked : promotionAllowed sourceCurrentReceipt ≡ false
sourceCurrentSpatialPowerBlocked = refl


data ReverseSpatialRepair : Set where
  recoverConcreteMonomialization : ReverseSpatialRepair
  recoverConcretePeriod : ReverseSpatialRepair
  recoverConcreteOrbitWeight : ReverseSpatialRepair
  reproveGenericPowerTheorem : ReverseSpatialRepair

preferredReverseSpatialRepairs : List ReverseSpatialRepair
preferredReverseSpatialRepairs =
  recoverConcreteMonomialization ∷
  recoverConcretePeriod ∷
  recoverConcreteOrbitWeight ∷
  []
