module DASHI.Analysis.NonArchimedeanTwistedBlockReductionBidiExact where

------------------------------------------------------------------------
-- Twisted-block reduction BIDI boundary.
--
-- Source audit of `TwistedBlockPow.lean` shows a precise split:
--
--   TwistedBlockPowConjecture n
--     = statement about the concrete spatial `twistedDirMatrix`
--
-- while
--
--   twisted_block_pow_of_monomial_scale_n
--     = unconditional reduction theorem for an arbitrary monomialMatrix π w,
--       provided the full-period and full-orbit-weight hypotheses are supplied.
--
-- Therefore the generic power theorem is strong and reusable, but it is not
-- itself a proof of the concrete spatial conjecture.  The reverse compiler for
-- the spatial theorem must recover an explicit same-object monomialization plus
-- the required h_cycle/h_weight receipts for that very operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

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

------------------------------------------------------------------------
-- Reverse direction: the generic reduction is already owned, so proof search
-- must not spend effort reproving matrix powers.  It should reopen the missing
-- same-object/period/weight producers instead.
------------------------------------------------------------------------

data ReverseSpatialRepair : Set where
  recoverConcreteMonomialization : ReverseSpatialRepair
  recoverConcretePeriod : ReverseSpatialRepair
  recoverConcreteOrbitWeight : ReverseSpatialRepair
  reproveGenericPowerTheorem : ReverseSpatialRepair

preferredReverseSpatialRepairs :
  ReverseSpatialRepair × ReverseSpatialRepair × ReverseSpatialRepair
preferredReverseSpatialRepairs =
  recoverConcreteMonomialization ,
  (recoverConcretePeriod , recoverConcreteOrbitWeight)
