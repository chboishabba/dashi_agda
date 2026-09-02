module DASHI.Economics.FinancialPhysicalBackingMarketControlExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FINANCIAL REPRESENTATION / PHYSICAL UNDERLYING CONTROL PATTERN
--
-- Cross-pollinated from the paper-gold discussion without hard-coding one
-- jurisdiction or commodity.  A financial representation may require a
-- backing receipt tied to the same literal underlying exposure.  Restricting
-- one financial channel does not imply banning physical ownership or fixing
-- the commodity price.
------------------------------------------------------------------------

record BackedFinancialMarketSurface : Set₁ where
  constructor backedFinancialMarketSurface
  field
    Commodity : Set
    FinancialClaim : Set
    PhysicalHolding : Set
    Actor : Set
    RuleRegime : Set

    claimCommodity : FinancialClaim → Commodity
    holdingCommodity : PhysicalHolding → Commodity
    ownsClaim : Actor → FinancialClaim → Set
    ownsPhysical : Actor → PhysicalHolding → Set
    claimAllowed : RuleRegime → FinancialClaim → Set
    physicalAllowed : RuleRegime → PhysicalHolding → Set

    reference : String

open BackedFinancialMarketSurface public

record SameUnderlyingBacking
    (surface : BackedFinancialMarketSurface)
    (claim : FinancialClaim surface)
    (holding : PhysicalHolding surface) : Set where
  constructor sameUnderlyingBacking
  field
    sameCommodity :
      claimCommodity surface claim ≡ holdingCommodity surface holding
    backingReference : String

open SameUnderlyingBacking public

record BackingReceipt
    (surface : BackedFinancialMarketSurface)
    (claim : FinancialClaim surface) : Set₁ where
  constructor backingReceipt
  field
    backingHolding : PhysicalHolding surface
    sameUnderlying : SameUnderlyingBacking surface claim backingHolding
    reserveOrBackingReference : String

open BackingReceipt public

------------------------------------------------------------------------
-- Channels remain distinct.  A regulator may constrain a paper/derivative
-- channel while leaving a physical or accumulation channel available.
------------------------------------------------------------------------

data ExposureChannel : Set where
  physicalChannel
  accumulationChannel
  fullyFundedFinancialChannel
  leveragedFinancialChannel
  deferredFinancialChannel
  : ExposureChannel

record ChannelPolicy : Set where
  constructor channelPolicy
  field
    channel : ExposureChannel
    available : Bool
    policyReference : String

open ChannelPolicy public

record SelectiveFinancialRetrenchment : Set where
  constructor selectiveFinancialRetrenchment
  field
    financialChannel : ExposureChannel
    financialUnavailable : Bool
    financialUnavailableIsTrue : financialUnavailable ≡ true
    physicalChannelAvailable : Bool
    physicalChannelAvailableIsTrue : physicalChannelAvailable ≡ true
    retrenchmentReference : String

open SelectiveFinancialRetrenchment public

------------------------------------------------------------------------
-- Backing is a same-object coupling requirement, not an assertion that the
-- financial representation and physical carrier are identical objects.
------------------------------------------------------------------------

record FinancialPhysicalBackingBoundary : Set where
  constructor financialPhysicalBackingBoundary
  field
    financialClaimIsPhysicalHolding : Bool
    financialClaimIsPhysicalHoldingIsFalse :
      financialClaimIsPhysicalHolding ≡ false

    paperRestrictionImpliesPhysicalBan : Bool
    paperRestrictionImpliesPhysicalBanIsFalse :
      paperRestrictionImpliesPhysicalBan ≡ false

    paperRestrictionSetsCommodityPrice : Bool
    paperRestrictionSetsCommodityPriceIsFalse :
      paperRestrictionSetsCommodityPrice ≡ false

    sameUnderlyingImpliesSameObject : Bool
    sameUnderlyingImpliesSameObjectIsFalse :
      sameUnderlyingImpliesSameObject ≡ false

    backingReceiptProvesAllMarketRiskAbsent : Bool
    backingReceiptProvesAllMarketRiskAbsentIsFalse :
      backingReceiptProvesAllMarketRiskAbsent ≡ false

canonicalFinancialPhysicalBackingBoundary : FinancialPhysicalBackingBoundary
canonicalFinancialPhysicalBackingBoundary =
  financialPhysicalBackingBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
