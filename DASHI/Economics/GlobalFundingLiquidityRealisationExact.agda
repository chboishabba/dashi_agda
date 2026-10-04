module DASHI.Economics.GlobalFundingLiquidityRealisationExact where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- GENERIC LATENT-LOSS / FUNDING-CONSTRAINT / FORCED-REALISATION KERNEL
--
-- This owner abstracts the common mechanism shared by bank duration books,
-- yen-funded carry positions, leveraged Treasury trades and structured AI
-- infrastructure.  A marked or latent loss is not itself a realised loss.
-- Realisation pressure requires a funding/liquidity constraint.
------------------------------------------------------------------------

isPositive : Trit → Bool
isPositive neg = false
isPositive zer = false
isPositive pos = true

record FundingState : Set where
  constructor fundingState
  field
    latentValuationLoss : Trit
    runnableFundingShock : Trit
    liquidityCapacityInsufficient : Trit
    collateralOrMarginPressure : Trit
    adequateBackstop : Trit
    forcedMonetisation : Trit
    realisedLoss : Trit
    capitalOrEquityStress : Trit

open FundingState public

fundingConstraintActive : FundingState → Bool
fundingConstraintActive s =
  isPositive (runnableFundingShock s)
  ∧ isPositive (liquidityCapacityInsufficient s)

forcedRealisationRisk : FundingState → Bool
forcedRealisationRisk s =
  isPositive (latentValuationLoss s)
  ∧ fundingConstraintActive s
  ∧ isPositive (collateralOrMarginPressure s)

data LatentLossImpliesRealisedLossPermission : Set where
data FundingShockImpliesFailurePermission : Set where
data RealisedLossImpliesFailurePermission : Set where
data TriggerAssetProvesCausationPermission : Set where

latentLossDoesNotAutoRealise :
  LatentLossImpliesRealisedLossPermission → ⊥
latentLossDoesNotAutoRealise ()

fundingShockDoesNotAutoProveFailure :
  FundingShockImpliesFailurePermission → ⊥
fundingShockDoesNotAutoProveFailure ()

realisedLossDoesNotAutoProveFailure :
  RealisedLossImpliesFailurePermission → ⊥
realisedLossDoesNotAutoProveFailure ()

triggerDoesNotAutoProveCausation :
  TriggerAssetProvesCausationPermission → ⊥
triggerDoesNotAutoProveCausation ()

record ForcedRealisationReceipt : Set where
  constructor forcedRealisationReceipt
  field
    state : FundingState
    latentLossObserved : isPositive (latentValuationLoss state) ≡ true
    fundingConstraintObserved : fundingConstraintActive state ≡ true
    collateralPressureObserved : isPositive (collateralOrMarginPressure state) ≡ true

open ForcedRealisationReceipt public

receiptClosesForcedRealisationRisk :
  (r : ForcedRealisationReceipt) →
  forcedRealisationRisk (state r) ≡ true
receiptClosesForcedRealisationRisk
  (forcedRealisationReceipt
    (fundingState pos pos pos pos backstop forced realised capital)
    refl refl refl) = refl
