module DASHI.Physics.Closure.BetaCriticalReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.UniformBoundStrongCouplingReceipt as Bound

data BetaCriticalComparison : Set where
  suTwoFourDimensionalMonteCarloBetaCritical :
    BetaCriticalComparison

  carrierBetaAlphaOneDeepStrongCoupling :
    BetaCriticalComparison

  standardContinuumRequiresBetaToInfinity :
    BetaCriticalComparison

  carrierFixedBetaNotStandardTrajectory :
    BetaCriticalComparison

canonicalBetaCriticalComparisons :
  List BetaCriticalComparison
canonicalBetaCriticalComparisons =
  suTwoFourDimensionalMonteCarloBetaCritical
  ∷ carrierBetaAlphaOneDeepStrongCoupling
  ∷ standardContinuumRequiresBetaToInfinity
  ∷ carrierFixedBetaNotStandardTrajectory
  ∷ []

data BetaCriticalPromotion : Set where

betaCriticalPromotionImpossibleHere :
  BetaCriticalPromotion →
  ⊥
betaCriticalPromotionImpossibleHere ()

betaCriticalReferenceLabel : String
betaCriticalReferenceLabel =
  "SU(2) four-dimensional lattice gauge theory has beta_crit near 2.3 in numerical strong/weak-coupling crossover diagnostics"

carrierBetaComparisonLabel : String
carrierBetaComparisonLabel =
  "carrier beta = alpha1 ~= 0.04124 << beta_crit, so the carrier point is deeply strong-coupled"

continuumTrajectoryLabel : String
continuumTrajectoryLabel =
  "standard Wilson continuum limit requires beta -> infinity as lattice spacing -> 0"

record BetaCriticalReceipt : Setω where
  field
    uniformBoundReceipt :
      Bound.UniformBoundStrongCouplingReceipt

    strongCouplingL2Partial :
      Bound.ymL2PartiallyInhabited uniformBoundReceipt ≡ true

    uniformBoundKeepsClayFalse :
      Bound.clayYangMillsPromoted uniformBoundReceipt ≡ false

    betaCriticalReference :
      String

    betaCriticalReferenceIsCanonical :
      betaCriticalReference ≡ betaCriticalReferenceLabel

    carrierBetaComparison :
      String

    carrierBetaComparisonIsCanonical :
      carrierBetaComparison ≡ carrierBetaComparisonLabel

    continuumTrajectory :
      String

    continuumTrajectoryIsCanonical :
      continuumTrajectory ≡ continuumTrajectoryLabel

    carrierDeepStrongCoupling :
      Bool

    carrierDeepStrongCouplingIsTrue :
      carrierDeepStrongCoupling ≡ true

    strongCouplingExpansionValidAtCarrierBeta :
      Bool

    strongCouplingExpansionValidAtCarrierBetaIsTrue :
      strongCouplingExpansionValidAtCarrierBeta ≡ true

    carrierBetaNotOnRGTrajectory :
      Bool

    carrierBetaNotOnRGTrajectoryIsTrue :
      carrierBetaNotOnRGTrajectory ≡ true

    standardWilsonContinuumLimitRequiresBetaToInfinity :
      Bool

    standardWilsonContinuumLimitRequiresBetaToInfinityIsTrue :
      standardWilsonContinuumLimitRequiresBetaToInfinity ≡ true

    continuumLimitClosed :
      Bool

    continuumLimitClosedIsFalse :
      continuumLimitClosed ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    terminalClayClaimPromoted :
      Bool

    terminalClayClaimPromotedIsFalse :
      terminalClayClaimPromoted ≡ false

    comparisons :
      List BetaCriticalComparison

    comparisonsAreCanonical :
      comparisons ≡ canonicalBetaCriticalComparisons

    promotionFlags :
      List BetaCriticalPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

open BetaCriticalReceipt public

canonicalBetaCriticalReceipt :
  BetaCriticalReceipt
canonicalBetaCriticalReceipt =
  record
    { uniformBoundReceipt =
        Bound.canonicalUniformBoundStrongCouplingReceipt
    ; strongCouplingL2Partial =
        refl
    ; uniformBoundKeepsClayFalse =
        refl
    ; betaCriticalReference =
        betaCriticalReferenceLabel
    ; betaCriticalReferenceIsCanonical =
        refl
    ; carrierBetaComparison =
        carrierBetaComparisonLabel
    ; carrierBetaComparisonIsCanonical =
        refl
    ; continuumTrajectory =
        continuumTrajectoryLabel
    ; continuumTrajectoryIsCanonical =
        refl
    ; carrierDeepStrongCoupling =
        true
    ; carrierDeepStrongCouplingIsTrue =
        refl
    ; strongCouplingExpansionValidAtCarrierBeta =
        true
    ; strongCouplingExpansionValidAtCarrierBetaIsTrue =
        refl
    ; carrierBetaNotOnRGTrajectory =
        true
    ; carrierBetaNotOnRGTrajectoryIsTrue =
        refl
    ; standardWilsonContinuumLimitRequiresBetaToInfinity =
        true
    ; standardWilsonContinuumLimitRequiresBetaToInfinityIsTrue =
        refl
    ; continuumLimitClosed =
        false
    ; continuumLimitClosedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; terminalClayClaimPromoted =
        false
    ; terminalClayClaimPromotedIsFalse =
        refl
    ; comparisons =
        canonicalBetaCriticalComparisons
    ; comparisonsAreCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    }

betaCriticalKeepsClayFalse :
  clayYangMillsPromoted canonicalBetaCriticalReceipt ≡ false
betaCriticalKeepsClayFalse =
  refl
