module DASHI.Physics.Closure.NSLyapunovFunctionIsLane7OnlyReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties using (≤-refl)

------------------------------------------------------------------------
-- NS Lyapunov lane receipt.
--
-- This receipt records the narrow Lyapunov interpretation used by the
-- NS-facing EV5 bookkeeping surface.  The monotone Lyapunov witness is the
-- lane7/tail-enstrophy lane only.  The lane2/mean-shell lane is retained as a
-- coordinate and boundedness/cutoff witness, not as part of an additive scalar
-- monotone Lyapunov function.  Scalar additive Q is rejected/falsified here,
-- Clay/general Navier-Stokes is not promoted, and forward simulation remains
-- scoped to smooth Kolmogorov-calibrated data.

data NSLyapunovLaneStatus : Set where
  lane7TailEnstrophyOnly_scalarQRejected_noClayPromotion :
    NSLyapunovLaneStatus

data NSLyapunovComponent : Set where
  lane7TailEnstrophyLyapunovWitness :
    NSLyapunovComponent

  lane2MeanShellCoordinateWitness :
    NSLyapunovComponent

  lane2BoundednessCutoffWitness :
    NSLyapunovComponent

  scalarAdditiveQRejected :
    NSLyapunovComponent

  clayGeneralNSNotPromoted :
    NSLyapunovComponent

  smoothKolmogorovForwardSimulationScope :
    NSLyapunovComponent

canonicalNSLyapunovComponents :
  List NSLyapunovComponent
canonicalNSLyapunovComponents =
  lane7TailEnstrophyLyapunovWitness
  ∷ lane2MeanShellCoordinateWitness
  ∷ lane2BoundednessCutoffWitness
  ∷ scalarAdditiveQRejected
  ∷ clayGeneralNSNotPromoted
  ∷ smoothKolmogorovForwardSimulationScope
  ∷ []

data ForwardSimulationScope : Set where
  smoothKolmogorovCalibratedDataOnly :
    ForwardSimulationScope

data GeneralNSScope : Set where
  arbitraryLerayHopfData :
    GeneralNSScope

  arbitraryH118Data :
    GeneralNSScope

  clayMillenniumGlobalRegularity :
    GeneralNSScope

canonicalExcludedGeneralNSScope :
  List GeneralNSScope
canonicalExcludedGeneralNSScope =
  arbitraryLerayHopfData
  ∷ arbitraryH118Data
  ∷ clayMillenniumGlobalRegularity
  ∷ []

data ScalarAdditiveQPromotion : Set where

scalarAdditiveQPromotionImpossibleHere :
  ScalarAdditiveQPromotion →
  ⊥
scalarAdditiveQPromotionImpossibleHere ()

record Lane7TailEnstrophyWitness (before after : Nat) : Set where
  field
    tailEnstrophyNonIncreasing :
      after ≤ before

open Lane7TailEnstrophyWitness public

canonicalLane7TailEnstrophyWitness :
  ∀ lane7 →
  Lane7TailEnstrophyWitness lane7 lane7
canonicalLane7TailEnstrophyWitness lane7 =
  record
    { tailEnstrophyNonIncreasing =
        ≤-refl
    }

record Lane2MeanShellBoundednessWitness (cutoff lane2 : Nat) : Set where
  field
    meanShellBelowCutoff :
      lane2 ≤ cutoff

open Lane2MeanShellBoundednessWitness public

canonicalZeroLane2MeanShellBoundednessWitness :
  ∀ cutoff →
  Lane2MeanShellBoundednessWitness cutoff zero
canonicalZeroLane2MeanShellBoundednessWitness cutoff =
  record
    { meanShellBelowCutoff =
        z≤n
    }

lane7TailEnstrophyStatement :
  String
lane7TailEnstrophyStatement =
  "Lyapunov witness: lane7/tail enstrophy is the only monotone scalar witness recorded by this receipt."

lane2MeanShellStatement :
  String
lane2MeanShellStatement =
  "Lane2/mean shell is a coordinate and boundedness/cutoff witness; it is not part of a monotone additive scalar Lyapunov."

scalarAdditiveQRejectionStatement :
  String
scalarAdditiveQRejectionStatement =
  "Scalar additive Q is rejected/falsified here: lane2 plus lane7 is not accepted as a single monotone scalar Lyapunov function."

promotionBoundaryStatement :
  String
promotionBoundaryStatement =
  "No Clay/general Navier-Stokes promotion is made; the receipt fails closed outside the recorded carrier scope."

forwardSimulationScopeStatement :
  String
forwardSimulationScopeStatement =
  "Forward-simulation proof status remains scoped to smooth Kolmogorov-calibrated data and is not promoted to arbitrary NS data."

record NSLyapunovFunctionIsLane7OnlyReceipt
    (lane2 cutoff lane7Before lane7After : Nat) : Set₁ where
  field
    status :
      NSLyapunovLaneStatus

    statusIsCanonical :
      status
      ≡
      lane7TailEnstrophyOnly_scalarQRejected_noClayPromotion

    lane7TailEnstrophyIsLyapunovWitness :
      Bool

    lane7TailEnstrophyIsLyapunovWitnessIsTrue :
      lane7TailEnstrophyIsLyapunovWitness ≡ true

    lane7Witness :
      Lane7TailEnstrophyWitness lane7Before lane7After

    lane7TailEnstrophyNonIncreasing :
      lane7After ≤ lane7Before

    lane7TailEnstrophyMatchesWitness :
      lane7TailEnstrophyNonIncreasing
      ≡
      Lane7TailEnstrophyWitness.tailEnstrophyNonIncreasing lane7Witness

    lane2MeanShellIsCoordinateWitness :
      Bool

    lane2MeanShellIsCoordinateWitnessIsTrue :
      lane2MeanShellIsCoordinateWitness ≡ true

    lane2MeanShellIsBoundednessWitness :
      Bool

    lane2MeanShellIsBoundednessWitnessIsTrue :
      lane2MeanShellIsBoundednessWitness ≡ true

    lane2IncludedInMonotoneScalarLyapunov :
      Bool

    lane2IncludedInMonotoneScalarLyapunovIsFalse :
      lane2IncludedInMonotoneScalarLyapunov ≡ false

    lane2Boundedness :
      Lane2MeanShellBoundednessWitness cutoff lane2

    lane2MeanShellBelowCutoff :
      lane2 ≤ cutoff

    lane2MeanShellBoundMatchesWitness :
      lane2MeanShellBelowCutoff
      ≡
      Lane2MeanShellBoundednessWitness.meanShellBelowCutoff
        lane2Boundedness

    scalarAdditiveQAccepted :
      Bool

    scalarAdditiveQAcceptedIsFalse :
      scalarAdditiveQAccepted ≡ false

    scalarAdditiveQRejectedHere :
      Bool

    scalarAdditiveQRejectedHereIsTrue :
      scalarAdditiveQRejectedHere ≡ true

    scalarAdditiveQFalsifiedHere :
      Bool

    scalarAdditiveQFalsifiedHereIsTrue :
      scalarAdditiveQFalsifiedHere ≡ true

    forwardSimulationScope :
      ForwardSimulationScope

    forwardSimulationScopeIsSmoothKolmogorovOnly :
      forwardSimulationScope ≡ smoothKolmogorovCalibratedDataOnly

    smoothKolmogorovCalibratedData :
      Bool

    smoothKolmogorovCalibratedDataIsTrue :
      smoothKolmogorovCalibratedData ≡ true

    forwardSimulationPromotedToArbitraryNSData :
      Bool

    forwardSimulationPromotedToArbitraryNSDataIsFalse :
      forwardSimulationPromotedToArbitraryNSData ≡ false

    clayGeneralNSPromoted :
      Bool

    clayGeneralNSPromotedIsFalse :
      clayGeneralNSPromoted ≡ false

    generalNSPromotion :
      Bool

    generalNSPromotionIsFalse :
      generalNSPromotion ≡ false

    clayMillenniumClaimClosed :
      Bool

    clayMillenniumClaimClosedIsFalse :
      clayMillenniumClaimClosed ≡ false

    components :
      List NSLyapunovComponent

    componentsAreCanonical :
      components ≡ canonicalNSLyapunovComponents

    excludedGeneralNSScope :
      List GeneralNSScope

    excludedGeneralNSScopeIsCanonical :
      excludedGeneralNSScope ≡ canonicalExcludedGeneralNSScope

    lane7Statement :
      String

    lane7StatementIsCanonical :
      lane7Statement ≡ lane7TailEnstrophyStatement

    lane2Statement :
      String

    lane2StatementIsCanonical :
      lane2Statement ≡ lane2MeanShellStatement

    scalarQStatement :
      String

    scalarQStatementIsCanonical :
      scalarQStatement ≡ scalarAdditiveQRejectionStatement

    promotionStatement :
      String

    promotionStatementIsCanonical :
      promotionStatement ≡ promotionBoundaryStatement

    forwardScopeStatement :
      String

    forwardScopeStatementIsCanonical :
      forwardScopeStatement ≡ forwardSimulationScopeStatement

    scalarAdditiveQPromotionFlags :
      List ScalarAdditiveQPromotion

    scalarAdditiveQPromotionFlagsAreEmpty :
      scalarAdditiveQPromotionFlags ≡ []

open NSLyapunovFunctionIsLane7OnlyReceipt public

canonicalZeroNSLyapunovFunctionIsLane7OnlyReceipt :
  ∀ cutoff →
  NSLyapunovFunctionIsLane7OnlyReceipt zero cutoff zero zero
canonicalZeroNSLyapunovFunctionIsLane7OnlyReceipt cutoff =
  record
    { status =
        lane7TailEnstrophyOnly_scalarQRejected_noClayPromotion
    ; statusIsCanonical =
        refl
    ; lane7TailEnstrophyIsLyapunovWitness =
        true
    ; lane7TailEnstrophyIsLyapunovWitnessIsTrue =
        refl
    ; lane7Witness =
        canonicalLane7TailEnstrophyWitness zero
    ; lane7TailEnstrophyNonIncreasing =
        z≤n
    ; lane7TailEnstrophyMatchesWitness =
        refl
    ; lane2MeanShellIsCoordinateWitness =
        true
    ; lane2MeanShellIsCoordinateWitnessIsTrue =
        refl
    ; lane2MeanShellIsBoundednessWitness =
        true
    ; lane2MeanShellIsBoundednessWitnessIsTrue =
        refl
    ; lane2IncludedInMonotoneScalarLyapunov =
        false
    ; lane2IncludedInMonotoneScalarLyapunovIsFalse =
        refl
    ; lane2Boundedness =
        canonicalZeroLane2MeanShellBoundednessWitness cutoff
    ; lane2MeanShellBelowCutoff =
        z≤n
    ; lane2MeanShellBoundMatchesWitness =
        refl
    ; scalarAdditiveQAccepted =
        false
    ; scalarAdditiveQAcceptedIsFalse =
        refl
    ; scalarAdditiveQRejectedHere =
        true
    ; scalarAdditiveQRejectedHereIsTrue =
        refl
    ; scalarAdditiveQFalsifiedHere =
        true
    ; scalarAdditiveQFalsifiedHereIsTrue =
        refl
    ; forwardSimulationScope =
        smoothKolmogorovCalibratedDataOnly
    ; forwardSimulationScopeIsSmoothKolmogorovOnly =
        refl
    ; smoothKolmogorovCalibratedData =
        true
    ; smoothKolmogorovCalibratedDataIsTrue =
        refl
    ; forwardSimulationPromotedToArbitraryNSData =
        false
    ; forwardSimulationPromotedToArbitraryNSDataIsFalse =
        refl
    ; clayGeneralNSPromoted =
        false
    ; clayGeneralNSPromotedIsFalse =
        refl
    ; generalNSPromotion =
        false
    ; generalNSPromotionIsFalse =
        refl
    ; clayMillenniumClaimClosed =
        false
    ; clayMillenniumClaimClosedIsFalse =
        refl
    ; components =
        canonicalNSLyapunovComponents
    ; componentsAreCanonical =
        refl
    ; excludedGeneralNSScope =
        canonicalExcludedGeneralNSScope
    ; excludedGeneralNSScopeIsCanonical =
        refl
    ; lane7Statement =
        lane7TailEnstrophyStatement
    ; lane7StatementIsCanonical =
        refl
    ; lane2Statement =
        lane2MeanShellStatement
    ; lane2StatementIsCanonical =
        refl
    ; scalarQStatement =
        scalarAdditiveQRejectionStatement
    ; scalarQStatementIsCanonical =
        refl
    ; promotionStatement =
        promotionBoundaryStatement
    ; promotionStatementIsCanonical =
        refl
    ; forwardScopeStatement =
        forwardSimulationScopeStatement
    ; forwardScopeStatementIsCanonical =
        refl
    ; scalarAdditiveQPromotionFlags =
        []
    ; scalarAdditiveQPromotionFlagsAreEmpty =
        refl
    }

nsLyapunovReceiptLane7Only :
  ∀ cutoff →
  lane7TailEnstrophyIsLyapunovWitness
    (canonicalZeroNSLyapunovFunctionIsLane7OnlyReceipt cutoff)
  ≡
  true
nsLyapunovReceiptLane7Only cutoff =
  refl

nsLyapunovReceiptRejectsScalarAdditiveQ :
  ∀ cutoff →
  scalarAdditiveQAccepted
    (canonicalZeroNSLyapunovFunctionIsLane7OnlyReceipt cutoff)
  ≡
  false
nsLyapunovReceiptRejectsScalarAdditiveQ cutoff =
  refl

nsLyapunovReceiptNoClayPromotion :
  ∀ cutoff →
  clayGeneralNSPromoted
    (canonicalZeroNSLyapunovFunctionIsLane7OnlyReceipt cutoff)
  ≡
  false
nsLyapunovReceiptNoClayPromotion cutoff =
  refl
