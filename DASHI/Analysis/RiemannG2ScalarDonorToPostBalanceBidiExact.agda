module DASHI.Analysis.RiemannG2ScalarDonorToPostBalanceBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Analysis.RiemannG2TargetCenteredScalarCancellationAssemblyExact as Scalar
import DASHI.Analysis.RiemannG2ExistingScalarDonorInventoryExact as Inventory
import DASHI.Analysis.RiemannG2PostScalarBalanceBreakingBidiExact as Post

------------------------------------------------------------------------
-- SCALAR DONOR -> POST-BALANCE BIDI
--
-- This owner composes the two current irreducible seams without introducing any
-- extra harmonic theory:
--
--   exact existing donor + same-object attachment
--       -> literal scalar consumer closure
--       -> explicit changed-comparison / balance-breaking receipt
--       -> strict final comparison admission.
--
-- It is useful because it prevents two opposite search mistakes:
--   * spending effort rebuilding generic harmonic infrastructure;
--   * assuming that closing the scalar leaf automatically finishes G2.
------------------------------------------------------------------------

record ScalarToPostBalanceRun
    (scalarProblem : Scalar.LiteralTargetCenteredScalarProblem)
    (comparisonProblem : Post.LiteralG2ComparisonProblem) : Set₁ where
  constructor scalar-to-post-balance-run
  field
    admittedExistingDonor : Inventory.AdmittedExistingLiteralDonor scalarProblem
    balanceBreakingReceipt : Post.BalanceBreakingReceipt comparisonProblem
    strictFinalComparison :
      Post.StrictBelow comparisonProblem
        (Post.offEnergy comparisonProblem)
        (Post.clusterMargin comparisonProblem)
    sameLiteralFinalConsumerUsed : Set

open ScalarToPostBalanceRun public

scalarClosureFromRun :
  (S : Scalar.LiteralTargetCenteredScalarProblem) ->
  (P : Post.LiteralG2ComparisonProblem) ->
  ScalarToPostBalanceRun S P ->
  Scalar.G2dScalarConsumerClosure S
scalarClosureFromRun S P run =
  Inventory.admittedDonorClosesLiteralScalarConsumer
    S
    (admittedExistingDonor run)

postScalarAdmissionFromRun :
  (S : Scalar.LiteralTargetCenteredScalarProblem) ->
  (P : Post.LiteralG2ComparisonProblem) ->
  (run : ScalarToPostBalanceRun S P) ->
  Post.PostScalarContradictionAdmission S P
postScalarAdmissionFromRun S P run =
  Post.scalarClosureAndBalanceBreakAdmitFinalComparison
    S P
    (scalarClosureFromRun S P run)
    (balanceBreakingReceipt run)
    (strictFinalComparison run)
    (sameLiteralFinalConsumerUsed run)

------------------------------------------------------------------------
-- Current frontier status.
------------------------------------------------------------------------

exactConcreteScalarDonorCurrentlyIdentified : Bool
exactConcreteScalarDonorCurrentlyIdentified =
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventory

exactConcreteScalarDonorCurrentlyIdentifiedIsFalse :
  exactConcreteScalarDonorCurrentlyIdentified ≡ false
exactConcreteScalarDonorCurrentlyIdentifiedIsFalse =
  Inventory.concreteExactLiteralDonorIdentifiedInCurrentInventoryIsFalse

record ScalarDonorToPostBalanceBoundary : Set where
  constructor scalar-donor-to-post-balance-boundary
  field
    genericHarmonicInfrastructureNeedsRebuilding : Bool
    genericHarmonicInfrastructureNeedsRebuildingIsFalse :
      genericHarmonicInfrastructureNeedsRebuilding ≡ false

    exactConcreteDonorAlreadyIdentified : Bool
    exactConcreteDonorAlreadyIdentifiedIsFalse :
      exactConcreteDonorAlreadyIdentified ≡ false

    scalarClosureAloneFinishesG2 : Bool
    scalarClosureAloneFinishesG2IsFalse :
      scalarClosureAloneFinishesG2 ≡ false

    donorPlusBalanceBreakAndStrictComparisonAdmitsPostScalarStage : Bool
    donorPlusBalanceBreakAndStrictComparisonAdmitsPostScalarStageIsTrue :
      donorPlusBalanceBreakAndStrictComparisonAdmitsPostScalarStage ≡ true

    highestAlphaReading : String

canonicalScalarDonorToPostBalanceBoundary : ScalarDonorToPostBalanceBoundary
canonicalScalarDonorToPostBalanceBoundary =
  scalar-donor-to-post-balance-boundary
    false refl
    false refl
    false refl
    true refl
    "The RH proof search now has two explicit same-object sockets, not an unbounded harmonic-analysis task: first identify or prove the exact target-centred scalar donor; then provide an explicit balance-breaking/changed-comparison receipt with the strict final comparison. Ordinary harmonic machinery stays reused, and scalar closure is not misreported as RH."
