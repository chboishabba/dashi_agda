module DASHI.Moonshine.OggSSPClimbingGymAddressDiscriminatorExact where

------------------------------------------------------------------------
-- PREDECLARED NATIVE-ADDRESS DISCRIMINATOR
--
-- The earlier mutual-nearest statistic saturates for both Ogg and non-Ogg
-- controls.  This owner therefore records a stronger experiment before looking
-- at its result.  The numerical companion works only on depth-one native
-- p-radix addresses and uses one predeclared scalar per prime:
--
--   Pearson occupancy deviation from the uniform p-cell model.
--
-- Prime size is controlled *within prime* by a deterministic boundary-shift
-- null over one cell period.  The observed occupancy deviation is standardized
-- against that prime-local null.  The Ogg-vs-control group statistic is then
-- the difference of mean standardized scores, and significance is assessed by
-- exhaustively relabelling which five of the twenty primes are controls.
--
-- This design asks a falsifiable question:
--
--   does the native radix partition retain Ogg-support information beyond
--   prime-specific occupancy geometry?
--
-- It does NOT infer a Monster mechanism from a small tail probability and does
-- not replace the rigorous phase-cell certificate programme.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record AddressDiscriminatorDesign : Set where
  constructor address-discriminator-design
  field
    depth : Nat
    perPrimeStatistic : String
    perPrimeNull : String
    standardisation : String
    groupContrast : String
    labelPermutation : String
    declaredControls : String
    multipleStatisticSearchAllowed : Bool

open AddressDiscriminatorDesign public

canonicalAddressDiscriminatorDesign : AddressDiscriminatorDesign
canonicalAddressDiscriminatorDesign =
  address-discriminator-design
    1
    "Pearson chi-square occupancy deviation over the p native depth-one cells"
    "deterministic midpoint boundary shifts over one native cell period 1/p"
    "z = (observed - shift-null mean) / shift-null population SD; zero if SD=0 and observed equals mean"
    "mean z over 15 canonical Ogg primes minus mean z over five non-Ogg controls"
    "exhaust all C(20,5)=15504 assignments of five controls; report two-sided |contrast| tail"
    "37,43,53,61,67 are the existing independent non-Ogg controls"
    false

record AddressDiscriminatorBoundary : Set where
  constructor address-discriminator-boundary
  field
    nativeRadixCellsUsed : Bool
    depthOnePrimaryStatisticPredeclared : Bool
    perPrimeShiftNullRequired : Bool
    primeLocalStandardisationRequired : Bool
    exhaustiveBalancedLabelPermutationRequired : Bool
    controlsRemainIndependentOfObservedStatistic : Bool

    sourceMpmathCacheIsRigorousZeroCertificate : Bool
    multipleStatisticSelectionPromotedConfirmatory : Bool
    smallPermutationTailProvesOggTheorem : Bool
    addressStatisticAlonePromotesMonsterMechanism : Bool
    addressStatisticProvesRiemannHypothesis : Bool

open AddressDiscriminatorBoundary public

canonicalAddressDiscriminatorBoundary : AddressDiscriminatorBoundary
canonicalAddressDiscriminatorBoundary =
  address-discriminator-boundary
    true true true true true true
    false false false false false
