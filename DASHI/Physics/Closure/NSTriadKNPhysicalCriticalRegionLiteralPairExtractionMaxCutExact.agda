module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionLiteralPairExtractionMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B / EXACT LITERAL PAIR EXTRACTION FOR THE THREE DEEP BLOCKS
--
-- The live R236 payment owner stores the three deep-only coordinates only as
-- scalars.  B1/B2/B3, however, need the original unordered physical pair rows
-- before any Bernstein/null/L2 estimate is applied.
--
-- This owner replays the SAME pair-list recursion and SAME R236 classifier and
-- retains each selected pair as a literal row carrying alpha, beta and their
-- actual high-input shell indices.  No absolute value, estimate, shell-count
-- factor, synthetic carrier or new analytic premise is introduced.
--
-- The three terminal identities are exactly:
--
--   live DFL-DFL signed block = sum literal DFL-DFL rows,
--   live DFL-DHH signed block = sum literal DFL-DHH rows,
--   live DHH-DHH signed block = sum literal DHH-DHH rows.
--
-- Thus the representation/extraction seam is closed.  The remaining B1/B2/B3
-- obligations are genuinely analytic shell payments on these rows.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_; _++_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalParabolicCriticalRegionRoutingExact as Routing
import DASHI.Physics.Closure.NSTriadKNFixedOutputCoherentCovariancePairDifferenceExact as Pair
import DASHI.Physics.Closure.NSTriadKNFixedOutputInputLaplacianCriticalRegionPairBlocksExact as Blocks
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceLiveExact as LiveOwner
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCoherentCovarianceBonyLiveExact as RateLive
import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalCriticalRegionPaymentLiveExact as Pay

F : C3.RealField _
F = Rational.rationalRealField

record LiteralPairRow : Set where
  constructor literal-pair-row
  field
    alpha beta : Physical.PhysicalTriadIncidence

open LiteralPairRow public

leftHighShell rightHighShell : LiteralPairRow → Nat
leftHighShell row = Routing.highInputShell (alpha row)
rightHighShell row = Routing.highInputShell (beta row)

rowSignedValue :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  LiteralPairRow → ℚ
rowSignedValue rate work row =
  0ℚ - Blocks.pairTerm rate work (alpha row) (beta row)

sumRows :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  List LiteralPairRow → ℚ
sumRows rate work [] = 0ℚ
sumRows rate work (row ∷ rest) =
  rowSignedValue rate work row + sumRows rate work rest

sumRowsAppend :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (left right : List LiteralPairRow) →
  sumRows rate work (left ++ right)
  ≡ sumRows rate work left + sumRows rate work right
sumRowsAppend rate work [] right = refl
sumRowsAppend rate work (row ∷ rest) right
  rewrite sumRowsAppend rate work rest right = refl

------------------------------------------------------------------------
-- One-pair selectors.  They use exactly the live R236 tags.
------------------------------------------------------------------------

dflDflRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDflRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion =
  literal-pair-row alpha beta ∷ []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = []

dflDhhRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDhhRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion =
  literal-pair-row alpha beta ∷ []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion =
  literal-pair-row alpha beta ∷ []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = []

dhhDhhRoute :
  Physical.PhysicalTriadIncidence →
  Physical.PhysicalTriadIncidence → List LiteralPairRow
dhhDhhRoute alpha beta
  with Routing.criticalRegionTag alpha | Routing.criticalRegionTag beta
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = []
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion =
  literal-pair-row alpha beta ∷ []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = []
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = []
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = []
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = []

------------------------------------------------------------------------
-- One-pair meanings against the exact Region.routePair owner.
------------------------------------------------------------------------

dflDflRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (a b : Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDflRoute a b)
  ≡ 0ℚ - Blocks.deepFarLowDeepFarLow
      (Blocks.routePair a b (Blocks.pairTerm rate work a b))
dflDflRouteMeaning rate work a b
  with Routing.criticalRegionTag a | Routing.criticalRegionTag b
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = refl
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = refl
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = refl
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = refl
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = refl
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = refl
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = refl
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = refl

dflDhhRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (a b : Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDhhRoute a b)
  ≡ 0ℚ - Blocks.deepFarLowDeepHighHigh
      (Blocks.routePair a b (Blocks.pairTerm rate work a b))
dflDhhRouteMeaning rate work a b
  with Routing.criticalRegionTag a | Routing.criticalRegionTag b
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = refl
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = refl
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = solve []
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = refl
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = refl
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = refl
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = refl
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = refl

dhhDhhRouteMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (a b : Physical.PhysicalTriadIncidence) →
  sumRows rate work (dhhDhhRoute a b)
  ≡ 0ℚ - Blocks.deepHighHighDeepHighHigh
      (Blocks.routePair a b (Blocks.pairTerm rate work a b))
dhhDhhRouteMeaning rate work a b
  with Routing.criticalRegionTag a | Routing.criticalRegionTag b
... | Routing.deepFarLowRegion | Routing.deepFarLowRegion = refl
... | Routing.deepFarLowRegion | Routing.deepHighHighRegion = refl
... | Routing.deepFarLowRegion | Routing.criticalCoreRegion = refl
... | Routing.deepHighHighRegion | Routing.deepFarLowRegion = refl
... | Routing.deepHighHighRegion | Routing.deepHighHighRegion = solve []
... | Routing.deepHighHighRegion | Routing.criticalCoreRegion = refl
... | Routing.criticalCoreRegion | Routing.deepFarLowRegion = refl
... | Routing.criticalCoreRegion | Routing.deepHighHighRegion = refl
... | Routing.criticalCoreRegion | Routing.criticalCoreRegion = refl

------------------------------------------------------------------------
-- Additivity of the three signed block projections.
------------------------------------------------------------------------

negativeDflDflAdd :
  (x y : Blocks.RegionPairBlocks) →
  0ℚ - Blocks.deepFarLowDeepFarLow (Blocks.addBlocks x y)
  ≡ (0ℚ - Blocks.deepFarLowDeepFarLow x)
    + (0ℚ - Blocks.deepFarLowDeepFarLow y)
negativeDflDflAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (a ∷ j ∷ [])

negativeDflDhhAdd :
  (x y : Blocks.RegionPairBlocks) →
  0ℚ - Blocks.deepFarLowDeepHighHigh (Blocks.addBlocks x y)
  ≡ (0ℚ - Blocks.deepFarLowDeepHighHigh x)
    + (0ℚ - Blocks.deepFarLowDeepHighHigh y)
negativeDflDhhAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (b ∷ d ∷ k ∷ m ∷ [])

negativeDhhDhhAdd :
  (x y : Blocks.RegionPairBlocks) →
  0ℚ - Blocks.deepHighHighDeepHighHigh (Blocks.addBlocks x y)
  ≡ (0ℚ - Blocks.deepHighHighDeepHighHigh x)
    + (0ℚ - Blocks.deepHighHighDeepHighHigh y)
negativeDhhDhhAdd
  (Blocks.region-pair-blocks
    (Blocks.region-row a b c) (Blocks.region-row d e f) (Blocks.region-row g h i))
  (Blocks.region-pair-blocks
    (Blocks.region-row j k l) (Blocks.region-row m n o) (Blocks.region-row p q r)) =
  solve (e ∷ n ∷ [])

------------------------------------------------------------------------
-- Complete unordered pair-row extraction.  This mirrors pairBlocks exactly.
------------------------------------------------------------------------

dflDflAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDflAgainst head [] = []
dflDflAgainst head (x ∷ xs) =
  dflDflRoute head x ++ dflDflAgainst head xs

dflDflRows : List Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDflRows [] = []
dflDflRows (head ∷ rest) = dflDflAgainst head rest ++ dflDflRows rest

dflDhhAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDhhAgainst head [] = []
dflDhhAgainst head (x ∷ xs) =
  dflDhhRoute head x ++ dflDhhAgainst head xs

dflDhhRows : List Physical.PhysicalTriadIncidence → List LiteralPairRow
dflDhhRows [] = []
dflDhhRows (head ∷ rest) = dflDhhAgainst head rest ++ dflDhhRows rest

dhhDhhAgainst :
  Physical.PhysicalTriadIncidence →
  List Physical.PhysicalTriadIncidence → List LiteralPairRow
dhhDhhAgainst head [] = []
dhhDhhAgainst head (x ∷ xs) =
  dhhDhhRoute head x ++ dhhDhhAgainst head xs

dhhDhhRows : List Physical.PhysicalTriadIncidence → List LiteralPairRow
dhhDhhRows [] = []
dhhDhhRows (head ∷ rest) = dhhDhhAgainst head rest ++ dhhDhhRows rest

------------------------------------------------------------------------
-- Exact fold meanings.
------------------------------------------------------------------------

dflDflAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDflAgainst head rest)
  ≡ 0ℚ - Blocks.deepFarLowDeepFarLow
      (Blocks.blocksAgainstHead rate work head rest)
dflDflAgainstMeaning rate work head [] = refl
dflDflAgainstMeaning rate work head (x ∷ xs) =
  trans
    (sumRowsAppend rate work (dflDflRoute head x) (dflDflAgainst head xs))
    (trans
      (cong₂ _+_
        (dflDflRouteMeaning rate work head x)
        (dflDflAgainstMeaning rate work head xs))
      (sym (negativeDflDflAdd
        (Blocks.routePair head x (Blocks.pairTerm rate work head x))
        (Blocks.blocksAgainstHead rate work head xs))))

dflDflRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDflRows items)
  ≡ 0ℚ - Blocks.deepFarLowDeepFarLow (Blocks.pairBlocks rate work items)
dflDflRowsMeaning rate work [] = refl
dflDflRowsMeaning rate work (head ∷ rest) =
  trans
    (sumRowsAppend rate work (dflDflAgainst head rest) (dflDflRows rest))
    (trans
      (cong₂ _+_
        (dflDflAgainstMeaning rate work head rest)
        (dflDflRowsMeaning rate work rest))
      (sym (negativeDflDflAdd
        (Blocks.blocksAgainstHead rate work head rest)
        (Blocks.pairBlocks rate work rest))))

dflDhhAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDhhAgainst head rest)
  ≡ 0ℚ - Blocks.deepFarLowDeepHighHigh
      (Blocks.blocksAgainstHead rate work head rest)
dflDhhAgainstMeaning rate work head [] = refl
dflDhhAgainstMeaning rate work head (x ∷ xs) =
  trans
    (sumRowsAppend rate work (dflDhhRoute head x) (dflDhhAgainst head xs))
    (trans
      (cong₂ _+_
        (dflDhhRouteMeaning rate work head x)
        (dflDhhAgainstMeaning rate work head xs))
      (sym (negativeDflDhhAdd
        (Blocks.routePair head x (Blocks.pairTerm rate work head x))
        (Blocks.blocksAgainstHead rate work head xs))))

dflDhhRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dflDhhRows items)
  ≡ 0ℚ - Blocks.deepFarLowDeepHighHigh (Blocks.pairBlocks rate work items)
dflDhhRowsMeaning rate work [] = refl
dflDhhRowsMeaning rate work (head ∷ rest) =
  trans
    (sumRowsAppend rate work (dflDhhAgainst head rest) (dflDhhRows rest))
    (trans
      (cong₂ _+_
        (dflDhhAgainstMeaning rate work head rest)
        (dflDhhRowsMeaning rate work rest))
      (sym (negativeDflDhhAdd
        (Blocks.blocksAgainstHead rate work head rest)
        (Blocks.pairBlocks rate work rest))))

dhhDhhAgainstMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (head : Physical.PhysicalTriadIncidence) →
  (rest : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dhhDhhAgainst head rest)
  ≡ 0ℚ - Blocks.deepHighHighDeepHighHigh
      (Blocks.blocksAgainstHead rate work head rest)
dhhDhhAgainstMeaning rate work head [] = refl
dhhDhhAgainstMeaning rate work head (x ∷ xs) =
  trans
    (sumRowsAppend rate work (dhhDhhRoute head x) (dhhDhhAgainst head xs))
    (trans
      (cong₂ _+_
        (dhhDhhRouteMeaning rate work head x)
        (dhhDhhAgainstMeaning rate work head xs))
      (sym (negativeDhhDhhAdd
        (Blocks.routePair head x (Blocks.pairTerm rate work head x))
        (Blocks.blocksAgainstHead rate work head xs))))

dhhDhhRowsMeaning :
  (rate work : Physical.PhysicalTriadIncidence → ℚ) →
  (items : List Physical.PhysicalTriadIncidence) →
  sumRows rate work (dhhDhhRows items)
  ≡ 0ℚ - Blocks.deepHighHighDeepHighHigh (Blocks.pairBlocks rate work items)
dhhDhhRowsMeaning rate work [] = refl
dhhDhhRowsMeaning rate work (head ∷ rest) =
  trans
    (sumRowsAppend rate work (dhhDhhAgainst head rest) (dhhDhhRows rest))
    (trans
      (cong₂ _+_
        (dhhDhhAgainstMeaning rate work head rest)
        (dhhDhhRowsMeaning rate work rest))
      (sym (negativeDhhDhhAdd
        (Blocks.blocksAgainstHead rate work head rest)
        (Blocks.pairBlocks rate work rest))))

------------------------------------------------------------------------
-- Live specialization: exact B1/B2/B3 source extraction.
------------------------------------------------------------------------

module LiveExtraction
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F)
    (output : Z3.FourierMode) where

  module Live = LiveOwner.Live physicalSystem S
  module Rate = RateLive.LiveBony physicalSystem S output
  module P = Pay.LiveRegionPayment physicalSystem S output

  items : List Physical.PhysicalTriadIncidence
  items = Live.fibre output

  b1Rows : List LiteralPairRow
  b1Rows = dflDflRows items

  b2Rows : List LiteralPairRow
  b2Rows = dflDhhRows items

  b3Rows : List LiteralPairRow
  b3Rows = dhhDhhRows items

  b1LiveBlockIsLiteralRows :
    P.deepFarLowFarLowSigned
    ≡ sumRows Rate.inputMass (Live.work output) b1Rows
  b1LiveBlockIsLiteralRows =
    sym (dflDflRowsMeaning Rate.inputMass (Live.work output) items)

  b2LiveBlockIsLiteralRows :
    P.deepFarLowDeepHighHighSigned
    ≡ sumRows Rate.inputMass (Live.work output) b2Rows
  b2LiveBlockIsLiteralRows =
    sym (dflDhhRowsMeaning Rate.inputMass (Live.work output) items)

  b3LiveBlockIsLiteralRows :
    P.deepHighHighHighHighSigned
    ≡ sumRows Rate.inputMass (Live.work output) b3Rows
  b3LiveBlockIsLiteralRows =
    sym (dhhDhhRowsMeaning Rate.inputMass (Live.work output) items)

------------------------------------------------------------------------
-- Status.  Extraction is closed; shell inequalities are deliberately not.
------------------------------------------------------------------------

b1LiteralDFLPairExtractionClosed : Bool
b1LiteralDFLPairExtractionClosed = true

b2LiteralDFLDHHPairExtractionClosed : Bool
b2LiteralDFLDHHPairExtractionClosed = true

b3LiteralDHHPairExtractionClosed : Bool
b3LiteralDHHPairExtractionClosed = true

literalRowsRetainActualShellIndices : Bool
literalRowsRetainActualShellIndices = true

literalPairExtractionIntroducesEstimate : Bool
literalPairExtractionIntroducesEstimate = false

b1LiteralShellBernsteinEstimateClosedHere : Bool
b1LiteralShellBernsteinEstimateClosedHere = false

b2PerShellSignedEstimateClosedHere : Bool
b2PerShellSignedEstimateClosedHere = false

b3IntraShellSignedL2EstimateClosedHere : Bool
b3IntraShellSignedL2EstimateClosedHere = false

clayPromotion : Bool
clayPromotion = false
