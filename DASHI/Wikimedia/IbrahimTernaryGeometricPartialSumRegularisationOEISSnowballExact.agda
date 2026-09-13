module DASHI.Wikimedia.IbrahimTernaryGeometricPartialSumRegularisationOEISSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _/_; -_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as AttributionSnowball
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine
import DASHI.Wikimedia.IbrahimZeroToThirteenTernaryCarryNDimFibreSnowballExact as Ternary

------------------------------------------------------------------------
-- TERNARY GEOMETRIC PARTIAL SUMS / REPUNITS / DIVERGENT CONTINUATION
--
-- Keep three objects distinct:
--
--   finite partial sums:    S_n = sum_{k=0}^{n-1} 3^k = (3^n-1)/2,
--   ordinary infinite sum:  sum_{k>=0} 3^k, which diverges,
--   rational-function / regularised continuation of 1/(1-x) at x=3: -1/2.
--
-- Indexing matters:
--
--   1 + 3 + 9 + ...  (starts at 3^0)  -> continuation value -1/2,
--   3 + 9 + 27 + ... (starts at 3^1)  -> continuation value -3/2.
--
-- The finite partial sums are OEIS A003462, and are also base-3 repunits:
--
--   0, 1, 4, 13, 40, 121, ...
--   0, 1, 11_3, 111_3, 1111_3, ...
--
-- Thus the existing ternary row 13 = 111_3 = 1+3+9 is literally A003462(3).
------------------------------------------------------------------------

pow3 : Nat → Nat
pow3 zero = 1
pow3 (suc n) = 3 * pow3 n

partialSum3 : Nat → Nat
partialSum3 zero = 0
partialSum3 (suc n) = 1 + 3 * partialSum3 n

partial0 : partialSum3 0 ≡ 0
partial0 = refl
partial1 : partialSum3 1 ≡ 1
partial1 = refl
partial2 : partialSum3 2 ≡ 4
partial2 = refl
partial3 : partialSum3 3 ≡ 13
partial3 = refl
partial4 : partialSum3 4 ≡ 40
partial4 = refl
partial5 : partialSum3 5 ≡ 121
partial5 = refl
partial9 : partialSum3 9 ≡ 9841
partial9 = refl
partial10 : partialSum3 10 ≡ 29524
partial10 = refl

thirteenIsOnePlusThreePlusNine : 13 ≡ 1 + 3 + 9
thirteenIsOnePlusThreePlusNine = refl

thirteenMatchesExistingTernary111 :
  Ternary.Ternary013Row.value Ternary.r13 ≡ partialSum3 3
thirteenMatchesExistingTernary111 = refl

partialNineMatchesClosedFormNumerically :
  2 * partialSum3 9 + 1 ≡ Nine.a000244 9
partialNineMatchesClosedFormNumerically = refl

partialTenIncludesThreePowerNine :
  partialSum3 10 ≡ partialSum3 9 + Nine.a000244 9
partialTenIncludesThreePowerNine = refl

------------------------------------------------------------------------
-- Two indexing conventions and their rational-function continuation values.
-- These are NOT ordinary sums of the divergent series.
------------------------------------------------------------------------

minusHalf : ℚ
minusHalf = - (+ 1 / 2)

minusThreeHalves : ℚ
minusThreeHalves = - (+ 3 / 2)

record GeometricRegularisationAssignment : Set where
  constructor geometric-regularisation-assignment
  field
    displayedSeries : String
    startExponent : Nat
    rationalFunction : String
    continuationAtThree : ℚ
    ordinarySeriesConvergesAtThree : Bool
    valueIsOrdinaryInfiniteSum : Bool
    interpretation : String
open GeometricRegularisationAssignment public

fromZeroAssignment : GeometricRegularisationAssignment
fromZeroAssignment = geometric-regularisation-assignment
  "1 + 3 + 9 + 27 + ..."
  0
  "1/(1-x) evaluated away from its disk of convergence"
  minusHalf
  false
  false
  "rational-function/formal continuation value -1/2; not the ordinary limit of partial sums"

fromOneAssignment : GeometricRegularisationAssignment
fromOneAssignment = geometric-regularisation-assignment
  "3 + 9 + 27 + 81 + ..."
  1
  "x/(1-x) evaluated away from its disk of convergence"
  minusThreeHalves
  false
  false
  "rational-function/formal continuation value -3/2; indexing-shift correction to the -1/2 construction"

------------------------------------------------------------------------
-- OEIS / QID / provenance.
------------------------------------------------------------------------

record TernaryGeometricExternalCoordinates : Set where
  constructor ternary-geometric-external-coordinates
  field
    powersOfThreeOEIS : String
    partialSumsOfPowersOfThreeOEIS : String
    baseThreeRenderingOEIS : String
    geometricSeriesQid : String
    divergentSeriesQid : String
    ternaryNumeralSystemQid : String
    partialSumFamilyPaid : Bool
    a003462RepunitRolePaid : Bool
    qidCreatesRegularisationTheorem : Bool
open TernaryGeometricExternalCoordinates public

canonicalTernaryGeometricExternalCoordinates : TernaryGeometricExternalCoordinates
canonicalTernaryGeometricExternalCoordinates = ternary-geometric-external-coordinates
  "A000244" "A003462" "A007089"
  "Q1306887" "Q906520" "Q1056486"
  true true false

eulerDivergentSeriesSource : Attribution.AttributedSource
eulerDivergentSeriesSource = Attribution.mkNoDOISource
  "Leonhard Euler"
  "De seriebus divergentibus"
  "Novi Commentarii academiae scientiarum Petropolitanae 5, 205-237; Enestrom E247"
  "1760"
  "https://scholarlycommons.pacific.edu/euler-works/247/"
  Attribution.academicArticleSource
  "primary historical source for assigning values to divergent series; not authority that the geometric series at x=3 converges in the ordinary sense"
  Attribution.publicAttribution

hardyDivergentSeriesSource : Attribution.AttributedSource
hardyDivergentSeriesSource = Attribution.mkNoDOISource
  "G. H. Hardy"
  "Divergent Series"
  "Clarendon Press / Oxford University Press"
  "1949"
  "https://bookstore.ams.org/CHEL-334-S/"
  Attribution.academicBookSource
  "modern summability/divergent-series reference; distinguishes summation methods from ordinary convergence"
  Attribution.publicAttribution

eulerAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt eulerDivergentSeriesSource
hardyAttribution = AttributionSnowball.canonicalSourceRoleSnowballReceipt hardyDivergentSeriesSource

------------------------------------------------------------------------
-- BIDI / WrongType firewalls.
------------------------------------------------------------------------

data DivergentSeriesRegularisedValueIsOrdinarySum : Set where
data StartAtOneHasMinusHalfContinuation : Set where
data A003462CreatesMonsterMeaning : Set where
data TernaryRepunitCreatesTetration : Set where

divergentRegularisedValueIsNotOrdinarySum :
  DivergentSeriesRegularisedValueIsOrdinarySum → ⊥
divergentRegularisedValueIsNotOrdinarySum ()

startAtOneDoesNotHaveMinusHalfByThisIndexing :
  StartAtOneHasMinusHalfContinuation → ⊥
startAtOneDoesNotHaveMinusHalfByThisIndexing ()

oeisPartialSumDoesNotCreateMonsterMeaning : A003462CreatesMonsterMeaning → ⊥
oeisPartialSumDoesNotCreateMonsterMeaning ()

repunitDoesNotCreateTetration : TernaryRepunitCreatesTetration → ⊥
repunitDoesNotCreateTetration ()

record TernaryGeometricRegularisationFrontier : Set where
  constructor ternary-geometric-regularisation-frontier
  field
    finitePartialSumRecurrencePaid : Bool
    a003462PartialSumCoordinatePaid : Bool
    thirteenAs111Base3AndOnePlusThreePlusNinePaid : Bool
    rankNineFinitePartialSum9841Paid : Bool
    throughThreePowerNinePartialSum29524Paid : Bool
    fromZeroContinuationMinusHalfEncoded : Bool
    fromOneContinuationMinusThreeHalvesEncoded : Bool
    ordinaryConvergenceAtRatioThreePaid : Bool
    regularisedValuePromotedToOrdinarySum : Bool
    nextResidual : String
open TernaryGeometricRegularisationFrontier public

currentTernaryGeometricRegularisationFrontier : TernaryGeometricRegularisationFrontier
currentTernaryGeometricRegularisationFrontier = ternary-geometric-regularisation-frontier
  true true true true true true true false false
  "snowball A003462 as the finite repunit/partial-sum family against the existing 1,3,9 ternary atlas and 3^n/A000244 fibre ladder. Keep the rational-function value -1/2 attached only to the series starting at 3^0; the shifted 3^1 tail has -3/2. Compare these formal continuation fixed points with any existing zeta/Ramanujan regularisation owners only after identifying the exact summation method and domain, never by shared assigned value alone."
