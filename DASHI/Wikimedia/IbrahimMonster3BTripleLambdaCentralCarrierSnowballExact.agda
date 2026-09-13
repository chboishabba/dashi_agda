module DASHI.Wikimedia.IbrahimMonster3BTripleLambdaCentralCarrierSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact as Supplement
import DASHI.Wikimedia.IbrahimMonster3BT1WordT2ScalarRoutingSnowballExact as Routing

------------------------------------------------------------------------
-- TRIPLE MODEL / LAMBDA-CENTRE REFINEMENT
--
-- Barraclough--Wilson Section 3.2 writes every element of the main group
-- 3^(1+12):6.Suz:2 as a triple
--
--   (g , v , lambda),   lambda in F3,
--
-- represented by the displayed 38-dimensional block matrix.  The new normal
-- subgroup coordinate is literally lambda.  Hence over g = identity and
-- v = zero, the central C3 is represented by the three lambda translations
-- 0,1,2.  Choosing which nonzero translation is named t2 is an orientation;
-- inversion swaps 1 and 2.
--
-- The primary-derived supplementary maps additionally show that main classes
-- 18,19,20 have the same images in the quotients which forget lambda:
-- they are the three lifts over one underlying (g,v) class.  Class 20 is the
-- lift killed by qGtoN3B.
--
-- CRITICAL: the surviving public table data do not pay the historical mapping
-- of ROW NUMBER to lambda value.  In particular we do NOT assert
--   class18=lambda0, class19=lambda1, class20=lambda2
-- without makewords.mag labels or an equivalent same-object receipt.
------------------------------------------------------------------------

barracloughWilson : Attribution.AttributedSource
barracloughWilson = Attribution.mkDOISource
  "R. W. Barraclough; R. A. Wilson"
  "The Character Table of a Maximal Subgroup of the Monster"
  "LMS Journal of Computation and Mathematics 10, 161-175"
  "2007"
  "10.1112/S1461157000001352"
  "https://doi.org/10.1112/S1461157000001352"
  Attribution.academicArticleSource
  "primary source for the 38-dimensional triple model (g,v,lambda), lambda in F3, its block matrix, and quotient-map computation on class labels"
  Attribution.publicAttribution

paperAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilson

------------------------------------------------------------------------
-- Exact F3 central carrier, represented minimally rather than importing a new
-- finite-field architecture.
------------------------------------------------------------------------

data Lambda3 : Set where
  lambda0 lambda1 lambda2 : Lambda3

invertLambda : Lambda3 → Lambda3
invertLambda lambda0 = lambda0
invertLambda lambda1 = lambda2
invertLambda lambda2 = lambda1

invertLambdaInvolutive : (x : Lambda3) → invertLambda (invertLambda x) ≡ x
invertLambdaInvolutive lambda0 = refl
invertLambdaInvolutive lambda1 = refl
invertLambdaInvolutive lambda2 = refl

nonzeroLambdaDistinct : lambda1 ≡ lambda2 → ⊥
nonzeroLambdaDistinct ()

record MainTripleCoordinate : Set₁ where
  constructor main-triple-coordinate
  field
    GCoordinate : Set
    VCoordinate : Set
    lambdaCoordinate : Lambda3
open MainTripleCoordinate public

record ExtraspecialCentralLambdaCarrier : Set where
  constructor extraspecial-central-lambda-carrier
  field
    identityLambda : Lambda3
    firstNonidentityLambda : Lambda3
    secondNonidentityLambda : Lambda3
    identityIsZero : identityLambda ≡ lambda0
    firstIsOne : firstNonidentityLambda ≡ lambda1
    secondIsTwo : secondNonidentityLambda ≡ lambda2
    inversionSwapsNonidentity : invertLambda firstNonidentityLambda ≡ secondNonidentityLambda
open ExtraspecialCentralLambdaCarrier public

canonicalExtraspecialCentralLambdaCarrier : ExtraspecialCentralLambdaCarrier
canonicalExtraspecialCentralLambdaCarrier = extraspecial-central-lambda-carrier
  lambda0 lambda1 lambda2 refl refl refl refl

------------------------------------------------------------------------
-- Primary supplementary row family.
------------------------------------------------------------------------

record ThreeLiftRowFamily : Set where
  constructor three-lift-row-family
  field
    firstMainClass : Nat
    secondMainClass : Nat
    thirdMainClass : Nat
    sameUnderlyingVGClass : Bool
    sameOuterSuzukiClass : Bool
    n3bKernelClass : Nat
    n3bKernelClassIsThird : n3bKernelClass ≡ thirdMainClass
    rowToLambdaOrderingPaid : Bool
open ThreeLiftRowFamily public

primaryThreeLiftRowFamily : ThreeLiftRowFamily
primaryThreeLiftRowFamily = three-lift-row-family
  18 19 20
  true true
  20 refl
  false

------------------------------------------------------------------------
-- Conditional ordering surface: useful for search, never theorem promotion.
------------------------------------------------------------------------

record CandidateRowLambdaOrdering : Set where
  constructor candidate-row-lambda-ordering
  field
    class18Candidate : Lambda3
    class19Candidate : Lambda3
    class20Candidate : Lambda3
    historicalMakewordsOrderingReceipt : Set
open CandidateRowLambdaOrdering public

------------------------------------------------------------------------
-- Attribution/navigation coordinates.
------------------------------------------------------------------------

record TripleLambdaExternalCoordinates : Set where
  constructor triple-lambda-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasLambdaOrderingAuthority : Bool
open TripleLambdaExternalCoordinates public

canonicalTripleLambdaExternalCoordinates : TripleLambdaExternalCoordinates
canonicalTripleLambdaExternalCoordinates = triple-lambda-external-coordinates
  "Q1055807"
  "Q1057968"
  "512.22"
  "512.23"
  "not applicable: lambda lift ordering is representation/class-table provenance, not an integer sequence"
  false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data ThreeRowsCreateLambdaOrder : Set where
data ConsecutiveRowsCreateLexicographicOrder : Set where
data ClassTwentyCreatesLambdaTwo : Set where
data LambdaTwoCreatesInverseDiagonalName : Set where
data QidCreatesRowOrdering : Set where
data DeweyCreatesRowOrdering : Set where
data OeisCreatesRowOrdering : Set where

threeRowsDoNotCreateLambdaOrder : ThreeRowsCreateLambdaOrder → ⊥
threeRowsDoNotCreateLambdaOrder ()

consecutiveRowsDoNotCreateLexicographicOrder : ConsecutiveRowsCreateLexicographicOrder → ⊥
consecutiveRowsDoNotCreateLexicographicOrder ()

classTwentyDoesNotCreateLambdaTwo : ClassTwentyCreatesLambdaTwo → ⊥
classTwentyDoesNotCreateLambdaTwo ()

lambdaTwoDoesNotCreateDiagonalName : LambdaTwoCreatesInverseDiagonalName → ⊥
lambdaTwoDoesNotCreateDiagonalName ()

qidDoesNotCreateOrdering : QidCreatesRowOrdering → ⊥
qidDoesNotCreateOrdering ()

deweyDoesNotCreateOrdering : DeweyCreatesRowOrdering → ⊥
deweyDoesNotCreateOrdering ()

oeisDoesNotCreateOrdering : OeisCreatesRowOrdering → ⊥
oeisDoesNotCreateOrdering ()

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record TripleLambdaFrontier : Set where
  constructor triple-lambda-frontier
  field
    tripleModelSourcePaid : Bool
    lambdaInF3SourcePaid : Bool
    centralLambdaCarrierPaidUpToOrientation : Bool
    t2SubgroupPaidUpToInversion : Bool
    classes18To20ThreeLiftFamilyPaid : Bool
    class20QuotientKernelPaid : Bool
    rowToLambdaOrderingPaid : Bool
    class20RelativeSignPaid : Bool
    nextResidual : String
open TripleLambdaFrontier public

currentTripleLambdaFrontier : TripleLambdaFrontier
currentTripleLambdaFrontier = triple-lambda-frontier
  true true true true true true
  false false
  "recover the historical makewords.mag (i,j,k) labels, another surviving class-label ledger, or an exact word/matrix receipt that maps main classes 18,19,20 to lambda=0,1,2. The primary paper already pays that these are the three lambda lifts and the supplement pays that class 20 is killed by qGtoN3B. Do not assume row 18/19/20 corresponds to lambda 0/1/2 merely from consecutiveness. Once class20's lambda coordinate is paid, combine it with the literal Suzuki t1=[C,DCD]^7 and the chosen t2 orientation to state the diagonal kernel relative sign."

supplementFrontier : Supplement.PrimarySupplementKernelFrontier
supplementFrontier = Supplement.currentPrimarySupplementKernelFrontier

routingFrontier : Routing.T1T2RoutingFrontier
routingFrontier = Routing.currentT1T2RoutingFrontier
