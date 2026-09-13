module DASHI.Wikimedia.IbrahimMonster3BT1ComplementClass18LambdaZeroSnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimMonster3BT1WordT2ScalarRoutingSnowballExact as Routing
import DASHI.Wikimedia.IbrahimMonster3BTripleLambdaCentralCarrierSnowballExact as Lambda
import DASHI.Wikimedia.IbrahimMonster3BPrimarySupplementKernelClass20SnowballExact as Kernel

------------------------------------------------------------------------
-- t1 COMPLEMENT ANCHOR: 6.Suz.2 CLASS 3 -> MAIN CLASS 18
--
-- Bray--Wilson pays the literal standard-generator word
--
--   t1 = [ C , D C D ]^7
--
-- as a generator of the normal C3 in 3.Suz:2 / 6.Suz:2.
--
-- CTblLib's 6.Suz.2 ordinary table pays the table coordinate independently:
-- class 3 has class size two and is fixed by the square map, while class 2
-- squares to class 3.  Thus class 3 is the nonidentity normal order-three
-- class; class 2 is its order-six lift.
--
-- Barraclough--Wilson's primary supplementary map is explicitly labelled the
-- fusion of the COMPLEMENTARY 6.Suz:2 into the main group, and maps outer
-- class 3 to main class 18.  In the source-native semidirect triple model,
-- the complement is the zero-normal-coordinate section, so main class 18 is
-- the lambda=0 lift of t1.
--
-- Together with the already-paid three-lift family 18/19/20, this proves:
--
--   class18 = t1 with lambda0
--   {class19,class20} = {t1*t2, t1*t2^-1}
--   class20 is the member killed by qGtoN3B.
--
-- The orientation 19<->lambda1 / 20<->lambda2 (or vice versa) remains unpaid.
------------------------------------------------------------------------

brayWilson : Attribution.AttributedSource
brayWilson = Attribution.mkDOISource
  "John N. Bray; Robert A. Wilson"
  "Explicit representations of maximal subgroups of the Monster"
  "Journal of Algebra 300(2), 834-857"
  "2006"
  "10.1016/j.jalgebra.2005.12.017"
  "https://doi.org/10.1016/j.jalgebra.2005.12.017"
  Attribution.academicArticleSource
  "primary source for t1=[C,DCD]^7 as generator of the normal order-three Suzuki-cover subgroup"
  Attribution.publicAttribution

barracloughWilsonSupplement : Attribution.AttributedSource
barracloughWilsonSupplement = Attribution.mkNoDOISource
  "R. W. Barraclough; R. A. Wilson"
  "N3Betc supplementary fusion: complementary 6.Suz.2 -> 3^1+12:6.Suz.2"
  "author-hosted supplementary data"
  "2007"
  "https://www.rwb.me.uk/table/index.html"
  (Attribution.namedSourceKind "primary supplementary computational data")
  "primary source for complement fusion position 3 -> main position 18; no separate DOI asserted"
  Attribution.publicAttribution

ctbllibTableSource : Attribution.AttributedSource
ctbllibTableSource = Attribution.mkNoDOISource
  "Thomas Breuer; GAP CTblLib contributors; underlying ATLAS table data"
  "CTblLib ordinary character table 6.Suz.2"
  "GAP Character Table Library"
  "current table source"
  "https://www.gap-system.org/Packages/ctbllib.html"
  (Attribution.namedSourceKind "software character-table source")
  "computational identity source for the class-size and power-map signature of 6.Suz.2 class 3; not primary theorem authority"
  Attribution.publicAttribution

brayWilsonAttribution = Snowball.canonicalSourceRoleSnowballReceipt brayWilson
supplementAttribution = Snowball.canonicalSourceRoleSnowballReceipt barracloughWilsonSupplement
ctbllibAttribution = Snowball.canonicalSourceRoleSnowballReceipt ctbllibTableSource

record SuzukiT1TableCoordinate : Set where
  constructor suzuki-t1-table-coordinate
  field
    tableIdentity : String
    classPosition : Nat
    classSize : Nat
    elementOrder : Nat
    literalGeneratorWord : String
    classIdentityPaid : Bool
open SuzukiT1TableCoordinate public

canonicalSuzukiT1TableCoordinate : SuzukiT1TableCoordinate
canonicalSuzukiT1TableCoordinate = suzuki-t1-table-coordinate
  "6.Suz.2"
  3
  2
  3
  "[C,DCD]^7"
  true

record ComplementLiftReceipt : Set where
  constructor complement-lift-receipt
  field
    outerClassPosition : Nat
    mainClassPosition : Nat
    fusionExplicitlyComplementary : Bool
    sameObjectT1Paid : Bool
    zeroLambdaSectionPaid : Bool
open ComplementLiftReceipt public

canonicalComplementLiftReceipt : ComplementLiftReceipt
canonicalComplementLiftReceipt = complement-lift-receipt
  3 18 true true true

record DiagonalPairNarrowing : Set where
  constructor diagonal-pair-narrowing
  field
    lambdaZeroMainClass : Nat
    firstNonzeroLiftClass : Nat
    secondNonzeroLiftClass : Nat
    qGtoN3BKernelClass : Nat
    lambdaZeroClassIs18 : lambdaZeroMainClass ≡ 18
    kernelClassIs20 : qGtoN3BKernelClass ≡ 20
    nonzeroPairExactly19And20 : Bool
    class20BelongsToDiagonalPair : Bool
    class20RelativeSignPaid : Bool
open DiagonalPairNarrowing public

canonicalDiagonalPairNarrowing : DiagonalPairNarrowing
canonicalDiagonalPairNarrowing = diagonal-pair-narrowing
  18 19 20 20 refl refl true true false

------------------------------------------------------------------------
-- Attribution/navigation boundaries.
------------------------------------------------------------------------

record ComplementAnchorExternalCoordinates : Set where
  constructor complement-anchor-external-coordinates
  field
    groupRepresentationQid : String
    finiteGroupQid : String
    groupRepresentationDewey : String
    finiteGroupDewey : String
    oeisCoordinate : String
    oeisHasComplementAuthority : Bool
open ComplementAnchorExternalCoordinates public

canonicalComplementAnchorExternalCoordinates : ComplementAnchorExternalCoordinates
canonicalComplementAnchorExternalCoordinates = complement-anchor-external-coordinates
  "Q1055807"
  "Q1057968"
  "512.22"
  "512.23"
  "not applicable: complement fusion and central C3 class identity are group/representation data"
  false

------------------------------------------------------------------------
-- WrongType / non-promotion boundaries.
------------------------------------------------------------------------

data ClassThreeCreatesWordT1 : Set where
data ComplementFusionCreatesLambdaOneTwoOrder : Set where
data ClassTwentyCreatesInverseSign : Set where
data QidCreatesComplementReceipt : Set where
data DeweyCreatesComplementReceipt : Set where
data OeisCreatesComplementReceipt : Set where

classThreeDoesNotCreateWord : ClassThreeCreatesWordT1 → ⊥
classThreeDoesNotCreateWord ()

complementDoesNotOrderNonzeroLifts : ComplementFusionCreatesLambdaOneTwoOrder → ⊥
complementDoesNotOrderNonzeroLifts ()

classTwentyDoesNotCreateInverseSign : ClassTwentyCreatesInverseSign → ⊥
classTwentyDoesNotCreateInverseSign ()

qidDoesNotCreateReceipt : QidCreatesComplementReceipt → ⊥
qidDoesNotCreateReceipt ()

deweyDoesNotCreateReceipt : DeweyCreatesComplementReceipt → ⊥
deweyDoesNotCreateReceipt ()

oeisDoesNotCreateReceipt : OeisCreatesComplementReceipt → ⊥
oeisDoesNotCreateReceipt ()

------------------------------------------------------------------------
-- Highest-alpha frontier.
------------------------------------------------------------------------

record T1ComplementFrontier : Set where
  constructor t1-complement-frontier
  field
    t1LiteralWordPaid : Bool
    outerClassThreeOrderThreeSizeTwoPaid : Bool
    outerClassThreeIsT1Paid : Bool
    complementFusionThreeToEighteenPaid : Bool
    mainClassEighteenLambdaZeroPaid : Bool
    classesNineteenTwentyAreNonzeroDiagonalPairPaid : Bool
    classTwentyIsKilledDiagonalPaid : Bool
    classTwentyRelativeSignPaid : Bool
    nextResidual : String
open T1ComplementFrontier public

currentT1ComplementFrontier : T1ComplementFrontier
currentT1ComplementFrontier = t1-complement-frontier
  true true true true true true true false
  "the complement anchor removes the lambda-zero ambiguity: main class 18 is t1 with lambda=0, and classes 19/20 are the two diagonal products. The only invariant historical sign leaf is now to distinguish whether killed class 20 is t1*t2 or t1*t2^-1. Pay that using makewords.mag (i,j,k) ordering, factor.c/q(C,D,E), or an exact evaluation of Bray-Wilson's diagonal discriminator in the same representation. Do not infer 19=lambda1 and 20=lambda2 from consecutive row numbers."

routingFrontier : Routing.T1T2RoutingFrontier
routingFrontier = Routing.currentT1T2RoutingFrontier

lambdaFrontier : Lambda.TripleLambdaFrontier
lambdaFrontier = Lambda.currentTripleLambdaFrontier

kernelFrontier : Kernel.PrimarySupplementKernelFrontier
kernelFrontier = Kernel.currentPrimarySupplementKernelFrontier
