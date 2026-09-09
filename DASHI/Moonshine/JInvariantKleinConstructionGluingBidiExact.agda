module DASHI.Moonshine.JInvariantKleinConstructionGluingBidiExact where

------------------------------------------------------------------------
-- KLEIN J / SIGNED-FIBRE / GLUING BIDI
--
-- The image source describes the plotted object as KleinInvariantJ[z] =
-- g2^3 / Delta in the complex plane.  The real-part description also records
-- an exceptional fundamental triangle with a pair of edges zipped together
-- and a third edge shared with the exceptional tongue.
--
-- This module turns those two source coordinates into a same-object proof
-- search interface.  It does not claim that the rendered open/closed visual
-- motifs are already the analytic gluing maps.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Foundations.Base369SignedMembershipExact as Signed
import DASHI.Moonshine.JInvariantImageFractalSourceAtlasExact as Sources

------------------------------------------------------------------------
-- 1. Exact construction shape of the plotted Klein j object.
------------------------------------------------------------------------

record KleinJAlgebra : Set₁ where
  constructor klein-j-algebra
  field
    Point : Set
    Value : Set
    g2 : Point → Value
    delta : Point → Value
    cube : Value → Value
    quotient : Value → Value → Value

open KleinJAlgebra public

KleinJ : (A : KleinJAlgebra) → Point A → Value A
KleinJ A z = quotient A (cube A (g2 A z)) (delta A z)

record KleinJConstructionAlignment : Set where
  constructor klein-j-construction-alignment
  field
    sourceDescribesG2CubedOverDelta : Bool
    constructionUsesG2 : Bool
    constructionUsesDelta : Bool
    constructionUsesCubeThenQuotient : Bool
    analyticLawsLocallyProved : Bool

canonicalKleinJConstructionAlignment : KleinJConstructionAlignment
canonicalKleinJConstructionAlignment =
  klein-j-construction-alignment true true true true false

complexPlaneSourceClaimRemainsNonProof :
  Sources.sourceEntitlesKernelProof Sources.complexPlaneCarrierClaim ≡ false
complexPlaneSourceClaimRemainsNonProof = refl

exceptionalGluingSourceClaimRemainsNonProof :
  Sources.sourceEntitlesKernelProof Sources.exceptionalTriangleGluingClaim ≡ false
exceptionalGluingSourceClaimRemainsNonProof = refl

------------------------------------------------------------------------
-- 2. Boundary gluing is a fibre coordinate, not a sign bit.
------------------------------------------------------------------------

data GluingState : Set where
  zippedTogether : GluingState
  sharedBoundary : GluingState
  openBoundary : GluingState
  unclassifiedBoundary : GluingState

record SignedGluingFibre : Set where
  constructor signed-gluing-fibre
  field
    orientation : Signed.FibredOrientation
    gluing : GluingState

open SignedGluingFibre public

closedInverseGluing : SignedGluingFibre
closedInverseGluing =
  signed-gluing-fibre Signed.inverseOrientation zippedTogether

openInverseGluing : SignedGluingFibre
openInverseGluing =
  signed-gluing-fibre Signed.inverseOrientation openBoundary

sameSignedOrientationDifferentGluing :
  orientation closedInverseGluing ≡ orientation openInverseGluing
sameSignedOrientationDifferentGluing = refl

closedFixtureIsZipped : gluing closedInverseGluing ≡ zippedTogether
closedFixtureIsZipped = refl

openFixtureIsOpen : gluing openInverseGluing ≡ openBoundary
openFixtureIsOpen = refl

------------------------------------------------------------------------
-- 3. The gluing test: visual anti-orientation only schedules this square.
------------------------------------------------------------------------

data Empty : Set where

notBool : Bool → Bool
notBool false = true
notBool true = false

record BoolGluingSquare : Set where
  constructor bool-gluing-square
  field
    top : Bool → Bool
    left : Bool → Bool
    right : Bool → Bool
    bottom : Bool → Bool

open BoolGluingSquare public

pathTopRight : BoolGluingSquare → Bool → Bool
pathTopRight S x = right S (top S x)

pathLeftBottom : BoolGluingSquare → Bool → Bool
pathLeftBottom S x = bottom S (left S x)

closedCommutingFixture : BoolGluingSquare
closedCommutingFixture =
  bool-gluing-square
    (λ x → x)
    (λ x → x)
    (λ x → x)
    (λ x → x)

closedFixtureCommutes :
  (x : Bool) →
  pathTopRight closedCommutingFixture x ≡
  pathLeftBottom closedCommutingFixture x
closedFixtureCommutes x = refl

antiGluingFixture : BoolGluingSquare
antiGluingFixture =
  bool-gluing-square
    (λ x → x)
    (λ x → x)
    notBool
    (λ x → x)

antiFixtureTopRightTrueIsFalse :
  pathTopRight antiGluingFixture true ≡ false
antiFixtureTopRightTrueIsFalse = refl

antiFixtureLeftBottomTrueIsTrue :
  pathLeftBottom antiGluingFixture true ≡ true
antiFixtureLeftBottomTrueIsTrue = refl

trueIsNotFalse : true ≡ false → Empty
trueIsNotFalse ()

antiFixtureDoesNotCommuteAtTrue :
  pathTopRight antiGluingFixture true ≡
  pathLeftBottom antiGluingFixture true →
  Empty
antiFixtureDoesNotCommuteAtTrue ()

------------------------------------------------------------------------
-- 4. BIDI frontier on the actual Klein-j construction.
------------------------------------------------------------------------

data KleinJGluingResidual : Set where
  missingAnalyticFundamentalDomainCarrier : KleinJGluingResidual
  missingActualZippedEdgeMap : KleinJGluingResidual
  missingActualOpenEdgeMap : KleinJGluingResidual
  missingSameObjectCommutationSquare : KleinJGluingResidual
  missingSignedFibreCompatibilityWithModularAction : KleinJGluingResidual

firstKleinJGluingResidual : KleinJGluingResidual
firstKleinJGluingResidual = missingAnalyticFundamentalDomainCarrier

record KleinJGluingBidiFrontier : Set where
  constructor klein-j-gluing-bidi-frontier
  field
    complexPlaneConstructionSourceAligned : Bool
    zippedEdgeSourceCoordinateAvailable : Bool
    signedGluingCollisionModelled : Bool
    commutingAndNoncommutingFixturesAvailable : Bool
    actualAnalyticGluingPaid : Bool
    visualAntiAutomaticallyMeansNoncommuting : Bool
    firstResidual : KleinJGluingResidual

canonicalKleinJGluingBidiFrontier : KleinJGluingBidiFrontier
canonicalKleinJGluingBidiFrontier =
  klein-j-gluing-bidi-frontier
    true true true true false false
    firstKleinJGluingResidual

visualAntiDoesNotPromoteNoncommutation :
  KleinJGluingBidiFrontier.visualAntiAutomaticallyMeansNoncommuting
    canonicalKleinJGluingBidiFrontier ≡ false
visualAntiDoesNotPromoteNoncommutation = refl
