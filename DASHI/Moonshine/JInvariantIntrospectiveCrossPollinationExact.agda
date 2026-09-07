module DASHI.Moonshine.JInvariantIntrospectiveCrossPollinationExact where

------------------------------------------------------------------------
-- J-INVARIANT INTROSPECTIVE CROSS-POLLINATION
--
-- The observed images motivated two questions:
--   * repeated local three-way colour/fan structure;
--   * complementary real/phase / paired-orientation structure.
--
-- Source inspection then found exact nearby mathematical coordinates:
--   * the theta presentation uses three named theta constants a,b,c;
--   * the modular-lambda presentation has six j-equivalent replacements;
--   * j has three branch values {0,1,infinity};
--   * the q-expansion is the classical Monster/moonshine seam.
--
-- The visual observation schedules these checks.  It does not prove that the
-- visible three-way fans ARE theta sectors, Belyi branches, Base369 cells, or
-- Monster fibres.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import Base369 using
  ( TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  )

import DASHI.Moonshine.JInvariantSourceAtlasExact as Sources
import DASHI.Moonshine.JInvariantLambdaOrbitBase369BridgeExact as Lambda
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.Base369Ternary27SpectralSymmetryIrrepBridgeExact as Spectral

------------------------------------------------------------------------
-- 1. Exact finite theta-coordinate indexing from the sourced formula.
--
-- This is only an index equivalence: theta2/theta3/theta4 are NOT SSP trits.
------------------------------------------------------------------------

data ThetaCoordinateTag : Set where
  theta2Tag theta3Tag theta4Tag : ThetaCoordinateTag

thetaTagToTriIndex : ThetaCoordinateTag → TriTruth
thetaTagToTriIndex theta2Tag = tri-low
thetaTagToTriIndex theta3Tag = tri-mid
thetaTagToTriIndex theta4Tag = tri-high

triIndexToThetaTag : TriTruth → ThetaCoordinateTag
triIndexToThetaTag tri-low = theta2Tag
triIndexToThetaTag tri-mid = theta3Tag
triIndexToThetaTag tri-high = theta4Tag

thetaTriRoundTrip : (t : ThetaCoordinateTag) → triIndexToThetaTag (thetaTagToTriIndex t) ≡ t
thetaTriRoundTrip theta2Tag = refl
thetaTriRoundTrip theta3Tag = refl
thetaTriRoundTrip theta4Tag = refl

triThetaRoundTrip : (t : TriTruth) → thetaTagToTriIndex (triIndexToThetaTag t) ≡ t
triThetaRoundTrip tri-low = refl
triThetaRoundTrip tri-mid = refl
triThetaRoundTrip tri-high = refl

------------------------------------------------------------------------
-- 2. Exact finite 3 / 6 / 27 neighbourhood already owned in-repo.
------------------------------------------------------------------------

jSourceHasThreeThetaCoordinateLabels : Bool
jSourceHasThreeThetaCoordinateLabels = true

jSourceHasSixLambdaOrbitLabels : Bool
jSourceHasSixLambdaOrbitLabels = true

base369OneCubeHasTwentySevenStates :
  Geometry.hypervoxelStateCount ≡ 27
base369OneCubeHasTwentySevenStates = Geometry.hypervoxelStateCountIs27

base369CubeHasTwentySevenFrequencyLabels :
  Spectral.cubeSectorCount ≡ 27
base369CubeHasTwentySevenFrequencyLabels = Spectral.cubeSectorCountIs27

------------------------------------------------------------------------
-- 3. RH role is deliberately narrower than the modular/Monster bridge.
--
-- Per the current research architecture, RH is assigned to arithmetic-prime
-- and reflection/spectral-symmetry work.  The interface below has NO
-- canonical inhabitant: an actual RH-side producer must supply the receipts.
------------------------------------------------------------------------

record RHPrimeSymmetryInterface : Set₁ where
  field
    PrimeSideReceipt : Set
    ReflectionSymmetryReceipt : Set
    primeSide : PrimeSideReceipt
    reflectionSymmetrySide : ReflectionSymmetryReceipt

-- There is intentionally no RHPrimeSymmetryInterface -> j-invariance,
-- no RHPrimeSymmetryInterface -> Monster action, and no visual -> RH theorem.

------------------------------------------------------------------------
-- 4. Introspective observer: source-aligned coordinates versus visual prompts.
------------------------------------------------------------------------

data JObserverCoordinate : Set where
  thetaTripleCoordinate : JObserverCoordinate
  lambdaSixOrbitCoordinate : JObserverCoordinate
  belyiThreeBranchCoordinate : JObserverCoordinate
  monsterQExpansionCoordinate : JObserverCoordinate
  rhPrimeSideCoordinate : JObserverCoordinate
  rhReflectionSymmetryCoordinate : JObserverCoordinate

record JIntrospectiveCrossPollinationBoundary : Set where
  constructor j-introspective-cross-pollination-boundary
  field
    visualThreeFanScheduledThetaInspection : Bool
    sourceActuallyContainsThetaTriple : Bool
    sourceActuallyContainsSixLambdaOrbit : Bool
    sourceActuallyContainsThreeBelyiBranchValues : Bool
    sourceActuallyContainsMonsterQExpansionSeam : Bool
    finiteSixToThreePairingCompiled : Bool
    ternaryTwentySevenCarrierAlreadyOwned : Bool
    rhRoleRestrictedToPrimeAndReflectionSymmetry : Bool
    visualThreeFanEqualsThetaTriple : Bool
    belyiThreeBranchesEqualBase369Trits : Bool
    lambdaSixOrbitEqualsAnalyticBase369MobiusAction : Bool
    rhPrimeSymmetryReceiptProvesJOrMonster : Bool
    numericalThreeSixTwentySevenCoincidenceCreatesSemantics : Bool

canonicalJIntrospectiveCrossPollinationBoundary :
  JIntrospectiveCrossPollinationBoundary
canonicalJIntrospectiveCrossPollinationBoundary =
  j-introspective-cross-pollination-boundary
    true true true true true true true true
    false false false false false

visualPromptDoesNotPromoteThetaIdentity :
  JIntrospectiveCrossPollinationBoundary.visualThreeFanEqualsThetaTriple
    canonicalJIntrospectiveCrossPollinationBoundary ≡ false
visualPromptDoesNotPromoteThetaIdentity = refl

rhRoleDoesNotPromoteJOrMonster :
  JIntrospectiveCrossPollinationBoundary.rhPrimeSymmetryReceiptProvesJOrMonster
    canonicalJIntrospectiveCrossPollinationBoundary ≡ false
rhRoleDoesNotPromoteJOrMonster = refl

sharedNumeralsDoNotCreateSemanticIdentity :
  JIntrospectiveCrossPollinationBoundary.numericalThreeSixTwentySevenCoincidenceCreatesSemantics
    canonicalJIntrospectiveCrossPollinationBoundary ≡ false
sharedNumeralsDoNotCreateSemanticIdentity = refl

------------------------------------------------------------------------
-- 5. Keep the source-aligned carriers and exact finite bridge live.
------------------------------------------------------------------------

thetaClaimIsSecondaryReference :
  Sources.JReferenceClaim.secondaryReferenceOnly Sources.jThetaTripleClaim ≡ true
thetaClaimIsSecondaryReference = refl

lambdaPairBridgeIsFiniteOnly :
  Lambda.JLambdaBase369Boundary.analyticLambdaFunctionsImplementedHere
    Lambda.canonicalJLambdaBase369Boundary ≡ false
lambdaPairBridgeIsFiniteOnly = refl
