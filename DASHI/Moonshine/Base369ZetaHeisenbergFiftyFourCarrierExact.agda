module DASHI.Moonshine.Base369ZetaHeisenbergFiftyFourCarrierExact where

------------------------------------------------------------------------
-- BASE369 ZETA / HEISENBERG FIFTY-FOUR CARRIER
--
-- The 54-count is treated here as a finite carrier count, not silently as the
-- dimension of the 729-state Heisenberg Schrodinger representation.
--
-- Exact factorisations made structural here:
--
--   54 = 2 * 27
--      = 2 * 3 * 9
--      = 6 * 9.
--
-- The factor 2 is the nontrivial C3 conjugation orbit {zeta,zeta^-1};
-- the factor 27 is one Base369 ternary hypervoxel T3^3;
-- splitting one ternary coordinate from the other two gives
--   ({zeta,zeta^-1} x T3) x T3^2,
-- whose left factor has six constructors and whose right factor has nine.
-- The six constructors are put in exact bijection with the six coordinate axes
-- of the finite-Heisenberg X6 carrier.  This is a carrier chart only; it does
-- not identify a 54-site carrier with X6 itself, whose state count is 3^6=729.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Moonshine.C3CyclotomicRealDescentExact as Zeta
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as Heisenberg

------------------------------------------------------------------------
-- 1. The nontrivial zeta-conjugate pair.
------------------------------------------------------------------------

data NontrivialZetaSheet : Set where
  zetaSheet : NontrivialZetaSheet
  inverseZetaSheet : NontrivialZetaSheet

nontrivialZetaSheetCount : Nat
nontrivialZetaSheetCount = Zeta.nontrivialOrbitSize

nontrivialZetaSheetCountIsTwo : nontrivialZetaSheetCount ≡ 2
nontrivialZetaSheetCountIsTwo = refl

------------------------------------------------------------------------
-- 2. Two zeta sheets over one ternary 27-hypervoxel.
------------------------------------------------------------------------

record Zeta54Site : Set where
  constructor zeta54Site
  field
    sheet : NontrivialZetaSheet
    voxelPoint : Geometry.Ternary27Point
open Zeta54Site public

zeta54SiteCount : Nat
zeta54SiteCount = nontrivialZetaSheetCount * Geometry.hypervoxelStateCount

zeta54SiteCountIsFiftyFour : zeta54SiteCount ≡ 54
zeta54SiteCountIsFiftyFour = refl

twoTimesTwentySevenIsFiftyFour : 2 * 27 ≡ 54
twoTimesTwentySevenIsFiftyFour = refl

------------------------------------------------------------------------
-- 3. Split T3^3 as T3 x T3^2.  The first factor joins the zeta pair to make
--    the sixfold carrier; the remaining two trits make the nonary carrier.
------------------------------------------------------------------------

record Nonary9Point : Set where
  constructor nonary9Point
  field
    u : SSP.SSPTrit
    v : SSP.SSPTrit
open Nonary9Point public

nonaryPointCount : Nat
nonaryPointCount = 3 * 3

nonaryPointCountIsNine : nonaryPointCount ≡ 9
nonaryPointCountIsNine = refl

record ZetaTrit6 : Set where
  constructor zetaTrit6
  field
    phaseSheet : NontrivialZetaSheet
    ternaryCoordinate : SSP.SSPTrit
open ZetaTrit6 public

zetaTritCount : Nat
zetaTritCount = 2 * 3

zetaTritCountIsSix : zetaTritCount ≡ 6
zetaTritCountIsSix = refl

record SixByNineSite : Set where
  constructor sixByNineSite
  field
    sixCoordinate : ZetaTrit6
    nonaryCoordinate : Nonary9Point
open SixByNineSite public

sixByNineSiteCount : Nat
sixByNineSiteCount = zetaTritCount * nonaryPointCount

sixByNineSiteCountIsFiftyFour : sixByNineSiteCount ≡ 54
sixByNineSiteCountIsFiftyFour = refl

zeta54ToSixByNine : Zeta54Site → SixByNineSite
zeta54ToSixByNine
  (zeta54Site s (Geometry.ternary27Point x y z)) =
  sixByNineSite (zetaTrit6 s x) (nonary9Point y z)

sixByNineToZeta54 : SixByNineSite → Zeta54Site
sixByNineToZeta54
  (sixByNineSite (zetaTrit6 s x) (nonary9Point y z)) =
  zeta54Site s (Geometry.ternary27Point x y z)

zeta54SixByNineRoundTrip :
  (p : Zeta54Site) → sixByNineToZeta54 (zeta54ToSixByNine p) ≡ p
zeta54SixByNineRoundTrip
  (zeta54Site s (Geometry.ternary27Point x y z)) = refl

sixByNineZeta54RoundTrip :
  (p : SixByNineSite) → zeta54ToSixByNine (sixByNineToZeta54 p) ≡ p
sixByNineZeta54RoundTrip
  (sixByNineSite (zetaTrit6 s x) (nonary9Point y z)) = refl

------------------------------------------------------------------------
-- 4. Exact six-constructor chart to the Heisenberg coordinate axes.
------------------------------------------------------------------------

zetaTrit6ToAxis6 : ZetaTrit6 → Heisenberg.Axis6
zetaTrit6ToAxis6 (zetaTrit6 zetaSheet SSP.sspNegOne) = Heisenberg.axis0
zetaTrit6ToAxis6 (zetaTrit6 zetaSheet SSP.sspZero) = Heisenberg.axis1
zetaTrit6ToAxis6 (zetaTrit6 zetaSheet SSP.sspPosOne) = Heisenberg.axis2
zetaTrit6ToAxis6 (zetaTrit6 inverseZetaSheet SSP.sspNegOne) = Heisenberg.axis3
zetaTrit6ToAxis6 (zetaTrit6 inverseZetaSheet SSP.sspZero) = Heisenberg.axis4
zetaTrit6ToAxis6 (zetaTrit6 inverseZetaSheet SSP.sspPosOne) = Heisenberg.axis5

axis6ToZetaTrit6 : Heisenberg.Axis6 → ZetaTrit6
axis6ToZetaTrit6 Heisenberg.axis0 = zetaTrit6 zetaSheet SSP.sspNegOne
axis6ToZetaTrit6 Heisenberg.axis1 = zetaTrit6 zetaSheet SSP.sspZero
axis6ToZetaTrit6 Heisenberg.axis2 = zetaTrit6 zetaSheet SSP.sspPosOne
axis6ToZetaTrit6 Heisenberg.axis3 = zetaTrit6 inverseZetaSheet SSP.sspNegOne
axis6ToZetaTrit6 Heisenberg.axis4 = zetaTrit6 inverseZetaSheet SSP.sspZero
axis6ToZetaTrit6 Heisenberg.axis5 = zetaTrit6 inverseZetaSheet SSP.sspPosOne

zetaTritAxisRoundTrip :
  (c : ZetaTrit6) → axis6ToZetaTrit6 (zetaTrit6ToAxis6 c) ≡ c
zetaTritAxisRoundTrip (zetaTrit6 zetaSheet SSP.sspNegOne) = refl
zetaTritAxisRoundTrip (zetaTrit6 zetaSheet SSP.sspZero) = refl
zetaTritAxisRoundTrip (zetaTrit6 zetaSheet SSP.sspPosOne) = refl
zetaTritAxisRoundTrip (zetaTrit6 inverseZetaSheet SSP.sspNegOne) = refl
zetaTritAxisRoundTrip (zetaTrit6 inverseZetaSheet SSP.sspZero) = refl
zetaTritAxisRoundTrip (zetaTrit6 inverseZetaSheet SSP.sspPosOne) = refl

axisZetaTritRoundTrip :
  (a : Heisenberg.Axis6) → zetaTrit6ToAxis6 (axis6ToZetaTrit6 a) ≡ a
axisZetaTritRoundTrip Heisenberg.axis0 = refl
axisZetaTritRoundTrip Heisenberg.axis1 = refl
axisZetaTritRoundTrip Heisenberg.axis2 = refl
axisZetaTritRoundTrip Heisenberg.axis3 = refl
axisZetaTritRoundTrip Heisenberg.axis4 = refl
axisZetaTritRoundTrip Heisenberg.axis5 = refl

------------------------------------------------------------------------
-- 5. 729 remains the state count of six ternary Heisenberg coordinates.
------------------------------------------------------------------------

heisenbergCoordinateCount : Nat
heisenbergCoordinateCount = Heisenberg.translationGeneratorCount

heisenbergCoordinateCountIsSix : heisenbergCoordinateCount ≡ 6
heisenbergCoordinateCountIsSix = refl

heisenbergStateCount : Nat
heisenbergStateCount = Heisenberg.schrodingerBasisDimension

heisenbergStateCountIsSevenTwentyNine : heisenbergStateCount ≡ 729
heisenbergStateCountIsSevenTwentyNine = refl

fiftyFourIsSixTimesNine : 6 * 9 ≡ 54
fiftyFourIsSixTimesNine = refl

fiftyFourIsTwoTimesThreeTimesNine : 2 * 3 * 9 ≡ 54
fiftyFourIsTwoTimesThreeTimesNine = refl

------------------------------------------------------------------------
-- 6. Boundary: the carrier factorisation is exact, representation promotion
--    is not automatic.
------------------------------------------------------------------------

record ZetaHeisenbergFiftyFourBoundary : Set where
  constructor zetaHeisenbergFiftyFourBoundary
  field
    fiftyFourIsTwoZetaSheetsTimesTwentySeven : Bool
    fiftyFourIsSixTimesNine : Bool
    sixFactorChartsExactlyToHeisenbergAxes : Bool
    heisenbergStateCarrierHasSevenTwentyNineStates : Bool
    fiftyFourIsHeisenbergRepresentationDimension : Bool
    zetaSheetPairIsWholeC3CharacterCarrier : Bool
    sixByNineCarrierAloneDeterminesMonsterRepresentation : Bool

canonicalZetaHeisenbergFiftyFourBoundary : ZetaHeisenbergFiftyFourBoundary
canonicalZetaHeisenbergFiftyFourBoundary =
  zetaHeisenbergFiftyFourBoundary true true true true false false false
