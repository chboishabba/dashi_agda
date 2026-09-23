module DASHI.Moonshine.JInvariant369Zeta6561MonsterCrosswalkExact where

------------------------------------------------------------------------
-- ZETA / 6561 / 65610 / MONSTER-ADJACENT CROSSWALK
--
-- This owner restores several theorem-bearing lanes that are easy to conflate:
--
--  (A) cyclotomic zeta_3 / C3 character evaluation,
--  (B) 3^8 = 6561 ternary fibres/carriers,
--  (C) the Monster-3B regular multiplicity 65610 = 10 * 6561,
--  (D) 196830 = 3 * 65610 and 196883 = 196830 + 53,
--  (E) the independent Riemann-zeta -> divisor-sum -> Eisenstein lane.
--
-- It also constructs an exact pointed finite shape
--
--      6561 = 1 + 6560
--
-- as 1 + Fin 6560 ~= Fin 6561, but deliberately does NOT identify that
-- pointed shape with X8, the local-27 hidden fibre, or the external ATLAS
-- 6561-point 3-local permutation representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Fin using (Fin; zero; suc)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.IbrahimInverseZetaJCoarseFineMonsterDivisorSnowballExact as Inverse
import DASHI.Wikimedia.IbrahimMonster3BNineStratificationOEISPrimarySourceSnowballExact as Nine
import DASHI.Wikimedia.IbrahimEnZeroToThirteenNDimOEISHyperfabricSnowballExact as Rank
import DASHI.Moonshine.C3CoarseFineRatioTypingExact as Ratio
import DASHI.Moonshine.Base369MonsterThreeLocalEightToSixPlusTwoCarrierBidiExact as X8
import DASHI.Moonshine.Monster3BHeisenbergMultiplicityExact as Heisenberg
import DASHI.Moonshine.JInvariantFibonacciJCoarseFineVoxelBidiExact as JFine
import DASHI.Moonshine.JInvariantEisensteinFiniteQSeriesExact as Eisenstein

------------------------------------------------------------------------
-- 1. Cyclotomic zeta_3 lane: exact, finite, and NOT Riemann zeta.
------------------------------------------------------------------------

inverseZeta3IsZeta3Squared =
  Inverse.inverseZetaIsZetaSquared

zeta3TimesInverseIsOne =
  Inverse.zetaTimesInverseZetaIsOne

inverseZeta3TimesZeta3IsOne =
  Inverse.inverseZetaTimesZetaIsOne

zeta3CubedIsOne =
  Inverse.zetaCubedIsOne

regularC3PhaseCancels =
  Inverse.regularPhaseCancellation

------------------------------------------------------------------------
-- 2. The 6561 family, with typed roles kept separate.
------------------------------------------------------------------------

rank8ProfilesAre6561 :
  Rank.fixedTernaryProfileCount Rank.rank8 ≡ 6561
rank8ProfilesAre6561 =
  Rank.rank8Profiles

x8CarrierCountIs6561 :
  X8.threePowerEight ≡ 6561
x8CarrierCountIs6561 =
  X8.threePowerEightIs6561

x8SplitSixPlusTwoCountIs6561 :
  X8.threePowerSixTimesThreeSquared ≡ 6561
x8SplitSixPlusTwoCountIs6561 =
  X8.sixPlusTwoProductIs6561

heisenbergThreePowerEightIs6561 :
  Heisenberg.threePowerEight ≡ 6561
heisenbergThreePowerEightIs6561 =
  Heisenberg.threePowerEightIs6561

------------------------------------------------------------------------
-- 3. Exact pointed 6561 = 1 + 6560 shape.
------------------------------------------------------------------------

data Pointed6561 : Set where
  distinguished : Pointed6561
  ordinary : Fin 6560 → Pointed6561

pointedToFin6561 :
  Pointed6561 →
  Fin 6561
pointedToFin6561 distinguished = zero
pointedToFin6561 (ordinary index) = suc index

fin6561ToPointed :
  Fin 6561 →
  Pointed6561
fin6561ToPointed zero = distinguished
fin6561ToPointed (suc index) = ordinary index

pointed6561RoundTrip :
  (state : Pointed6561) →
  fin6561ToPointed (pointedToFin6561 state) ≡ state
pointed6561RoundTrip distinguished = refl
pointed6561RoundTrip (ordinary index) = refl

fin6561RoundTrip :
  (index : Fin 6561) →
  pointedToFin6561 (fin6561ToPointed index) ≡ index
fin6561RoundTrip zero = refl
fin6561RoundTrip (suc index) = refl

sixFiveSixOneAsOnePlusSixFiveSixZero :
  6561 ≡ 1 + 6560
sixFiveSixOneAsOnePlusSixFiveSixZero = refl

------------------------------------------------------------------------
-- 4. 6561 -> 65610 -> 196830 -> 196883 -> 196884.
------------------------------------------------------------------------

regularCopiesPerMacroBlockIs6561 :
  Ratio.regularCopiesPerMacroBlock ≡ 6561
regularCopiesPerMacroBlockIs6561 =
  Ratio.regularCopiesPerMacroBlockIs6561

regularMultiplicityIs65610 :
  Ratio.totalRegularCopyCount ≡ 65610
regularMultiplicityIs65610 =
  Ratio.totalRegularCopyCountIs65610

sixFiveSixOneZeroIsTenTimesSixFiveSixOne :
  65610 ≡ 10 * 6561
sixFiveSixOneZeroIsTenTimesSixFiveSixOne = refl

sixFiveSixOneZeroIsNinetyTimes729 :
  65610 ≡ 90 * 729
sixFiveSixOneZeroIsNinetyTimes729 =
  Nine.regularPhaseAsNinetyTimes729

oneNineSixEightThreeZeroIsThreeTimes65610 :
  196830 ≡ 3 * 65610
oneNineSixEightThreeZeroIsThreeTimes65610 =
  Inverse.bulkOverRegularMultiplicity

monster196883IsThreeTimes65610Plus53 :
  196883 ≡ 3 * 65610 + 53
monster196883IsThreeTimes65610Plus53 =
  Inverse.ExactRemainder.euclideanLaw
    Inverse.monsterOverRegularMultiplicity

moonshine196884IsMonsterPlusOne :
  196884 ≡ 196883 + 1
moonshine196884IsMonsterPlusOne = refl

------------------------------------------------------------------------
-- 5. 1 + 2 + 6 exponent stratification.
------------------------------------------------------------------------

nineExponentIsOnePlusTwoPlusSix :
  1 + 2 + 6 ≡ 9
nineExponentIsOnePlusTwoPlusSix =
  Nine.nineExponentAsOnePlusTwoPlusSix

threePowerNineStratifiesAsOneTwoSix =
  Nine.threePowerNineAsOneTwoSixProduct

bulkStratifiesAsOuterThreeTimesNinetyTimes729 :
  196830 ≡ 3 * 90 * 729
bulkStratifiesAsOuterThreeTimesNinetyTimes729 =
  Nine.regularBulkAsThreeTimesNinetyTimes729

------------------------------------------------------------------------
-- 6. External ATLAS 6561 coordinate.
--
-- The ATLAS page is authority only for the database statement.  It does not
-- identify the ATLAS permutation points with any DASHI ternary carrier.
------------------------------------------------------------------------

atlasMonster6561Source : Attribution.AttributedSource
atlasMonster6561Source = Attribution.mkNoDOISource
  "ATLAS of Finite Group Representations contributors"
  "ATLAS: 3^(3+2+6+6):(L3(3) x SD16) -- permutation representation on 6561 points"
  "ATLAS of Finite Group Representations"
  "retrieved 2026-09-23"
  "https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/Mmax15q1G0-p6561B0"
  (Attribution.namedSourceKind "finite-group permutation-representation database record")
  "source for a transitive imprimitive 6561-point permutation representation of the proper image 3^(2+6+6):(L3(3) x SD16) listed under the Monster 3-local subgroup; not a 6561-point permutation representation of the full Monster and not a DASHI X8/J-fibre identification"
  Attribution.publicAttribution

atlasMonster6561Attribution =
  Snowball.canonicalSourceRoleSnowballReceipt atlasMonster6561Source

record Atlas6561Coordinate : Set where
  constructor atlas-6561-coordinate
  field
    numberOfPoints : Nat
    properImageDescription : String
    transitive : Bool
    imprimitive : Bool
    fullMonsterActionClaimed : Bool
    identifiedWithDASHIX8 : Bool
    identifiedWithJHiddenFibre : Bool

open Atlas6561Coordinate public

canonicalAtlas6561Coordinate : Atlas6561Coordinate
canonicalAtlas6561Coordinate =
  atlas-6561-coordinate
    6561
    "3^(2+6+6):(L3(3) x SD16)"
    true true false false false

------------------------------------------------------------------------
-- 7. Riemann-zeta / divisor-sum / Eisenstein lane.
--
-- The finite Eisenstein owner consumes sigma_3 and sigma_5 through a
-- DivisorPowerKernel.  The classical Dirichlet-series identity
--
--   sum sigma_r(n)/n^s = zeta_R(s) zeta_R(s-r)
--
-- is NOT the same zeta as zeta_3 above and is not yet welded into that kernel
-- as a concrete Agda analytic theorem here.
------------------------------------------------------------------------

eisensteinFiniteBoundary :
  Eisenstein.EisensteinFiniteQSeriesFrontier
eisensteinFiniteBoundary =
  Eisenstein.canonicalEisensteinFiniteQSeriesFrontier

record ZetaLaneSeparationBoundary : Set where
  constructor zeta-lane-separation-boundary
  field
    cyclotomicZeta3InversePaid : Bool
    cyclotomicRegularCancellationPaid : Bool
    rank8AndX8Count6561Paid : Bool
    pointed6561OnePlus6560Paid : Bool
    regularMultiplicity65610Paid : Bool
    bulk196830AsThreeTimes65610Paid : Bool
    monsterResidual53Paid : Bool
    oneTwoSixExponentStratificationPaid : Bool
    atlas6561ExternalCoordinatePaid : Bool

    cyclotomicZeta3EqualsRiemannZeta : Bool
    atlas6561EqualsX8Carrier : Bool
    atlas6561EqualsJHiddenFibre : Bool
    pointed6561EqualsAtlasPermutationCarrier : Bool
    riemannZetaDivisorSeriesWeldToEisensteinKernelPaidHere : Bool

open ZetaLaneSeparationBoundary public

canonicalZetaLaneSeparationBoundary :
  ZetaLaneSeparationBoundary
canonicalZetaLaneSeparationBoundary =
  zeta-lane-separation-boundary
    true true true true true true true true true
    false false false false false

------------------------------------------------------------------------
-- 8. Explicit WrongType permissions.
------------------------------------------------------------------------

data CyclotomicZetaEqualsRiemannZeta : Set where
data Equal6561IdentifiesCarriers : Set where
data PointedSplitCreatesAtlasAction : Set where

cyclotomicZetaDoesNotEqualRiemannZeta :
  CyclotomicZetaEqualsRiemannZeta → ⊥
cyclotomicZetaDoesNotEqualRiemannZeta ()

same6561DoesNotIdentifyCarriers :
  Equal6561IdentifiesCarriers → ⊥
same6561DoesNotIdentifyCarriers ()

pointedSplitDoesNotCreateAtlasAction :
  PointedSplitCreatesAtlasAction → ⊥
pointedSplitDoesNotCreateAtlasAction ()
