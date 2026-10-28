module DASHI.Mathematics.Topology.AlexanderHornedLocalFibreTetrationTransportExact where

------------------------------------------------------------------------
-- EXACT NATIVE-TERNARY / THIRD-LEVEL FUNCTION-SPACE TRANSPORT.
--
-- Native Horn end cell at depth two:
--   X2 = C3_sector × Trit × Trit (27 actual addresses).
-- Repository LevelTwoCode:
--   T × T × T (27 endomorphism-truth-table slots).
-- These are constructor-level BIJECTIVE FINITE CARRIERS, even though
-- their semantics and natural symmetry actions differ.
--
-- The real point of cross-pollination is:
--   Gauge2 = (X2 -> C3_phase)
--          ≅ (LevelTwoCode -> TriTruth)
--   |Gauge2| = 3^27 = 3↑↑3.
-- This is a pointwise two-sided function-space equivalence, not
-- merely cardinality. It is the 3rd predicate-table level of the
-- existing DASHI RecursiveFibreTower function-space hierarchy.
--
-- Original Hatcher 3×2^n binary geometry remains distinct.
-- 3^27 fields do not create 3^27 geometric horns or Monster states.
-- Classical finite currying/function-space combinatorics reused from
-- prior DASHI owners. New finite typed chart is SOURCE-WRITTEN,
-- Agda-kernel pending; no postulates or function-extensionality axiom.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (_*_)
open import Data.Product using (_,_)
open import Data.Vec.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import Base369 as Base
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Cognition.RecursiveFibreTower as Tower
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Local

sectorAsTruth : C3.C3 → Base.TriTruth
sectorAsTruth C3.c0 = Base.tri-low
sectorAsTruth C3.c1 = Base.tri-mid
sectorAsTruth C3.c2 = Base.tri-high

truthAsSector : Base.TriTruth → C3.C3
truthAsSector Base.tri-low = C3.c0
truthAsSector Base.tri-mid = C3.c1
truthAsSector Base.tri-high = C3.c2

sectorTruthRoundTrip :
  (c : C3.C3) → truthAsSector (sectorAsTruth c) ≡ c
sectorTruthRoundTrip C3.c0 = refl
sectorTruthRoundTrip C3.c1 = refl
sectorTruthRoundTrip C3.c2 = refl

truthSectorRoundTrip :
  (t : Base.TriTruth) → sectorAsTruth (truthAsSector t) ≡ t
truthSectorRoundTrip Base.tri-low = refl
truthSectorRoundTrip Base.tri-mid = refl
truthSectorRoundTrip Base.tri-high = refl

tritAsTruth : Trit.Trit → Base.TriTruth
tritAsTruth Trit.neg = Base.tri-low
tritAsTruth Trit.zero = Base.tri-mid
tritAsTruth Trit.pos = Base.tri-high

truthAsTrit : Base.TriTruth → Trit.Trit
truthAsTrit Base.tri-low = Trit.neg
truthAsTrit Base.tri-mid = Trit.zero
truthAsTrit Base.tri-high = Trit.pos

tritTruthRoundTrip :
  (t : Trit.Trit) → truthAsTrit (tritAsTruth t) ≡ t
tritTruthRoundTrip Trit.neg = refl
tritTruthRoundTrip Trit.zero = refl
tritTruthRoundTrip Trit.pos = refl

truthTritRoundTrip :
  (t : Base.TriTruth) → tritAsTruth (truthAsTrit t) ≡ t
truthTritRoundTrip Base.tri-low = refl
truthTritRoundTrip Base.tri-mid = refl
truthTritRoundTrip Base.tri-high = refl

addressToTableCode :
  End.BalancedLevel 2 → Tower.LevelTwoCode
addressToTableCode (c , a ∷ b ∷ []) =
  sectorAsTruth c , (tritAsTruth a , tritAsTruth b)

tableCodeToAddress :
  Tower.LevelTwoCode → End.BalancedLevel 2
tableCodeToAddress (c , (a , b)) =
  truthAsSector c , truthAsTrit a ∷ truthAsTrit b ∷ []

addressTableAddress :
  (x : End.BalancedLevel 2) →
  tableCodeToAddress (addressToTableCode x) ≡ x
addressTableAddress (c , a ∷ b ∷ [])
  rewrite sectorTruthRoundTrip c
        | tritTruthRoundTrip a
        | tritTruthRoundTrip b = refl

tableAddressTable :
  (x : Tower.LevelTwoCode) →
  addressToTableCode (tableCodeToAddress x) ≡ x
tableAddressTable (c , (a , b))
  rewrite truthSectorRoundTrip c
        | truthTritRoundTrip a
        | truthTritRoundTrip b = refl

-- Level THREE is a trit-valued function on the TWENTY-SEVEN level-two
-- codes. It is NOT the set of 27 addresses, which forms the DOMAIN.
ThirdLevelTable : Set
ThirdLevelTable = Tower.LevelTwoCode → Base.TriTruth

gaugeToThirdTable :
  Local.FibreAction 2 → ThirdLevelTable
gaugeToThirdTable g x =
  sectorAsTruth (g (tableCodeToAddress x))

thirdTableToGauge :
  ThirdLevelTable → Local.FibreAction 2
thirdTableToGauge f x =
  truthAsSector (f (addressToTableCode x))

gaugeTableGauge :
  (g : Local.FibreAction 2) (x : End.BalancedLevel 2) →
  thirdTableToGauge (gaugeToThirdTable g) x ≡ g x
gaugeTableGauge g x
  rewrite addressTableAddress x
        | sectorTruthRoundTrip (g x) = refl

tableGaugeTable :
  (f : ThirdLevelTable) (x : Tower.LevelTwoCode) →
  gaugeToThirdTable (thirdTableToGauge f) x ≡ f x
tableGaugeTable f x
  rewrite tableAddressTable x
        | truthSectorRoundTrip (f x) = refl

thirdLevelCountIsActualGaugeCount :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
thirdLevelCountIsActualGaugeCount =
  End.ternaryConfigurationTetration

-- A SECOND function-space round yields the fourth tetration level.
-- It is NOT an additional physical address-refinement step.
FourthLevelTable : Set
FourthLevelTable = ThirdLevelTable → Base.TriTruth

fourthLevelCountStep :
  Tower.tetration 3 4 ≡ Tower.pow 3 (Tower.tetration 3 3)
fourthLevelCountStep = Tower.tetrationStep 3 3

-- External sector C3 acts on FIRST code coordinate, independently of
-- internal trit changes. This is not S3 CONJUGATION of an endomorphism.
nextSectorTruth : Base.TriTruth → Base.TriTruth
nextSectorTruth Base.tri-low = Base.tri-mid
nextSectorTruth Base.tri-mid = Base.tri-high
nextSectorTruth Base.tri-high = Base.tri-low

rotateFirstCode : Tower.LevelTwoCode → Tower.LevelTwoCode
rotateFirstCode (c , (a , b)) =
  nextSectorTruth c , (a , b)

sectorRotationIntertwinesFirstCoordinate :
  (x : End.BalancedLevel 2) →
  addressToTableCode (End.rotateBalancedLevel 2 x)
  ≡ rotateFirstCode (addressToTableCode x)
sectorRotationIntertwinesFirstCoordinate (C3.c0 , a ∷ b ∷ []) = refl
sectorRotationIntertwinesFirstCoordinate (C3.c1 , a ∷ b ∷ []) = refl
sectorRotationIntertwinesFirstCoordinate (C3.c2 , a ∷ b ∷ []) = refl

-- The chart is one-to-one as carriers and intertwines only the
-- specifically stated first-coordinate external C3 action.
