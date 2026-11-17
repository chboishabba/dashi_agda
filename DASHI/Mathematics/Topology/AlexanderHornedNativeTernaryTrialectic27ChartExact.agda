module DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryTrialectic27ChartExact where

------------------------------------------------------------------------
-- LOSSLESS 27-CELL CHART OF TWO DISTINCT SEMANTIC OBJECTS.
--
-- Native horn alternative at depth 2: C3_sector × Trit × Trit.
-- Existing reasoning source: SynthesisChoice27 = TriTruth × TriTruth × TriTruth.
-- Both have 27 elements, but one records a sector and two end digits,
-- and the other records thesis/antithesis/synthesis labels.
--
-- We give a CHOSEN bijection, its two inverse proofs, and both
-- independent C3 actions. The *local fibre translation group*
-- Map(K3_2,C3) thus transports to a group of independent local
-- translations on ALL 27 trialectic cells, not just to a COUNT 3^27.
--
-- Reuse original NativeTernaryFibreActionExact for pointwise group
-- operations, and NativeBalancedTernaryEndTowerExact for the real
-- end-address source. PR #1414 polynomial 27/S3/C3 receiver remains
-- independently owned and branch-only, not imported here.
-- This carrier chart does NOT identify root monodromy, wild exterior
-- pi1, physical spin, Galois A5, or Monster 3B.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong; cong₂)

import Base369 as Base
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Algebra.BalancedTernary as T
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Syn
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedNativeTernaryFibreActionExact as Native
import DASHI.Cognition.RecursiveFibreTower as Tower

sectorToTruth : C3.C3 → Base.TriTruth
sectorToTruth C3.c0 = Base.tri-low
sectorToTruth C3.c1 = Base.tri-mid
sectorToTruth C3.c2 = Base.tri-high

truthToSector : Base.TriTruth → C3.C3
truthToSector Base.tri-low = C3.c0
truthToSector Base.tri-mid = C3.c1
truthToSector Base.tri-high = C3.c2

tritToTruth : T.Trit → Base.TriTruth
tritToTruth T.neg = Base.tri-low
tritToTruth T.zero = Base.tri-mid
tritToTruth T.pos = Base.tri-high

truthToTrit : Base.TriTruth → T.Trit
truthToTrit Base.tri-low = T.neg
truthToTrit Base.tri-mid = T.zero
truthToTrit Base.tri-high = T.pos

sectorRoundTrip : ∀ c → truthToSector (sectorToTruth c) ≡ c
sectorRoundTrip C3.c0 = refl
sectorRoundTrip C3.c1 = refl
sectorRoundTrip C3.c2 = refl

truthSectorRoundTrip : ∀ x → sectorToTruth (truthToSector x) ≡ x
truthSectorRoundTrip Base.tri-low = refl
truthSectorRoundTrip Base.tri-mid = refl
truthSectorRoundTrip Base.tri-high = refl

tritRoundTrip : ∀ t → truthToTrit (tritToTruth t) ≡ t
tritRoundTrip T.neg = refl
tritRoundTrip T.zero = refl
tritRoundTrip T.pos = refl

truthTritRoundTrip : ∀ x → tritToTruth (truthToTrit x) ≡ x
truthTritRoundTrip Base.tri-low = refl
truthTritRoundTrip Base.tri-mid = refl
truthTritRoundTrip Base.tri-high = refl

toTrialectic : End.BalancedLevel 2 → Syn.SynthesisChoice27
toTrialectic (c , (a ∷ b ∷ [])) =
  sectorToTruth c , (tritToTruth a , tritToTruth b)

fromTrialectic : Syn.SynthesisChoice27 → End.BalancedLevel 2
fromTrialectic (x , (y , z)) =
  truthToSector x , (truthToTrit y ∷ truthToTrit z ∷ [])

nativeTrialecticRoundTrip :
  (a : End.BalancedLevel 2) →
  fromTrialectic (toTrialectic a) ≡ a
nativeTrialecticRoundTrip (c , (a ∷ b ∷ []))
  rewrite sectorRoundTrip c
        | tritRoundTrip a
        | tritRoundTrip b = refl

trialecticNativeRoundTrip :
  (a : Syn.SynthesisChoice27) →
  toTrialectic (fromTrialectic a) ≡ a
trialecticNativeRoundTrip (x , (y , z))
  rewrite truthSectorRoundTrip x
        | truthTritRoundTrip y
        | truthTritRoundTrip z = refl

-- External sector C3 rotates ONLY the first chart coordinate.
rotateTrialecticSector :
  Syn.SynthesisChoice27 → Syn.SynthesisChoice27
rotateTrialecticSector (x , (y , z)) =
  Base.rotateTri x , (y , z)

sectorRotationIntertwines :
  (a : End.BalancedLevel 2) →
  toTrialectic (End.rotateBalancedLevel 2 a)
    ≡ rotateTrialecticSector (toTrialectic a)
sectorRotationIntertwines (C3.c0 , (a ∷ b ∷ [])) = refl
sectorRotationIntertwines (C3.c1 , (a ∷ b ∷ [])) = refl
sectorRotationIntertwines (C3.c2 , (a ∷ b ∷ [])) = refl

-- Internal trit cycling is a distinct action on TWO coordinates;
-- it does not move the external sector.
rotateTrialecticDigits :
  Syn.SynthesisChoice27 → Syn.SynthesisChoice27
rotateTrialecticDigits (x , (y , z)) =
  x , (Base.rotateTri y , Base.rotateTri z)

tritRotationIntertwines :
  (t : T.Trit) →
  tritToTruth (End.rotateDigit t) ≡ Base.rotateTri (tritToTruth t)
tritRotationIntertwines T.neg = refl
tritRotationIntertwines T.zero = refl
tritRotationIntertwines T.pos = refl

digitRotationIntertwines :
  (a : End.BalancedLevel 2) →
  toTrialectic (End.rotateInternalLevel 2 a)
    ≡ rotateTrialecticDigits (toTrialectic a)
digitRotationIntertwines (c , (a ∷ b ∷ []))
  rewrite tritRotationIntertwines a
        | tritRotationIntertwines b = refl

-- Genuine function-space isomorphism at the 27-cell level.
-- The table/field meaning is transported by precomposition, not
-- identified without an explicit chart.
TrialecticLocalGauge27 : Set
TrialecticLocalGauge27 = Syn.SynthesisChoice27 → C3.C3

toTrialecticGauge :
  Native.FibreAction 2 → TrialecticLocalGauge27
toTrialecticGauge g x = g (fromTrialectic x)

fromTrialecticGauge :
  TrialecticLocalGauge27 → Native.FibreAction 2
fromTrialecticGauge g a = g (toTrialectic a)

nativeGaugeRoundTrip :
  (g : Native.FibreAction 2)
  (a : End.BalancedLevel 2) →
  fromTrialecticGauge (toTrialecticGauge g) a ≡ g a
nativeGaugeRoundTrip g a
  rewrite nativeTrialecticRoundTrip a = refl

trialecticGaugeRoundTrip :
  (g : TrialecticLocalGauge27)
  (x : Syn.SynthesisChoice27) →
  toTrialecticGauge (fromTrialecticGauge g) x ≡ g x
trialecticGaugeRoundTrip g x
  rewrite trialecticNativeRoundTrip x = refl

gaugeGroupLawIntertwines :
  (g h : Native.FibreAction 2)
  (x : Syn.SynthesisChoice27) →
  toTrialecticGauge (Native.combine g h) x
    ≡ C3._∙_ (toTrialecticGauge g x) (toTrialecticGauge h x)
gaugeGroupLawIntertwines g h x = refl

-- This is a CHOSEN chart, not the assertion that the two carriers
-- have the same geometric or philosophical interpretation.


------------------------------------------------------------------------
-- ACTUAL THIRD-LEVEL TERNARY PREDICATE SPACE, not only 3^27 counts.
--
-- This is a genuine NEW two-sided chart layered on the ALREADY OWNED
-- native/trialectic 27-state chart above. No parallel codebook added.
-- Each C3-valued local field becomes a ternary predicate on 27
-- level-two codes. This is the same pointwise function-space structure
-- whose sizes form the original RecursiveFibreTower tetration.
------------------------------------------------------------------------

ThirdPredicateTable : Set
ThirdPredicateTable = Syn.SynthesisChoice27 → Base.TriTruth

thirdLevelFromNativeGauge :
  Native.FibreAction 2 → ThirdPredicateTable
thirdLevelFromNativeGauge g code =
  sectorToTruth (toTrialecticGauge g code)

nativeGaugeFromThirdLevel :
  ThirdPredicateTable → Native.FibreAction 2
nativeGaugeFromThirdLevel h address =
  truthToSector (h (toTrialectic address))

thirdLevelNativeGaugeRoundTrip :
  (g : Native.FibreAction 2) (address : End.BalancedLevel 2) →
  nativeGaugeFromThirdLevel (thirdLevelFromNativeGauge g) address
    ≡ g address
thirdLevelNativeGaugeRoundTrip g address
  rewrite nativeTrialecticRoundTrip address
        | sectorRoundTrip (g address) = refl

nativeGaugeThirdLevelRoundTrip :
  (h : ThirdPredicateTable) (code : Syn.SynthesisChoice27) →
  thirdLevelFromNativeGauge (nativeGaugeFromThirdLevel h) code
    ≡ h code
nativeGaugeThirdLevelRoundTrip h code
  rewrite trialecticNativeRoundTrip code
        | truthSectorRoundTrip (h code) = refl

actualThirdPredicateCardinality :
  Tower.pow 3 (3 * Tower.pow 3 2) ≡ Tower.tetration 3 3
actualThirdPredicateCardinality =
  End.ternaryConfigurationTetration

-- A SECOND application of the predicate-space constructor gives the
-- FOURTH tetration level; this does not refine the ADDRESS depth.
FourthPredicateTable : Set
FourthPredicateTable = ThirdPredicateTable → Base.TriTruth

fourthPredicateCardinalityRecurrence :
  Tower.tetration 3 4 ≡ Tower.pow 3 (Tower.tetration 3 3)
fourthPredicateCardinalityRecurrence =
  Tower.tetrationStep 3 3

-- Spatial refinement X2 -> X3 instead gives 81 addresses and
-- field-group order 3^81. These two recursion axes must not collapse.
