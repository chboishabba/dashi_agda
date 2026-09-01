module DASHI.Foundations.Base369Completion54SituatedTriadBridgeExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact as Pareto

------------------------------------------------------------------------
-- BASE369 COMPLETION +54 / SITUATED 2x3 BRIDGE
--
-- The coarse completion contribution is a single extra channel (+1).  At a
-- finer local resolution that one channel may expose a 54-state fibre:
--
--   54 = (2 x 3) x 9 = 6 x 9 = 9 + 45.
--
-- The 2x3 factor is the six-slot situated matrix.  The 9 factor is the retained
-- ternary comparison sheet.  This is a resolution relation, not the equation
-- 1 = 54.
--
-- Separately, a *full valuation* of all six situated slots by ternary values has
-- 3^6 = 729 states.  Therefore the 54 completion fibre and the 729 appraisal
-- fibre play different roles and must not be conflated.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- 1. Coarse completion arithmetic.
------------------------------------------------------------------------

coarseBaseChannels : Nat
coarseBaseChannels = 9

coarseCompletionChannels : Nat
coarseCompletionChannels = 1

coarseCarrierChannels : Nat
coarseCarrierChannels = 10

coarseNinePlusOne : coarseBaseChannels + coarseCompletionChannels ≡ coarseCarrierChannels
coarseNinePlusOne = refl

globalFineFibre : Nat
globalFineFibre = 19683

baseBulk : Nat
baseBulk = 177147

completionBulk : Nat
completionBulk = 19683

coarseBulk : Nat
coarseBulk = 196830

nineFineFibresAreBaseBulk : coarseBaseChannels * globalFineFibre ≡ baseBulk
nineFineFibresAreBaseBulk = refl

oneFineFibreIsCompletionBulk : coarseCompletionChannels * globalFineFibre ≡ completionBulk
oneFineFibreIsCompletionBulk = refl

coarseBulkDecomposesNinePlusOne : baseBulk + completionBulk ≡ coarseBulk
coarseBulkDecomposesNinePlusOne = refl

------------------------------------------------------------------------
-- 2. Situated 2x3 slot carrier.
------------------------------------------------------------------------

data SituatedTriadRow : Set where
  observationalRow governedRow : SituatedTriadRow

data SituatedTriadColumn : Set where
  firstAxis secondAxis thirdAxis : SituatedTriadColumn

record SituatedSlot : Set where
  constructor situated-slot
  field
    row : SituatedTriadRow
    column : SituatedTriadColumn

open SituatedSlot public

supportSlot separationSlot measurementSlot : SituatedSlot
supportSlot = situated-slot observationalRow firstAxis
separationSlot = situated-slot observationalRow secondAxis
measurementSlot = situated-slot observationalRow thirdAxis

residualSlot provenanceSlot authoritySlot : SituatedSlot
residualSlot = situated-slot governedRow firstAxis
provenanceSlot = situated-slot governedRow secondAxis
authoritySlot = situated-slot governedRow thirdAxis

situatedSlotCount : Nat
situatedSlotCount = 6

twoRowsTimesThreeColumns : 2 * 3 ≡ situatedSlotCount
twoRowsTimesThreeColumns = refl

------------------------------------------------------------------------
-- 3. Retained ternary comparison sheet: 3 x 3 = 9.
------------------------------------------------------------------------

ComparisonSheet9 : Set
ComparisonSheet9 = Base.TriTruth × Base.TriTruth

comparisonSheetCount : Nat
comparisonSheetCount = 9

threeTimesThreeIsNine : 3 * 3 ≡ comparisonSheetCount
threeTimesThreeIsNine = refl

------------------------------------------------------------------------
-- 4. Local resolution of one completion channel.
--
-- A local completion microstate selects one of the six situated slots and one
-- of the nine ternary comparison states.  Cardinality = 6 x 9 = 54.
------------------------------------------------------------------------

record LocalCompletion54 : Set where
  constructor local-completion-54
  field
    situatedSlot : SituatedSlot
    comparisonState : ComparisonSheet9

open LocalCompletion54 public

localCompletionCount : Nat
localCompletionCount = 54

sixTimesNineIs54 : situatedSlotCount * comparisonSheetCount ≡ localCompletionCount
sixTimesNineIs54 = refl

twoTimesThreeTimesNineIs54 : (2 * 3) * 9 ≡ localCompletionCount
twoTimesThreeTimesNineIs54 = refl

ninePlusFortyFiveIs54 : 9 + 45 ≡ localCompletionCount
ninePlusFortyFiveIs54 = refl

onePlusFiveTimesNineIs54 : (1 + 5) * 9 ≡ localCompletionCount
onePlusFiveTimesNineIs54 = refl

------------------------------------------------------------------------
-- 5. Removing one distinguished global/trivial mode leaves 53.
------------------------------------------------------------------------

localResidualCount : Nat
localResidualCount = 53

onePlusResidualIs54 : 1 + localResidualCount ≡ localCompletionCount
onePlusResidualIs54 = refl

eightPlusFortyFiveIs53 : 8 + 45 ≡ localResidualCount
eightPlusFortyFiveIs53 = refl

------------------------------------------------------------------------
-- 6. The six-slot binary Pareto profile is only a coarse projection of the
-- native ternary situated matrix.
------------------------------------------------------------------------

record TernarySituatedMatrix2x3 : Set where
  constructor ternary-situated-matrix-2x3
  field
    support : Base.TriTruth
    separation : Base.TriTruth
    measurement : Base.TriTruth
    residual : Base.TriTruth
    provenance : Base.TriTruth
    authority : Base.TriTruth

open TernarySituatedMatrix2x3 public

axisLevelToTri : Pareto.AxisLevel → Base.TriTruth
axisLevelToTri Pareto.weak = Base.tri-low
axisLevelToTri Pareto.strong = Base.tri-high

liftBinaryProfile : Pareto.SituatedInformationProfile → TernarySituatedMatrix2x3
liftBinaryProfile profile =
  ternary-situated-matrix-2x3
    (axisLevelToTri (Pareto.supportRichness profile))
    (axisLevelToTri (Pareto.separationAccessibility profile))
    (axisLevelToTri (Pareto.measurementEconomy profile))
    (axisLevelToTri (Pareto.residualDecoupling profile))
    (axisLevelToTri (Pareto.provenanceStrength profile))
    (axisLevelToTri (Pareto.authorityStrength profile))

binaryProfileNeverIntroducesMid :
  (level : Pareto.AxisLevel) → axisLevelToTri level ≡ Base.tri-mid → ⊥
binaryProfileNeverIntroducesMid Pareto.weak ()
binaryProfileNeverIntroducesMid Pareto.strong ()

ternarySituatedValuationCount : Nat
ternarySituatedValuationCount = 729

------------------------------------------------------------------------
-- 7. 27 base x 729 appraisal = 19683 hyperfabric.
------------------------------------------------------------------------

base27Count : Nat
base27Count = 27

baseTimesAppraisalIsFineFibre :
  base27Count * ternarySituatedValuationCount ≡ globalFineFibre
baseTimesAppraisalIsFineFibre = refl

------------------------------------------------------------------------
-- 8. The structural +1 -> +54 analogy is represented explicitly as a change
-- of resolution, not an arithmetic identity.
------------------------------------------------------------------------

record CompletionResolution : Set where
  constructor completion-resolution
  field
    coarseMultiplicity : Nat
    localFineMultiplicity : Nat

canonicalCompletionResolution : CompletionResolution
canonicalCompletionResolution = completion-resolution 1 54

------------------------------------------------------------------------
-- Boundaries.
------------------------------------------------------------------------

data OneEqualsFiftyFour : Set where
data Local54EqualsGlobal19683Fibre : Set where
data Local54EqualsFull729Appraisal : Set where
data BinarySixAxisProfileIsFullTernaryCarrier : Set where
data RemovedTrivialModeEqualsIncludedCompletionChannel : Set where
data CardinalityCoincidenceCreatesMonsterRepresentation : Set where

oneDoesNotEqualFiftyFour : OneEqualsFiftyFour → ⊥
oneDoesNotEqualFiftyFour ()

local54IsNotGlobalFineFibre : Local54EqualsGlobal19683Fibre → ⊥
local54IsNotGlobalFineFibre ()

local54IsNotFull729Appraisal : Local54EqualsFull729Appraisal → ⊥
local54IsNotFull729Appraisal ()

binaryProfileIsNotFullTernaryCarrier : BinarySixAxisProfileIsFullTernaryCarrier → ⊥
binaryProfileIsNotFullTernaryCarrier ()

removedTrivialModeIsNotIncludedCompletionChannel :
  RemovedTrivialModeEqualsIncludedCompletionChannel → ⊥
removedTrivialModeIsNotIncludedCompletionChannel ()

cardinalityDoesNotCreateMonsterRepresentation :
  CardinalityCoincidenceCreatesMonsterRepresentation → ⊥
cardinalityDoesNotCreateMonsterRepresentation ()

record Base369Completion54SituatedTriadBoundary : Set where
  constructor base369-completion54-situated-triad-boundary
  field
    coarseCarrierIsNinePlusOne : Bool
    globalBulkIsNinePlusOneFineFibres : Bool
    situatedShapeIsTwoByThree : Bool
    comparisonSheetIsThreeByThree : Bool
    localCompletionIsSixTimesNine : Bool
    localCompletionIsFiftyFour : Bool
    residualAfterOneModeIsFiftyThree : Bool
    fullSituatedTernaryValuationIs729 : Bool
    base27Times729Is19683 : Bool
    plusOneLiterallyEqualsPlus54 : Bool
    local54Equals729 : Bool
    cardinalityCreatesMonsterAuthority : Bool

canonicalBase369Completion54SituatedTriadBoundary :
  Base369Completion54SituatedTriadBoundary
canonicalBase369Completion54SituatedTriadBoundary =
  base369-completion54-situated-triad-boundary
    true true true true true true true true true false false false
