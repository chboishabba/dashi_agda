module DASHI.Moonshine.JInvariantSheafHyperformAdmissibleDescentExact where

------------------------------------------------------------------------
-- J/369 SHEAF-LIKE DESCENT / ADMISSIBLE HYPERFABRIC CROSS-POLLINATION
--
-- This module does not introduce a competing ontology.  It connects the
-- existing jCoarse/jFine observer, ConsumerDescent/FactorsThrough,
-- CoarseFineRelativeFibre, Base369 hyperfabric, stratum admissibility and
-- WrongType machinery through one restriction/overlap vocabulary.
--
-- The categorical layer below is deliberately interface-level: it records
-- contravariant restriction and admissible pullback/pushout-shaped gluing.
-- It does not claim that the finite J/369 chart is already a literal
-- Grothendieck site for the analytic modular curve.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.ComputerScience.WrongTypeAttributionFactorisationPlanningSnowballExact as Wrong
import DASHI.Foundations.Base369CoarseFineFabricAdapterExact as Fabric
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Geometry
import DASHI.Foundations.Base369Ternary27StratumStabiliserFibreAdmissibilityExact as Admissible
import DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact as J
import DASHI.Moonshine.JInvariantFibonacciJCoarseFineVoxelBidiExact as Voxel
import DASHI.Moonshine.JInvariantJCoarseFineElevenTritChartShiftExact as Shift
import DASHI.Moonshine.JInvariantColourWheelNineSheetPantsGluingExact as Pants

------------------------------------------------------------------------
-- 1. Minimal contravariant restriction interface.
------------------------------------------------------------------------

record ChartRestrictionCategory : Set₁ where
  field
    Chart : Set
    Restriction : Chart → Chart → Set
    identity : (U : Chart) → Restriction U U
    compose :
      {U V W : Chart} →
      Restriction V W →
      Restriction U V →
      Restriction U W

open ChartRestrictionCategory public

record PresheafInterface (C : ChartRestrictionCategory) : Set₁ where
  field
    Section : Chart C → Set
    restrict :
      {U V : Chart C} →
      Restriction C V U →
      Section U →
      Section V
    restrictIdentity :
      (U : Chart C) →
      (s : Section U) →
      restrict (identity C U) s ≡ s
    restrictCompose :
      {U V W : Chart C} →
      (g : Restriction C V W) →
      (f : Restriction C U V) →
      (s : Section W) →
      restrict (compose C g f) s ≡ restrict f (restrict g s)

open PresheafInterface public

------------------------------------------------------------------------
-- 2. Pullback-shaped compatible overlaps and pushout-shaped gluing interface.
------------------------------------------------------------------------

record CompatibleOverlap
    {Left Right Boundary : Set}
    (leftBoundary : Left → Boundary)
    (rightBoundary : Right → Boundary) : Set where
  constructor compatible-overlap
  field
    left : Left
    right : Right
    sameBoundary : leftBoundary left ≡ rightBoundary right

open CompatibleOverlap public

record AdmissibleOverlap
    {Left Right Boundary : Set}
    (leftBoundary : Left → Boundary)
    (rightBoundary : Right → Boundary)
    (Allowed : Left → Right → Set) : Set where
  constructor admissible-overlap
  field
    overlap : CompatibleOverlap leftBoundary rightBoundary
    allowed : Allowed (left overlap) (right overlap)

open AdmissibleOverlap public

record AdmissiblePushoutInterface
    {Left Right Seam : Set}
    (seamLeft : Seam → Left)
    (seamRight : Seam → Right) : Set₁ where
  field
    Glued : Set
    includeLeft : Left → Glued
    includeRight : Right → Glued
    seamCommutes :
      (s : Seam) →
      includeLeft (seamLeft s) ≡ includeRight (seamRight s)
    descend :
      {Target : Set} →
      (fromLeft : Left → Target) →
      (fromRight : Right → Target) →
      ((s : Seam) → fromLeft (seamLeft s) ≡ fromRight (seamRight s)) →
      Glued → Target

open AdmissiblePushoutInterface public

------------------------------------------------------------------------
-- 3. The local J observer is a restriction/evaluation map.
------------------------------------------------------------------------

localJRestriction : J.StructuredJField → J.LocalJ27
localJRestriction = J.localJObserver

chosenLocalValue : J.StructuredJField → Base369.TriTruth
chosenLocalValue state = proj₂ (J.localJObserver state)

chosenLocalValueFactorsThroughLocalJ :
  Descent.FactorsThrough localJRestriction chosenLocalValue
chosenLocalValueFactorsThroughLocalJ =
  Factorized.factorizedRefinement proj₂ (λ state → refl)

q11CannotFactorThroughLocalJ :
  Descent.FactorsThrough localJRestriction (J.fineFieldAt J.q11) → ⊥
q11CannotFactorThroughLocalJ factor =
  J.localJ27CannotSufficeForQ11Consumer
    (Descent.fibreConstantIsConsumerSufficient
      (Descent.factorsThroughImpliesFibreConstant factor))

------------------------------------------------------------------------
-- 4. The existing J collision literally inhabits the self-pullback of the
--    local observer: two distinct global sections can agree on one local view.
------------------------------------------------------------------------

JLocalPullback : Set
JLocalPullback =
  Σ J.StructuredJField
    (λ leftState →
      Σ J.StructuredJField
        (λ rightState →
          localJRestriction leftState ≡ localJRestriction rightState))

jLocalCollisionInPullback : JLocalPullback
jLocalCollisionInPullback =
  J.leftJState , (J.rightJState , J.sameLocalJ27)

jLocalPullbackCarriesHiddenResidual :
  J.fineFieldAt J.q11 J.leftJState
  ≡ J.fineFieldAt J.q11 J.rightJState → ⊥
jLocalPullbackCarriesHiddenResidual = J.q11ConsumerDiffers

------------------------------------------------------------------------
-- 5. Base369 coarse/fine reopening gives the analogous hyperfabric pullback.
------------------------------------------------------------------------

Base369InteractionPullback : Set
Base369InteractionPullback =
  Σ Geometry.TernaryHyperformalPoint
    (λ leftState →
      Σ Geometry.TernaryHyperformalPoint
        (λ rightState →
          Geometry.projectInteractionVoxel leftState
          ≡ Geometry.projectInteractionVoxel rightState))

base369SameInteractionNeedsFineForIdentity :
  {left right : Geometry.TernaryHyperformalPoint} →
  Geometry.projectInteractionVoxel left
  ≡ Geometry.projectInteractionVoxel right →
  Geometry.projectAppraisalFibre left
  ≡ Geometry.projectAppraisalFibre right →
  left ≡ right
base369SameInteractionNeedsFineForIdentity =
  Fabric.base369InteractionPlusAppraisalDeterminesState

base369RelativeFineMustSeparateDistinctStates :
  {left right : Geometry.TernaryHyperformalPoint} →
  Geometry.projectInteractionVoxel left
  ≡ Geometry.projectInteractionVoxel right →
  (left ≡ right → ⊥) →
  Geometry.projectAppraisalFibre left
  ≡ Geometry.projectAppraisalFibre right → ⊥
base369RelativeFineMustSeparateDistinctStates =
  Fibre.relativeFineMustChangeInsideNontrivialCoarseFibre
    Fabric.base369CoarseFineReopening

------------------------------------------------------------------------
-- 6. WrongType: equal surface/cardinality is not admissibility.
------------------------------------------------------------------------

jQ11FactorisationObligation : Wrong.IndexedObligation
jQ11FactorisationObligation =
  Wrong.indexed-obligation
    Wrong.consumerFactorisationObligation
    "JCoarse/JFine:q11-consumer"
    "DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact.fineFieldAt-q11"
    "local-27 observer fibre"

local27Candidate : Wrong.OfferedCandidate
local27Candidate =
  Wrong.offered-candidate
    "JCoarse/JFine local 27"
    "coarse observer"
    "DASHI.Moonshine.JInvariantRiemannObserverResidualSufficiencyBidiExact.localJObserver"
    true

local27Q11WrongTypeReceipt : Wrong.WrongTypeErrorReceipt
local27Q11WrongTypeReceipt =
  Wrong.wrong-type-error-receipt
    jQ11FactorisationObligation
    local27Candidate
    Wrong.nonFactorableRepresentation
    "explicit same-local-27 / different-q11 fine-field witness"
    true

data CardinalCompatibilityImpliesAdmissibleGluing : Set where

cardinalityDoesNotCreateAdmissibleGluing :
  CardinalCompatibilityImpliesAdmissibleGluing → ⊥
cardinalityDoesNotCreateAdmissibleGluing ()

------------------------------------------------------------------------
-- 7. Existing 11-trit chart shift and pants path are retained as rechartings,
--    not promoted to analytic modular gluing.
------------------------------------------------------------------------

outerElevenTritDepthExact : Bool
outerElevenTritDepthExact = true

jElevenTritDepthExact : Bool
jElevenTritDepthExact = true

finiteOneTenTwoNineRechartExact : Bool
finiteOneTenTwoNineRechartExact = true

nineSheetPantsTwoExact : Bool
nineSheetPantsTwoExact = true

localTwentySevenPantsThreeExact : Bool
localTwentySevenPantsThreeExact = true

literalAnalyticGrothendieckSiteConstructedHere : Bool
literalAnalyticGrothendieckSiteConstructedHere = false

literalSmoothPantsPushoutConstructedHere : Bool
literalSmoothPantsPushoutConstructedHere = false

------------------------------------------------------------------------
-- 8. Cross-owner receipts expose the existing admissibility/firewall state.
------------------------------------------------------------------------

base369CoarseFineBoundary :
  Fabric.Base369CoarseFineBoundary
base369CoarseFineBoundary =
  Fabric.canonicalBase369CoarseFineBoundary

base369StratumAdmissibilityBoundary :
  Admissible.StratumStabiliserFibreBoundary
base369StratumAdmissibilityBoundary =
  Admissible.canonicalStratumStabiliserFibreBoundary

jResidualGovernance :
  J.JResidualSufficiencyGovernance
jResidualGovernance =
  J.canonicalJResidualSufficiencyGovernance

jVoxelFrontier :
  Voxel.JCoarseFineVoxelFrontier
jVoxelFrontier =
  Voxel.canonicalJCoarseFineVoxelFrontier

jChartShiftFrontier :
  Shift.ElevenTritChartShiftFrontier
jChartShiftFrontier =
  Shift.canonicalElevenTritChartShiftFrontier

jPantsBoundary :
  Pants.ColourWheelNinePantsBoundary
jPantsBoundary =
  Pants.canonicalColourWheelNinePantsBoundary

------------------------------------------------------------------------
-- 9. Consolidated frontier.
------------------------------------------------------------------------

record JSheafHyperformDescentFrontier : Set where
  constructor j-sheaf-hyperform-descent-frontier
  field
    localJRestrictionExact : Bool
    chosenConsumerFactorsThroughLocalJ : Bool
    hiddenFineConsumerNonDescentExact : Bool
    jObserverSelfPullbackCollisionInhabited : Bool
    base369CoarseFineReopeningReused : Bool
    base369RelativeFineSeparatesDistinctCoarseFibreStates : Bool
    wrongTypeReceiptForLocal27AsQ11Answer : Bool
    cardinalityAloneCreatesAdmissibleGluing : Bool
    onePlusTenTwoPlusNineRechartExact : Bool
    pantsFiniteRechartsExact : Bool
    literalGrothendieckTopologyConstructed : Bool
    literalAnalyticModularSheafIdentified : Bool
    literalSmoothPantsPushoutConstructed : Bool

canonicalJSheafHyperformDescentFrontier :
  JSheafHyperformDescentFrontier
canonicalJSheafHyperformDescentFrontier =
  j-sheaf-hyperform-descent-frontier
    true true true true true true true false true true false false false
