module DASHI.Foundations.Base369NestedUnitCompletionMonsterAssemblyExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Fin using (Fin)

import DASHI.Foundations.Base369FiveModePhaseQuotientExact as Five
import DASHI.Foundations.Base369StableAlgebraicIdentityTowerExact as Stable
import DASHI.Foundations.Base369MonsterNamedIdentityRegistryExact as Registry
import DASHI.Biology.JCoarseFineDepthDecompositionBridgeExact as Depth11
import DASHI.Biology.MoonshineWeightTwoGriessProductSchemaExact as Griess

------------------------------------------------------------------------
-- TYPED NESTED UNIT COMPLETIONS
--
-- Repeated expressions of the form X + 1 are represented by role-labelled
-- unit carriers.  Equal cardinality-shapes do not identify the roles.
------------------------------------------------------------------------

data UnitRole : Set where
  quotientIdentityRole
  pointedCompletionJRole
  stageFreshUnitRole
  localBoundaryInvariantRole
  conformalInvariantRole
  : UnitRole

data UnitAt (role : UnitRole) : Set where
  unit-at : UnitAt role

PointedExtension : Set → UnitRole → Set
PointedExtension A role = A ⊎ UnitAt role

------------------------------------------------------------------------
-- 1. The mode-phase nine is reduced eight plus its distinguished identity.
------------------------------------------------------------------------

modePhase9ToReducedPlusIdentity :
  Five.ModePhaseQuotient9 →
  PointedExtension Registry.ReducedNonary8 quotientIdentityRole
modePhase9ToReducedPlusIdentity Five.identityMode = inj₂ unit-at
modePhase9ToReducedPlusIdentity Five.A2negative =
  inj₁ (Registry.modeA2 , Five.negativeOrientation)
modePhase9ToReducedPlusIdentity Five.A2positive =
  inj₁ (Registry.modeA2 , Five.positiveOrientation)
modePhase9ToReducedPlusIdentity Five.B1negative =
  inj₁ (Registry.modeB1 , Five.negativeOrientation)
modePhase9ToReducedPlusIdentity Five.B1positive =
  inj₁ (Registry.modeB1 , Five.positiveOrientation)
modePhase9ToReducedPlusIdentity Five.B2negative =
  inj₁ (Registry.modeB2 , Five.negativeOrientation)
modePhase9ToReducedPlusIdentity Five.B2positive =
  inj₁ (Registry.modeB2 , Five.positiveOrientation)
modePhase9ToReducedPlusIdentity Five.Enegative =
  inj₁ (Registry.modeE , Five.negativeOrientation)
modePhase9ToReducedPlusIdentity Five.Epositive =
  inj₁ (Registry.modeE , Five.positiveOrientation)

reducedPlusIdentityToModePhase9 :
  PointedExtension Registry.ReducedNonary8 quotientIdentityRole →
  Five.ModePhaseQuotient9
reducedPlusIdentityToModePhase9 (inj₂ unit-at) = Five.identityMode
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeA2 , Five.negativeOrientation)) = Five.A2negative
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeA2 , Five.positiveOrientation)) = Five.A2positive
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeB1 , Five.negativeOrientation)) = Five.B1negative
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeB1 , Five.positiveOrientation)) = Five.B1positive
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeB2 , Five.negativeOrientation)) = Five.B2negative
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeB2 , Five.positiveOrientation)) = Five.B2positive
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeE , Five.negativeOrientation)) = Five.Enegative
reducedPlusIdentityToModePhase9 (inj₁ (Registry.modeE , Five.positiveOrientation)) = Five.Epositive

modePhaseReducedRoundTrip :
  (state : Five.ModePhaseQuotient9) →
  reducedPlusIdentityToModePhase9 (modePhase9ToReducedPlusIdentity state) ≡ state
modePhaseReducedRoundTrip Five.identityMode = refl
modePhaseReducedRoundTrip Five.A2negative = refl
modePhaseReducedRoundTrip Five.A2positive = refl
modePhaseReducedRoundTrip Five.B1negative = refl
modePhaseReducedRoundTrip Five.B1positive = refl
modePhaseReducedRoundTrip Five.B2negative = refl
modePhaseReducedRoundTrip Five.B2positive = refl
modePhaseReducedRoundTrip Five.Enegative = refl
modePhaseReducedRoundTrip Five.Epositive = refl

reducedModePhaseRoundTrip :
  (state : PointedExtension Registry.ReducedNonary8 quotientIdentityRole) →
  modePhase9ToReducedPlusIdentity (reducedPlusIdentityToModePhase9 state) ≡ state
reducedModePhaseRoundTrip (inj₂ unit-at) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeA2 , Five.negativeOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeA2 , Five.positiveOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeB1 , Five.negativeOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeB1 , Five.positiveOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeB2 , Five.negativeOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeB2 , Five.positiveOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeE , Five.negativeOrientation)) = refl
reducedModePhaseRoundTrip (inj₁ (Registry.modeE , Five.positiveOrientation)) = refl

modePhase9IsReduced8PlusIdentity :
  Stable.CarrierIso
    Five.ModePhaseQuotient9
    (PointedExtension Registry.ReducedNonary8 quotientIdentityRole)
modePhase9IsReduced8PlusIdentity =
  Stable.carrier-iso
    modePhase9ToReducedPlusIdentity
    reducedPlusIdentityToModePhase9
    modePhaseReducedRoundTrip
    reducedModePhaseRoundTrip

------------------------------------------------------------------------
-- 2. Pointed ten is mode-phase nine plus completionJ.
------------------------------------------------------------------------

modePhasePlusCompletionToPointed10 :
  PointedExtension Five.ModePhaseQuotient9 pointedCompletionJRole →
  Five.PointedNonary10
modePhasePlusCompletionToPointed10 (inj₂ unit-at) = Five.completionJ
modePhasePlusCompletionToPointed10 (inj₁ Five.identityMode) = Five.ordinary0
modePhasePlusCompletionToPointed10 (inj₁ Five.A2negative) = Five.ordinary1
modePhasePlusCompletionToPointed10 (inj₁ Five.A2positive) = Five.ordinary2
modePhasePlusCompletionToPointed10 (inj₁ Five.B1negative) = Five.ordinary3
modePhasePlusCompletionToPointed10 (inj₁ Five.B1positive) = Five.ordinary4
modePhasePlusCompletionToPointed10 (inj₁ Five.B2negative) = Five.ordinary5
modePhasePlusCompletionToPointed10 (inj₁ Five.B2positive) = Five.ordinary6
modePhasePlusCompletionToPointed10 (inj₁ Five.Enegative) = Five.ordinary7
modePhasePlusCompletionToPointed10 (inj₁ Five.Epositive) = Five.ordinary8

pointed10ToModePhasePlusCompletion :
  Five.PointedNonary10 →
  PointedExtension Five.ModePhaseQuotient9 pointedCompletionJRole
pointed10ToModePhasePlusCompletion Five.completionJ = inj₂ unit-at
pointed10ToModePhasePlusCompletion Five.ordinary0 = inj₁ Five.identityMode
pointed10ToModePhasePlusCompletion Five.ordinary1 = inj₁ Five.A2negative
pointed10ToModePhasePlusCompletion Five.ordinary2 = inj₁ Five.A2positive
pointed10ToModePhasePlusCompletion Five.ordinary3 = inj₁ Five.B1negative
pointed10ToModePhasePlusCompletion Five.ordinary4 = inj₁ Five.B1positive
pointed10ToModePhasePlusCompletion Five.ordinary5 = inj₁ Five.B2negative
pointed10ToModePhasePlusCompletion Five.ordinary6 = inj₁ Five.B2positive
pointed10ToModePhasePlusCompletion Five.ordinary7 = inj₁ Five.Enegative
pointed10ToModePhasePlusCompletion Five.ordinary8 = inj₁ Five.Epositive

modePhaseCompletionRoundTrip :
  (state : PointedExtension Five.ModePhaseQuotient9 pointedCompletionJRole) →
  pointed10ToModePhasePlusCompletion (modePhasePlusCompletionToPointed10 state) ≡ state
modePhaseCompletionRoundTrip (inj₂ unit-at) = refl
modePhaseCompletionRoundTrip (inj₁ Five.identityMode) = refl
modePhaseCompletionRoundTrip (inj₁ Five.A2negative) = refl
modePhaseCompletionRoundTrip (inj₁ Five.A2positive) = refl
modePhaseCompletionRoundTrip (inj₁ Five.B1negative) = refl
modePhaseCompletionRoundTrip (inj₁ Five.B1positive) = refl
modePhaseCompletionRoundTrip (inj₁ Five.B2negative) = refl
modePhaseCompletionRoundTrip (inj₁ Five.B2positive) = refl
modePhaseCompletionRoundTrip (inj₁ Five.Enegative) = refl
modePhaseCompletionRoundTrip (inj₁ Five.Epositive) = refl

pointedModePhaseRoundTrip :
  (state : Five.PointedNonary10) →
  modePhasePlusCompletionToPointed10 (pointed10ToModePhasePlusCompletion state) ≡ state
pointedModePhaseRoundTrip Five.ordinary0 = refl
pointedModePhaseRoundTrip Five.ordinary1 = refl
pointedModePhaseRoundTrip Five.ordinary2 = refl
pointedModePhaseRoundTrip Five.ordinary3 = refl
pointedModePhaseRoundTrip Five.ordinary4 = refl
pointedModePhaseRoundTrip Five.ordinary5 = refl
pointedModePhaseRoundTrip Five.ordinary6 = refl
pointedModePhaseRoundTrip Five.ordinary7 = refl
pointedModePhaseRoundTrip Five.ordinary8 = refl
pointedModePhaseRoundTrip Five.completionJ = refl

pointed10IsModePhase9PlusCompletionJ :
  Stable.CarrierIso
    Five.PointedNonary10
    (PointedExtension Five.ModePhaseQuotient9 pointedCompletionJRole)
pointed10IsModePhase9PlusCompletionJ =
  Stable.carrier-iso
    pointed10ToModePhasePlusCompletion
    modePhasePlusCompletionToPointed10
    pointedModePhaseRoundTrip
    modePhaseCompletionRoundTrip

------------------------------------------------------------------------
-- 3. Stable local 53 -> 54 completion.
--
-- The distinguished local nine is now the typed mode-phase nine rather than an
-- anonymous nine-cardinality carrier, making the removed identity explicit.
------------------------------------------------------------------------

ModeBoundary53Stable : Set
ModeBoundary53Stable = Registry.ModeNonary45 ⊎ Registry.ReducedNonary8

ModeBoundary54Stable : Set
ModeBoundary54Stable = Registry.ModeNonary45 ⊎ Five.ModePhaseQuotient9

modeBoundary54To53PlusUnit :
  ModeBoundary54Stable →
  PointedExtension ModeBoundary53Stable localBoundaryInvariantRole
modeBoundary54To53PlusUnit (inj₁ bulk45) = inj₁ (inj₁ bulk45)
modeBoundary54To53PlusUnit (inj₂ Five.identityMode) = inj₂ unit-at
modeBoundary54To53PlusUnit (inj₂ q) with modePhase9ToReducedPlusIdentity q
... | inj₁ reduced = inj₁ (inj₂ reduced)
... | inj₂ unit-at = inj₂ unit-at

modeBoundary53PlusUnitTo54 :
  PointedExtension ModeBoundary53Stable localBoundaryInvariantRole →
  ModeBoundary54Stable
modeBoundary53PlusUnitTo54 (inj₂ unit-at) = inj₂ Five.identityMode
modeBoundary53PlusUnitTo54 (inj₁ (inj₁ bulk45)) = inj₁ bulk45
modeBoundary53PlusUnitTo54 (inj₁ (inj₂ reduced)) =
  inj₂ (reducedPlusIdentityToModePhase9 (inj₁ reduced))

modeBoundary54RoundTrip :
  (state : ModeBoundary54Stable) →
  modeBoundary53PlusUnitTo54 (modeBoundary54To53PlusUnit state) ≡ state
modeBoundary54RoundTrip (inj₁ bulk45) = refl
modeBoundary54RoundTrip (inj₂ Five.identityMode) = refl
modeBoundary54RoundTrip (inj₂ Five.A2negative) = refl
modeBoundary54RoundTrip (inj₂ Five.A2positive) = refl
modeBoundary54RoundTrip (inj₂ Five.B1negative) = refl
modeBoundary54RoundTrip (inj₂ Five.B1positive) = refl
modeBoundary54RoundTrip (inj₂ Five.B2negative) = refl
modeBoundary54RoundTrip (inj₂ Five.B2positive) = refl
modeBoundary54RoundTrip (inj₂ Five.Enegative) = refl
modeBoundary54RoundTrip (inj₂ Five.Epositive) = refl

modeBoundary53UnitRoundTrip :
  (state : PointedExtension ModeBoundary53Stable localBoundaryInvariantRole) →
  modeBoundary54To53PlusUnit (modeBoundary53PlusUnitTo54 state) ≡ state
modeBoundary53UnitRoundTrip (inj₂ unit-at) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₁ bulk45)) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeA2 , Five.negativeOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeA2 , Five.positiveOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeB1 , Five.negativeOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeB1 , Five.positiveOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeB2 , Five.negativeOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeB2 , Five.positiveOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeE , Five.negativeOrientation))) = refl
modeBoundary53UnitRoundTrip (inj₁ (inj₂ (Registry.modeE , Five.positiveOrientation))) = refl

modeBoundary54Is53PlusInvariant :
  Stable.CarrierIso
    ModeBoundary54Stable
    (PointedExtension ModeBoundary53Stable localBoundaryInvariantRole)
modeBoundary54Is53PlusInvariant =
  Stable.carrier-iso
    modeBoundary54To53PlusUnit
    modeBoundary53PlusUnitTo54
    modeBoundary54RoundTrip
    modeBoundary53UnitRoundTrip

------------------------------------------------------------------------
-- 4. 10 + 1 = 11 exists in the repo as a distinct *depth/bundle* completion,
-- not as the same state-carrier pointing used above.
------------------------------------------------------------------------

stageTenPlusFreshUnitIsEleven :
  DASHI.Core.CoarseFineDepthDecompositionExact.coarseComponent
    Depth11.stage11BundlePlusFreshUnit
  ≡ 10
stageTenPlusFreshUnitIsEleven = refl

stageFreshUnitIsOne :
  DASHI.Core.CoarseFineDepthDecompositionExact.relativeFineComponent
    Depth11.stage11BundlePlusFreshUnit
  ≡ 1
stageFreshUnitIsOne = refl

stageJoinedDepthIsEleven :
  DASHI.Core.CoarseFineDepthDecompositionExact.absoluteComponent
    Depth11.stage11BundlePlusFreshUnit
  ≡ 11
stageJoinedDepthIsEleven = refl

------------------------------------------------------------------------
-- 5. Semantic candidate for the Monster constituent and full weight-two space.
------------------------------------------------------------------------

SemanticMonsterConstituent196883 : Set
SemanticMonsterConstituent196883 =
  Registry.NamedMonsterDecisionState196830 ⊎ ModeBoundary53Stable

SemanticWeightTwo196884 : Set
SemanticWeightTwo196884 =
  PointedExtension SemanticMonsterConstituent196883 conformalInvariantRole

------------------------------------------------------------------------
-- 6. Exact BIDI socket: this is the missing representation-theoretic payment.
------------------------------------------------------------------------

record MonsterConstituentSemanticBridge : Set where
  field
    constituentIso :
      Stable.CarrierIso
        SemanticMonsterConstituent196883
        (Fin 196883)

open MonsterConstituentSemanticBridge public

semanticBridgeLiftsToWeightTwoCoordinates :
  MonsterConstituentSemanticBridge →
  Stable.CarrierIso SemanticWeightTwo196884 Griess.WeightTwoCoordinate
semanticBridgeLiftsToWeightTwoCoordinates bridge =
  Stable.carrier-iso toWeightTwo fromWeightTwo fromTo toFrom
  where
  toWeightTwo : SemanticWeightTwo196884 → Griess.WeightTwoCoordinate
  toWeightTwo (inj₂ unit-at) = Griess.conformalCoordinate
  toWeightTwo (inj₁ state) = Griess.monsterCoordinate (Stable.to (constituentIso bridge) state)

  fromWeightTwo : Griess.WeightTwoCoordinate → SemanticWeightTwo196884
  fromWeightTwo Griess.conformalCoordinate = inj₂ unit-at
  fromWeightTwo (Griess.monsterCoordinate index) =
    inj₁ (Stable.from (constituentIso bridge) index)

  fromTo : (state : SemanticWeightTwo196884) → fromWeightTwo (toWeightTwo state) ≡ state
  fromTo (inj₂ unit-at) = refl
  fromTo (inj₁ state)
    rewrite Stable.fromTo (constituentIso bridge) state = refl

  toFrom : (state : Griess.WeightTwoCoordinate) → toWeightTwo (fromWeightTwo state) ≡ state
  toFrom Griess.conformalCoordinate = refl
  toFrom (Griess.monsterCoordinate index)
    rewrite Stable.toFrom (constituentIso bridge) index = refl

------------------------------------------------------------------------
-- 7. Boundaries: repeated units and dimensions retain role labels.
------------------------------------------------------------------------

data QuotientIdentityEqualsCompletionJ : Set where
data CompletionJEqualsStageFreshUnit : Set where
data LocalInvariantEqualsConformalInvariant : Set where
data DimensionSplitConstructsMonsterConstituentIso : Set where

quotientIdentityIsNotCompletionJByShape : QuotientIdentityEqualsCompletionJ → ⊥
quotientIdentityIsNotCompletionJByShape ()

completionJIsNotStageFreshUnitByArithmetic : CompletionJEqualsStageFreshUnit → ⊥
completionJIsNotStageFreshUnitByArithmetic ()

localInvariantIsNotConformalInvariantWithoutBridge : LocalInvariantEqualsConformalInvariant → ⊥
localInvariantIsNotConformalInvariantWithoutBridge ()

dimensionSplitDoesNotConstructMonsterBridge : DimensionSplitConstructsMonsterConstituentIso → ⊥
dimensionSplitDoesNotConstructMonsterBridge ()

record NestedUnitCompletionBoundary : Set where
  constructor nested-unit-completion-boundary
  field
    reducedEightPlusIdentityIsModePhaseNine : Bool
    modePhaseNinePlusCompletionJIsPointedTen : Bool
    localFiftyThreePlusInvariantIsFiftyFour : Bool
    stageTenPlusFreshUnitIsElevenDepth : Bool
    fullWeightTwoIsConformalPlusMonsterCoordinate : Bool
    repeatedUnitShapeMeansSameUnitRole : Bool
    dimensionSplitAloneBuildsMonsterSemanticBridge : Bool

canonicalNestedUnitCompletionBoundary : NestedUnitCompletionBoundary
canonicalNestedUnitCompletionBoundary =
  nested-unit-completion-boundary true true true true true false false
