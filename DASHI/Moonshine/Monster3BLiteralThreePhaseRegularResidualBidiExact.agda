module DASHI.Moonshine.Monster3BLiteralThreePhaseRegularResidualBidiExact where

------------------------------------------------------------------------
-- LITERAL THREE-PHASE VOA CARRIER -> REGULAR C3 BULK -> RESIDUAL 53
--
-- The selected 3B phase source already owns ONE literal central action on the
-- VOA carrier.  Its three dependent eigenspaces are therefore not parallel
-- carriers: they are fibres of that same action.
--
-- Character authority says
--
--   W|C3 = 65610 Reg(C3) + 53 * 1.
--
-- The zeta sector already has an ActualZetaSectorRecognition in the current
-- BIDI lane.  The new scientific leaf is consequently: recognize a 65610
-- regular block inside the literal phase-one eigenspace.  Once that block and
-- a complementary residual are supplied, the 53 is a SAME-ACTION residual.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.Monster3BCentralCharacterInertiaExact as Inertia
import DASHI.Moonshine.Monster3BMultiplicityEvaluationExact as Recognition
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as VOA
import DASHI.Moonshine.Monster3BRegularC3BulkResidualFiftyThreeBidiExact as Character

------------------------------------------------------------------------
-- 1. Literal eigenspaces from the SAME central action.
------------------------------------------------------------------------

LiteralPhaseSector :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.ActualMonster3BVOAPhaseActionSource G K group →
  Inertia.CentralPhase3 → Set
LiteralPhaseSector source phase =
  Inertia.CentralEigenspace
    (Inertia.phaseAction (VOA.normalizerActionFromVOA source)) phase

LiteralOneSector :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.ActualMonster3BVOAPhaseActionSource G K group → Set
LiteralOneSector source = LiteralPhaseSector source Inertia.phaseOne

LiteralZetaSector :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.ActualMonster3BVOAPhaseActionSource G K group → Set
LiteralZetaSector source = LiteralPhaseSector source Inertia.phaseZeta

LiteralZetaSquaredSector :
  ∀ {G K : Set} {group : GR.Group G} →
  VOA.ActualMonster3BVOAPhaseActionSource G K group → Set
LiteralZetaSquaredSector source =
  LiteralPhaseSector source Inertia.phaseZetaSquared

literalZetaAliasAgrees :
  ∀ {G K : Set} {group : GR.Group G}
    (source : VOA.ActualMonster3BVOAPhaseActionSource G K group) →
  LiteralZetaSector source ≡ VOA.literalVOAZetaSector source
literalZetaAliasAgrees source = refl

------------------------------------------------------------------------
-- 2. Attach the already-existing zeta recognition to this literal family.
------------------------------------------------------------------------

record LiteralThreePhaseRecognizedSource
    (G K : Set) (group : GR.Group G) : Setω where
  field
    phaseSource : VOA.ActualMonster3BVOAPhaseActionSource G K group
    zetaRecognition :
      Recognition.ActualZetaSectorRecognition (LiteralZetaSector phaseSource)

open LiteralThreePhaseRecognizedSource public

------------------------------------------------------------------------
-- 3. The decisive missing lift: a regular 65610 block INSIDE W_1 and a
--    complementary 53 residual, both stable under one selected actor action.
--
-- We intentionally do not infer this from the character identity alone.
------------------------------------------------------------------------

record LiteralFixedRegularResidualRecognition
    {G K : Set} {group : GR.Group G}
    (source : LiteralThreePhaseRecognizedSource G K group) : Setω where
  field
    Actor : Set
    actorActOne : Actor → LiteralOneSector (phaseSource source)
      → LiteralOneSector (phaseSource source)

    RegularFixed Residual53 : Set
    regularAct : Actor → RegularFixed → RegularFixed
    residualAct : Actor → Residual53 → Residual53

    splitOne :
      LiteralOneSector (phaseSource source) → RegularFixed ⊎ Residual53
    combineOne :
      RegularFixed ⊎ Residual53 → LiteralOneSector (phaseSource source)

    combineAfterSplit :
      (state : LiteralOneSector (phaseSource source)) →
      combineOne (splitOne state) ≡ state
    splitAfterCombine :
      (state : RegularFixed ⊎ Residual53) →
      splitOne (combineOne state) ≡ state

    regularStable :
      (actor : Actor) → (state : RegularFixed) →
      splitOne (actorActOne actor (combineOne (inj₁ state)))
      ≡ inj₁ (regularAct actor state)

    residualStable :
      (actor : Actor) → (state : Residual53) →
      splitOne (actorActOne actor (combineOne (inj₂ state)))
      ≡ inj₂ (residualAct actor state)

    -- Recognize the regular fixed block by the SAME 729 x 90 model already
    -- used by W_zeta.  This is the theorem-bearing replacement for a bare
    -- dimension-65610 assumption.
    regularRecognition : Recognition.ActualZetaSectorRecognition RegularFixed

    residualDimension : Nat
    residualDimensionIs53 : residualDimension ≡ 53

open LiteralFixedRegularResidualRecognition public

------------------------------------------------------------------------
-- 4. Once supplied, the 196830 bulk is literally three regular phase blocks:
--    fixed-regular, zeta, zeta-squared.  The zeta-squared recognition remains
--    separable because generator inversion/normalizer transport is a distinct
--    action theorem.
------------------------------------------------------------------------

record LiteralThreeRegularPhaseBulkRecognition
    {G K : Set} {group : GR.Group G}
    (source : LiteralThreePhaseRecognizedSource G K group)
    (fixed : LiteralFixedRegularResidualRecognition source) : Setω where
  field
    zetaSquaredRecognition :
      Recognition.ActualZetaSectorRecognition
        (LiteralZetaSquaredSector (phaseSource source))

------------------------------------------------------------------------
-- 5. BIDI boundary.
------------------------------------------------------------------------

record LiteralThreePhaseResidualBoundary : Set where
  constructor literalThreePhaseResidualBoundary
  field
    allThreeLiteralPhaseFibresUseSameCentralAction : Bool
    zetaRecognitionAlreadyExistingLeaf : Bool
    characterRegularC3BulkAlreadyExact : Bool
    fixedRegular729Times90RecognitionIsLive : Bool
    fixedResidual53ComplementIsLive : Bool
    zetaSquaredRecognitionOrTransportIsLive : Bool
    characterIdentityConstructsFixedSubspace : Bool
    residual53IsAlbertByDimension : Bool

canonicalLiteralThreePhaseResidualBoundary : LiteralThreePhaseResidualBoundary
canonicalLiteralThreePhaseResidualBoundary =
  literalThreePhaseResidualBoundary
    true true true
    true true true
    false false
