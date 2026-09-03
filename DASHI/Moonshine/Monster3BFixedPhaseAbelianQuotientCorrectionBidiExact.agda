module DASHI.Moonshine.Monster3BFixedPhaseAbelianQuotientCorrectionBidiExact where

------------------------------------------------------------------------
-- FIXED-PHASE CORRECTION: CENTRAL-TRIVIAL != SCHRODINGER 729
--
-- For the extraspecial 3^(1+12) Heisenberg kernel E, the two nonlinear
-- degree-3^6 Stone-von-Neumann representations belong to the two NONTRIVIAL
-- central characters.  The central-trivial phase instead factors through
--
--   E / Z(E) = F3^12 = X6 + X6*.
--
-- Hence a 65610-dimensional block in W_1 must NOT be required to satisfy the
-- zeta-sector ActualZetaSectorRecognition API.  Its correct representation-
-- theoretic frontier is an action/decomposition through the abelian quotient.
--
-- This file does not manufacture that decomposition.  It replaces the wrong
-- target by a typed quotient-character recognition interface and preserves the
-- residual-53 split as a separate same-action obligation.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.Base369Monster3BVOAActionPhaseAdapterBidiExact as VOA
import DASHI.Moonshine.Monster3BLiteralThreePhaseRegularResidualBidiExact as Phase
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as Heis

------------------------------------------------------------------------
-- 1. Literal quotient-character label carrier.
------------------------------------------------------------------------

FixedCharacterLabel : Set
FixedCharacterLabel = Heis.Symplectic12

------------------------------------------------------------------------
-- 2. Correct fixed-phase recognition frontier.
--
-- The decomposition fibres are abstract because the actual inertia/orbit
-- multiplicities have not yet been computed.  What is fixed here is the
-- representation TYPE: labels live on E/Z(E), not on the 729-dimensional
-- Schrodinger basis X6.
------------------------------------------------------------------------

record FixedPhaseAbelianQuotientRecognition
    {G K : Set} {group : GR.Group G}
    (source : Phase.LiteralThreePhaseRecognizedSource G K group) : Setω where
  field
    Actor : Set
    actorActOne : Actor → Phase.LiteralOneSector (Phase.phaseSource source)
      → Phase.LiteralOneSector (Phase.phaseSource source)

    CharacterCarrier Residual53 : Set
    characterAct : Actor → CharacterCarrier → CharacterCarrier
    residualAct : Actor → Residual53 → Residual53

    splitOne :
      Phase.LiteralOneSector (Phase.phaseSource source)
      → CharacterCarrier ⊎ Residual53
    combineOne :
      CharacterCarrier ⊎ Residual53
      → Phase.LiteralOneSector (Phase.phaseSource source)

    combineAfterSplit :
      (state : Phase.LiteralOneSector (Phase.phaseSource source)) →
      combineOne (splitOne state) ≡ state
    splitAfterCombine :
      (state : CharacterCarrier ⊎ Residual53) →
      splitOne (combineOne state) ≡ state

    characterStable :
      (actor : Actor) → (state : CharacterCarrier) →
      splitOne (actorActOne actor (combineOne (inj₁ state)))
      ≡ inj₁ (characterAct actor state)

    residualStable :
      (actor : Actor) → (state : Residual53) →
      splitOne (actorActOne actor (combineOne (inj₂ state)))
      ≡ inj₂ (residualAct actor state)

    -- Quotient-character observer.  The actual theorem still required is that
    -- this observer and its fibres reconstruct the desired 65610 block under
    -- the selected inertia action.
    characterLabel : CharacterCarrier → FixedCharacterLabel

    characterBlockDimension : Nat
    residualDimension : Nat
    characterBlockDimensionIs65610 : characterBlockDimension ≡ 65610
    residualDimensionIs53 : residualDimension ≡ 53

open FixedPhaseAbelianQuotientRecognition public

------------------------------------------------------------------------
-- 3. Scientific boundary / correction receipt.
------------------------------------------------------------------------

record FixedPhaseCorrectionBoundary : Set where
  constructor fixedPhaseCorrectionBoundary
  field
    extraspecialQuotientIsTwelveTritCarrier : Bool
    zetaUsesNontrivialCentralCharacter : Bool
    zetaSquaredUsesNontrivialCentralCharacter : Bool
    fixedPhaseCentralCharacterIsTrivial : Bool
    fixedPhaseShouldUseZeta729Recognition : Bool
    fixedPhaseShouldFactorThroughAbelianQuotient : Bool
    fixed65610CharacterBlockConstructedHere : Bool
    residual53ConstructedHere : Bool

canonicalFixedPhaseCorrectionBoundary : FixedPhaseCorrectionBoundary
canonicalFixedPhaseCorrectionBoundary =
  fixedPhaseCorrectionBoundary
    true true true true
    false true
    false false

------------------------------------------------------------------------
-- 4. Consequence for the previous frontier.
--
-- The old field
--   regularRecognition : ActualZetaSectorRecognition RegularFixed
-- was a deliberately-live hypothesis, not an inhabited theorem.  This owner
-- records that it is not the target to pursue.  The live replacement is the
-- quotient-character decomposition above.
------------------------------------------------------------------------
