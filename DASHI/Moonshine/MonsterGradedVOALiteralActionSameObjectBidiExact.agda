module DASHI.Moonshine.MonsterGradedVOALiteralActionSameObjectBidiExact where

------------------------------------------------------------------------
-- MONSTER GRADED CHARACTER AUTHORITY <-> LITERAL VOA STATE ACTION
--
-- The repository currently has two complementary Moonshine-facing APIs:
--
--   MonsterGradedVOABridgeExact
--     * exact graded trace
--     * exact Monster character-table authority
--     * first Moonshine coefficient bridge
--
--   VertexOperatorAlgebraCore.MoonshineVOABridge
--     * literal VOA carrier
--     * literal group action g -> (v -> g.v)
--     * graded representation on that same group
--
-- The point of this owner is NOT to construct a fresh representation.  It
-- packages a same-object weld in which the literal VOA bridge is indexed by
-- the exact group already carried by the older graded-VOA action surface.
-- The remaining receipts say that the literal graded representation and the
-- graded-character projections really are the same ones used by the trace
-- authority.
--
-- Thus one selected Monster element g can simultaneously be consumed as:
--
--   * a class/character/graded-trace probe, and
--   * an actual endomorphism of the literal VOA state carrier.
--
-- This is the seam needed by the selected-3B/eigenspace lane.  It does not
-- identify V^natural, prove that the full automorphism group is the Monster,
-- recover a 3B element, or prove ActualZetaSectorRecognition.
------------------------------------------------------------------------

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Moonshine.GradedRepresentation as GR
import DASHI.Moonshine.GradedVertexOperatorAlgebraBoundary as GVOA
import DASHI.Moonshine.MonsterGradedVOABridgeExact as Legacy
import DASHI.Moonshine.VertexOperatorAlgebraCore as Core

------------------------------------------------------------------------
-- 1. Same-object weld.
------------------------------------------------------------------------

record MonsterGradedVOALiteralActionWeld (Monster K : Set) : Setω where
  field
    gradedAuthority : Legacy.MonsterGradedVOABridge Monster K

    -- Deliberately index the literal bridge by the SAME group object already
    -- used by the legacy VOA-with-group-action.  No group cardinality or name
    -- comparison is accepted here.
    literalVOA :
      Core.MoonshineVOABridge Monster K
        (GVOA.group (Legacy.voaAction gradedAuthority))

    -- The literal bridge's declared graded representation is the exact
    -- representation used by the trace authority.
    sameGradedRepresentation :
      Core.monsterGradedRepresentation literalVOA
      ≡ GVOA.gradedRepresentation (Legacy.voaAction gradedAuthority)

    -- Its internal graded-character package must point back to that same
    -- representation and the same literal state action, rather than silently
    -- carrying parallel objects.
    gradedCharacterUsesSameRepresentation :
      Core.VOAGradedCharacter.gradedRepresentation
        (Core.gradedCharacter literalVOA)
      ≡ Core.monsterGradedRepresentation literalVOA

    gradedCharacterUsesSameAction :
      Core.VOAGradedCharacter.action
        (Core.gradedCharacter literalVOA)
      ≡ Core.monsterAction literalVOA

    -- The first-coefficient authority is also one object, not two compatible
    -- numerical statements.
    sameFirstCoefficientBridge :
      Core.firstCoefficientBridge literalVOA
      ≡ Legacy.firstCoefficientBridge gradedAuthority

open MonsterGradedVOALiteralActionWeld public

------------------------------------------------------------------------
-- 2. Literal carrier/action extracted from the weld.
------------------------------------------------------------------------

LiteralVOA :
  ∀ {Monster K} → MonsterGradedVOALiteralActionWeld Monster K →
  Core.VertexOperatorAlgebra
LiteralVOA weld = Core.voa (literalVOA weld)

LiteralState :
  ∀ {Monster K} → MonsterGradedVOALiteralActionWeld Monster K → Set
LiteralState weld =
  Core.GradedModule.Carrier
    (Core.gradedModule (LiteralVOA weld))

literalStateAction :
  ∀ {Monster K}
    (weld : MonsterGradedVOALiteralActionWeld Monster K) →
  Monster → LiteralState weld → LiteralState weld
literalStateAction weld =
  Core.VOAGroupAction.act (Core.monsterAction (literalVOA weld))

------------------------------------------------------------------------
-- 3. Character/trace observation on the SAME element type.
------------------------------------------------------------------------

legacyTraceCoefficient :
  ∀ {Monster K}
    (weld : MonsterGradedVOALiteralActionWeld Monster K) →
  Monster → Nat → K
legacyTraceCoefficient weld element grade =
  GVOA.traceCoefficient
    (Legacy.exactGradedTrace (gradedAuthority weld))
    element grade

record SameElementTraceActionObservation
  {Monster K : Set}
  (weld : MonsterGradedVOALiteralActionWeld Monster K)
  (element : Monster)
  (grade : Nat)
  (state : LiteralState weld) : Set where
  constructor sameElementTraceActionObservation
  field
    traceValue : K
    actedState : LiteralState weld
    traceValueIsLegacyCharacterProbe :
      traceValue ≡ legacyTraceCoefficient weld element grade
    actedStateIsLiteralAction :
      actedState ≡ literalStateAction weld element state

sameElementObservation :
  ∀ {Monster K}
    (weld : MonsterGradedVOALiteralActionWeld Monster K)
    (element : Monster)
    (grade : Nat)
    (state : LiteralState weld) →
  SameElementTraceActionObservation weld element grade state
sameElementObservation weld element grade state =
  sameElementTraceActionObservation
    (legacyTraceCoefficient weld element grade)
    (literalStateAction weld element state)
    refl refl

------------------------------------------------------------------------
-- 4. Grade-two specialisation used by the selected 3B lane.
------------------------------------------------------------------------

gradeTwoTrace :
  ∀ {Monster K}
    (weld : MonsterGradedVOALiteralActionWeld Monster K) →
  Monster → K
gradeTwoTrace weld element = legacyTraceCoefficient weld element 2

gradeTwoActionObservation :
  ∀ {Monster K}
    (weld : MonsterGradedVOALiteralActionWeld Monster K)
    (element : Monster)
    (state : LiteralState weld) →
  SameElementTraceActionObservation weld element 2 state
gradeTwoActionObservation weld element state =
  sameElementObservation weld element 2 state

------------------------------------------------------------------------
-- 5. Explicit scientific boundary.
------------------------------------------------------------------------

record SameObjectWeldBoundary : Set where
  constructor sameObjectWeldBoundary
  field
    characterAndLiteralActionShareElementType : Bool
    literalStateActionAvailable : Bool
    exactGradedTraceAuthorityRetained : Bool
    sameGradedRepresentationRequired : Bool
    sameInternalCharacterActionRequired : Bool
    selected3BElementRecoveredHere : Bool
    actualZetaSectorRecognitionProvedHere : Bool
    fullMonsterVOAIdentificationProvedHere : Bool
    characterValueAlonePromotesStateAction : Bool

canonicalSameObjectWeldBoundary : SameObjectWeldBoundary
canonicalSameObjectWeldBoundary =
  sameObjectWeldBoundary
    true true true true true
    false false false false
