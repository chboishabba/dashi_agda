module DASHI.Foundations.TernaryThirteenOriginalHeisenbergResidualActionExact where

------------------------------------------------------------------------
-- H1.01 HIGH-ALPHA POSITIVE ACTION LEAF.
--
-- The ACTUAL original finite Heisenberg multiplication acts by
-- left translation on the original 13-coordinate word, while
-- the normalized 131-coordinate original-relation residual is
-- retained literally. This is a source-grounded, nontrivial
-- action on the existing exact 13+131 normal-form carrier.
--
-- The action is deliberately NOT presented as a selected
-- participant appraisal update, an ITIR world action, or a
-- quantum unitary. Those require independent source evidence.
--
-- All action laws below are ordinary propositional equalities
-- of the product carrier's 13-word coordinate with literally
-- unchanged residual; no function extensionality is used.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.TernaryThirteenOriginalHeisenbergGroupCarrierExact as Bridge
import DASHI.Foundations.TernaryThirteenOriginalHeisenbergTransportedGroupLawsExact as Laws
import DASHI.Foundations.TernaryThirteenOriginalRelationResidualReopeningExact as Residual
import DASHI.Foundations.TernaryThirteenOriginalRelational144NonIdentificationExact as Boundary
import DASHI.Foundations.TernaryThirteenFibreSplitExact as Word
import DASHI.Foundations.StageTwelveGrothendieckRelationHyperformExact as Original
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Moonshine.Monster3BFiniteHeisenbergInverseExact as Inverse
import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as G
import DASHI.Algebra.Trit as F3

OriginalFullRelationCoordinates : Set
OriginalFullRelationCoordinates =
  Word.TritWord 13 × Residual.Residual131

-- The ORIGINAL word operation already contains the finite H_6
-- two-cocycle. This lift adds no new twist and never discards
-- the original independently addressable 131 relation cells.
wordActsOnFullCoordinates :
  Word.TritWord 13 →
  OriginalFullRelationCoordinates →
  OriginalFullRelationCoordinates
wordActsOnFullCoordinates g (code , rest) =
  Bridge.wordCompose g code , rest

groupActsOnFullCoordinates :
  H.Heisenberg6 →
  OriginalFullRelationCoordinates →
  OriginalFullRelationCoordinates
groupActsOnFullCoordinates g =
  wordActsOnFullCoordinates (Bridge.originalGroupToWord g)

wordActionIdentity :
  (state : OriginalFullRelationCoordinates) →
  wordActsOnFullCoordinates Bridge.wordIdentity state ≡ state
wordActionIdentity (code , rest) =
  cong (λ value → value , rest) (Laws.wordLeftIdentity code)

wordActionComposition :
  (g h : Word.TritWord 13)
  (state : OriginalFullRelationCoordinates) →
  wordActsOnFullCoordinates (Bridge.wordCompose g h) state
  ≡ wordActsOnFullCoordinates g
      (wordActsOnFullCoordinates h state)
wordActionComposition g h (code , rest) =
  cong (λ value → value , rest)
    (sym (Laws.wordAssoc g h code))

wordActionInverseLeft :
  (g : Word.TritWord 13)
  (state : OriginalFullRelationCoordinates) →
  wordActsOnFullCoordinates (Bridge.wordInverse g)
    (wordActsOnFullCoordinates g state)
  ≡ state
wordActionInverseLeft g (code , rest) =
  trans
    (sym (wordActionComposition (Bridge.wordInverse g) g
      (code , rest)))
    (trans
      (cong (λ value → wordActsOnFullCoordinates value (code , rest))
        (Laws.wordLeftInverse g))
      (wordActionIdentity (code , rest)))

wordActionInverseRight :
  (g : Word.TritWord 13)
  (state : OriginalFullRelationCoordinates) →
  wordActsOnFullCoordinates g
    (wordActsOnFullCoordinates (Bridge.wordInverse g) state)
  ≡ state
wordActionInverseRight g (code , rest) =
  trans
    (sym (wordActionComposition g (Bridge.wordInverse g)
      (code , rest)))
    (trans
      (cong (λ value → wordActsOnFullCoordinates value (code , rest))
        (Laws.wordRightInverse g))
      (wordActionIdentity (code , rest)))

originalGroupActionIdentity :
  (state : OriginalFullRelationCoordinates) →
  groupActsOnFullCoordinates H.identityH state ≡ state
originalGroupActionIdentity state =
  wordActionIdentity state

originalGroupActionComposition :
  (g h : H.Heisenberg6)
  (state : OriginalFullRelationCoordinates) →
  groupActsOnFullCoordinates (H.compose g h) state
  ≡ groupActsOnFullCoordinates g
      (groupActsOnFullCoordinates h state)
originalGroupActionComposition g h state =
  trans
    (cong
      (λ code → wordActsOnFullCoordinates code state)
      (sym (Bridge.originalMultiplicationRespected g h)))
    (wordActionComposition
      (Bridge.originalGroupToWord g)
      (Bridge.originalGroupToWord h)
      state)

originalGroupActionInverse :
  (g : H.Heisenberg6)
  (state : OriginalFullRelationCoordinates) →
  groupActsOnFullCoordinates (Inverse.inverseH g)
    (groupActsOnFullCoordinates g state)
  ≡ state
originalGroupActionInverse g state =
  trans
    (cong
      (λ code →
        wordActsOnFullCoordinates code
          (groupActsOnFullCoordinates g state))
      (sym (Bridge.originalInverseRespected g)))
    (wordActionInverseLeft (Bridge.originalGroupToWord g) state)

-- Exact projection/reopening laws on the original 144-cell
-- relation source. The 13-code is transformed; residual
-- values (and thus all omitted original ordered cells)
-- remain unchanged, rather than being overwritten.
originalActionCoarseProjection :
  (g : H.Heisenberg6)
  (state : OriginalFullRelationCoordinates) →
  proj₁ (groupActsOnFullCoordinates g state)
  ≡ Bridge.wordCompose (Bridge.originalGroupToWord g) (proj₁ state)
originalActionCoarseProjection g (code , rest) = refl

originalActionResidualFixed :
  (g : H.Heisenberg6)
  (state : OriginalFullRelationCoordinates) →
  proj₂ (groupActsOnFullCoordinates g state) ≡ proj₂ state
originalActionResidualFixed g (code , rest) = refl

actOnOriginalRelation :
  H.Heisenberg6 →
  Original.StageRelationField →
  Original.StageRelationField
actOnOriginalRelation g field =
  Residual.reopenNormalized
    (proj₁ (groupActsOnFullCoordinates g
      (Residual.fullRelationalObserver field)))
    (proj₂ (groupActsOnFullCoordinates g
      (Residual.fullRelationalObserver field)))

actOriginalRelationCoarse :
  (g : H.Heisenberg6)
  (field : Original.StageRelationField) →
  Boundary.relationToThirteen (actOnOriginalRelation g field)
  ≡ Bridge.wordCompose
      (Bridge.originalGroupToWord g)
      (Boundary.relationToThirteen field)
actOriginalRelationCoarse g field =
  Residual.reopenNormalizedCoarseRecovers
    (Bridge.wordCompose
      (Bridge.originalGroupToWord g)
      (Boundary.relationToThirteen field))
    (Residual.maskToResidual131 field)

actOriginalRelationResidualAt :
  (g : H.Heisenberg6)
  (field : Original.StageRelationField)
  (cell : Original.StageRelation144) →
  Residual.maskUnobserved (actOnOriginalRelation g field) cell
  ≡ Residual.maskUnobserved field cell
actOriginalRelationResidualAt g field cell =
  Residual.reopenNormalizedResidualRecoversAt
    (Bridge.wordCompose
      (Bridge.originalGroupToWord g)
      (Boundary.relationToThirteen field))
    (Residual.maskToResidual131 field)
    cell

record OriginalFullResidualHeisenbergAction : Set₁ where
  constructor original-full-residual-heisenberg-action
  field
    unit :
      (state : OriginalFullRelationCoordinates) →
      groupActsOnFullCoordinates H.identityH state ≡ state
    composite :
      (g h : H.Heisenberg6)
      (state : OriginalFullRelationCoordinates) →
      groupActsOnFullCoordinates (H.compose g h) state
      ≡ groupActsOnFullCoordinates g
          (groupActsOnFullCoordinates h state)
    inverse :
      (g : H.Heisenberg6)
      (state : OriginalFullRelationCoordinates) →
      groupActsOnFullCoordinates (Inverse.inverseH g)
        (groupActsOnFullCoordinates g state)
      ≡ state
    residualInvariant :
      (g : H.Heisenberg6)
      (state : OriginalFullRelationCoordinates) →
      proj₂ (groupActsOnFullCoordinates g state) ≡ proj₂ state

originalFullResidualHeisenbergAction :
  OriginalFullResidualHeisenbergAction
originalFullResidualHeisenbergAction =
  original-full-residual-heisenberg-action
    originalGroupActionIdentity
    originalGroupActionComposition
    originalGroupActionInverse
    originalActionResidualFixed

------------------------------------------------------------------------
-- NONVACUITY: the original source translation generator is NOT the
-- identity, and it genuinely moves the 13-coordinate component.
-- The unchanged residual therefore does not trivialize the action.
------------------------------------------------------------------------

sourceTranslationNotIdentity :
  Bridge.sourceTranslation ≡ H.identityH → ⊥
sourceTranslationNotIdentity equality =
  positiveNotZero
    (cong (λ group →
      G.x0 (H.translationPart (H.quotient group))) equality)
  where
    positiveNotZero : F3.pos ≡ F3.zer → ⊥
    positiveNotZero ()

originalWordTranslationMovesIdentity :
  Bridge.wordCompose
    (Bridge.originalGroupToWord Bridge.sourceTranslation)
    Bridge.wordIdentity
  ≡ Bridge.wordIdentity → ⊥
originalWordTranslationMovesIdentity equal =
  sourceTranslationNotIdentity
    (trans
      (sym (Bridge.originalGroupRoundTrip Bridge.sourceTranslation))
      (trans
        (cong Bridge.wordToOriginalGroup
          (trans
            (Laws.wordRightIdentity
              (Bridge.originalGroupToWord Bridge.sourceTranslation))
            equal))
        Bridge.originalIdentityRespected))

originalFullResidualActionIsNontrivial :
  (rest : Residual.Residual131) →
  groupActsOnFullCoordinates Bridge.sourceTranslation
    (Bridge.wordIdentity , rest)
  ≡ (Bridge.wordIdentity , rest) → ⊥
originalFullResidualActionIsNontrivial rest equal =
  originalWordTranslationMovesIdentity (cong proj₁ equal)
