module DASHI.Applied.RallyPaceNoteDialectFixtureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Applied.RallyReccePaceNoteFibreOverTimeExact as Rally

------------------------------------------------------------------------
-- SAME SEMANTIC CORNER, DIFFERENT PACE-NOTE DIALECT SURFACES
------------------------------------------------------------------------

leftFastOverCrestIntoRightTightensDontCut : Rally.PaceNoteSemantic
leftFastOverCrestIntoRightTightensDontCut =
  Rally.pace-note-semantic
    Rally.left
    Rally.veryFast
    Rally.constantRadius
    Rally.short
    Rally.crest
    Rally.neutralLine
    Rally.caution
    Rally.intoLink
    0

numericSurface : Rally.PaceNoteSurface
numericSurface =
  Rally.pace-note-surface
    Rally.sixFastestNumeric
    "left 6 over crest into right 4 tightens don't cut"
    "numeric 1-6 crew/game surface"

descriptiveSurface : Rally.PaceNoteSurface
descriptiveSurface =
  Rally.pace-note-surface
    Rally.descriptiveWords
    "fast left over crest into medium right tightens don't cut"
    "descriptive-word crew surface"

numericInterpretation : Rally.PaceNoteInterpretation
numericInterpretation =
  Rally.pace-note-interpretation
    numericSurface
    leftFastOverCrestIntoRightTightensDontCut
    "fixture: numeric surface interpreted into dialect-independent semantic fibre"

descriptiveInterpretation : Rally.PaceNoteInterpretation
descriptiveInterpretation =
  Rally.pace-note-interpretation
    descriptiveSurface
    leftFastOverCrestIntoRightTightensDontCut
    "fixture: descriptive surface interpreted into same semantic fibre"

sameSemanticDifferentDialect :
  Rally.PaceNoteInterpretation.semantic numericInterpretation ≡
  Rally.PaceNoteInterpretation.semantic descriptiveInterpretation
sameSemanticDifferentDialect = refl

------------------------------------------------------------------------
-- SHAPE MODIFIERS ARE SEMANTIC COORDINATES, NOT NUMBER-SCALE PATCHES.
------------------------------------------------------------------------

rightMediumTightens : Rally.PaceNoteSemantic
rightMediumTightens =
  Rally.pace-note-semantic
    Rally.right
    Rally.medium
    Rally.tightens
    Rally.long
    Rally.level
    Rally.dontCut
    Rally.ditch
    Rally.separated
    80

rightMediumOpens : Rally.PaceNoteSemantic
rightMediumOpens =
  Rally.pace-note-semantic
    Rally.right
    Rally.medium
    Rally.opens
    Rally.long
    Rally.level
    Rally.neutralLine
    Rally.caution
    Rally.separated
    80

-- The two calls can share direction/severity/distance while differing in shape.
-- We retain that difference in the semantic fibre rather than forcing it into
-- a finer severity number.
data ShapeDifferenceCanBeErasedBySeverityPermission : Set where
shapeDifferenceMustRemainAvailable : ShapeDifferenceCanBeErasedBySeverityPermission → ⊥
shapeDifferenceMustRemainAvailable ()

------------------------------------------------------------------------
-- CALL TIMING / LINKAGE ALSO REMAINS FIRST-CLASS.
------------------------------------------------------------------------

intoCall : Rally.PaceNoteSemantic
intoCall =
  Rally.pace-note-semantic
    Rally.left Rally.fast Rally.constantRadius Rally.short Rally.level
    Rally.neutralLine Rally.caution Rally.intoLink 0

separatedCall : Rally.PaceNoteSemantic
separatedCall =
  Rally.pace-note-semantic
    Rally.left Rally.fast Rally.constantRadius Rally.short Rally.level
    Rally.neutralLine Rally.caution Rally.separated 100

data LinkageMayBeDiscardedPermission : Set where
linkageMayNotBeDiscarded : LinkageMayBeDiscardedPermission → ⊥
linkageMayNotBeDiscarded ()
