module DASHI.Physics.Foundations.Round5CombinedSourceBoundary where

open import DASHI.Core.Prelude

import DASHI.Biology.ConsciousAccessRound4SourceAtlas as PadicSources
import DASHI.Biology.ConsciousAccessRound5ExtendedSourceAtlas as BiologyExtended
import DASHI.Biology.ConsciousAccessRound5CompletionSourceAtlas as BiologyCompletion
import DASHI.Biology.TernaryLogicRelaxationSourceAtlas as LogicRelaxationSources
import DASHI.Physics.Foundations.Round5SourceAtlas as PhysicsSources
import DASHI.Physics.Foundations.AttachedFormalismSourceAtlas as AttachedSources
import DASHI.Physics.DarkSector.DarkSectorColliderSourceAtlas as ColliderSources
import DASHI.Visualisation.AttachedVisualisationSourceAtlas as VisualisationSources
import DASHI.Visualisation.EventPadicSourceAtlas as EventPadicSources

------------------------------------------------------------------------
-- Source populations are retained as separate typed atlases because their
-- records use different declared tranche roles.  This boundary verifies every
-- attributed population without duplicating titles, authors, or DOI strings.

record Round5CombinedSourceBoundary : Set where
  constructor round5CombinedSourceBoundary
  field
    physicsSourceCountIsSeventeen :
      PhysicsSources.canonicalRound5SourceCount ≡ 17

    biologyExtendedSourceCountIsTwentyThree :
      BiologyExtended.canonicalRound5ExtendedSourceCount ≡ 23

    biologyCompletionSourceCountIsThirtyOne :
      BiologyCompletion.canonicalRound5CompletionSourceCount ≡ 31

    reusedPadicSourceCountIsEight :
      PadicSources.canonicalRound4SourceCount ≡ 8

    attachedFormalismSourceCountIsSix :
      AttachedSources.canonicalAttachedFormalismSourceCount ≡ 6

    colliderSourceCountIsSix :
      ColliderSources.canonicalDarkSectorColliderSourceCount ≡ 6

    visualisationSourceCountIsEight :
      VisualisationSources.canonicalAttachedVisualisationSourceCount ≡ 8

    eventPadicSourceCountIsTen :
      EventPadicSources.canonicalEventPadicSourceCount ≡ 10

    ternaryLogicRelaxationSourceCountIsThree :
      LogicRelaxationSources.canonicalTernaryLogicRelaxationSourceCount ≡ 3

open Round5CombinedSourceBoundary public

canonicalRound5CombinedSourceBoundary : Round5CombinedSourceBoundary
canonicalRound5CombinedSourceBoundary =
  round5CombinedSourceBoundary
    PhysicsSources.canonicalRound5SourceCountIsSeventeen
    BiologyExtended.canonicalRound5ExtendedSourceCountIsTwentyThree
    BiologyCompletion.canonicalRound5CompletionSourceCountIsThirtyOne
    PadicSources.canonicalRound4SourceCountIsEight
    AttachedSources.canonicalAttachedFormalismSourceCountIsSix
    ColliderSources.canonicalDarkSectorColliderSourceCountIsSix
    VisualisationSources.canonicalAttachedVisualisationSourceCountIsEight
    EventPadicSources.canonicalEventPadicSourceCountIsTen
    LogicRelaxationSources.canonicalTernaryLogicRelaxationSourceCountIsThree
