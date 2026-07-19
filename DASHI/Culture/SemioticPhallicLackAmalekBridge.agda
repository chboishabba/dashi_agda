module DASHI.Culture.SemioticPhallicLackAmalekBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Semiotic phallus / lack / Amalek bridge.
--
-- This module formalizes the symbolic-castration layer of the semiotic
-- deconstruction: a public sign intended to signify closure, bigness,
-- cleanliness, order, and sovereignty can return as visible lack/gash/cut.
-- The danger is not lack itself; the danger is projecting lack onto an Other
-- and routing affect through enemy-production or purification.
--
-- Candidate-only: no psychoanalytic diagnosis, no person identification, no
-- political/clinical authority, and no promotion of domination.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Sign vocabulary.

data PhallicSignSurface : Set where
  phallicClosureSurface :
    PhallicSignSurface

  lackGashSurface :
    PhallicSignSurface

  symbolicCastrationSurface :
    PhallicSignSurface

  hygieneCivilisationSurface :
    PhallicSignSurface

  enemyPollutantSurface :
    PhallicSignSurface

  survivorAsFeedbackSurface :
    PhallicSignSurface

canonicalPhallicSignSurfaces :
  List PhallicSignSurface
canonicalPhallicSignSurfaces =
  phallicClosureSurface
  ∷ lackGashSurface
  ∷ symbolicCastrationSurface
  ∷ hygieneCivilisationSurface
  ∷ enemyPollutantSurface
  ∷ survivorAsFeedbackSurface
  ∷ []

canonicalPhallicSignSurfaceCount : Nat
canonicalPhallicSignSurfaceCount =
  listCount canonicalPhallicSignSurfaces

phallicSignSurfaceName :
  PhallicSignSurface → String
phallicSignSurfaceName phallicClosureSurface =
  "phallic closure / naming / domination sign"
phallicSignSurfaceName lackGashSurface =
  "lack / gash / cut sign"
phallicSignSurfaceName symbolicCastrationSurface =
  "symbolic castration residual"
phallicSignSurfaceName hygieneCivilisationSurface =
  "clean-dirty civilisation-nature sign chain"
phallicSignSurfaceName enemyPollutantSurface =
  "enemy-pollutant Amalek risk"
phallicSignSurfaceName survivorAsFeedbackSurface =
  "survivor / harmed subject as feedback subject"

phallicSignSurfaceReading :
  PhallicSignSurface → String
phallicSignSurfaceReading phallicClosureSurface =
  "The intended sign says complete, big, clean, sovereign, named, and controlled."
phallicSignSurfaceReading lackGashSurface =
  "The returned sign says wound, opening, failure, cut, dependency, and non-closure."
phallicSignSurfaceReading symbolicCastrationSurface =
  "Symbolic castration is tracked as failed phallic gluing, not as a clinical diagnosis."
phallicSignSurfaceReading hygieneCivilisationSurface =
  "Clean/dirty and civilisation/nature are tracked as disciplinary sign chains."
phallicSignSurfaceReading enemyPollutantSurface =
  "Amalek risk activates when lack/contamination is projected onto a human group."
phallicSignSurfaceReading survivorAsFeedbackSurface =
  "A wounded institution must read survivor truth as feedback, not as a castrating attack on mission."

------------------------------------------------------------------------
-- Opposition lattice.

data SemioticOpposition : Set where
  phallusLackOpposition :
    SemioticOpposition

  blueGreenOpposition :
    SemioticOpposition

  cleanDirtyOpposition :
    SemioticOpposition

  civilisationNatureOpposition :
    SemioticOpposition

  sacredDefiledOpposition :
    SemioticOpposition

  humanPollutantOpposition :
    SemioticOpposition

canonicalSemioticOppositions :
  List SemioticOpposition
canonicalSemioticOppositions =
  phallusLackOpposition
  ∷ blueGreenOpposition
  ∷ cleanDirtyOpposition
  ∷ civilisationNatureOpposition
  ∷ sacredDefiledOpposition
  ∷ humanPollutantOpposition
  ∷ []

------------------------------------------------------------------------
-- Bridge receipt.

record SemioticPhallicLackAmalekBridge : Set where
  constructor mkSemioticPhallicLackAmalekBridge
  field
    signSurfaces :
      List PhallicSignSurface

    signSurfacesAreCanonical :
      signSurfaces ≡ canonicalPhallicSignSurfaces

    signOppositions :
      List SemioticOpposition

    signOppositionsAreCanonical :
      signOppositions ≡ canonicalSemioticOppositions

    semioticCyberneticsTracked :
      Bool

    semioticCyberneticsTrackedIsTrue :
      semioticCyberneticsTracked ≡ true

    phallicResidualTracked :
      Bool

    phallicResidualTrackedIsTrue :
      phallicResidualTracked ≡ true

    lackProjectionBlocked :
      Bool

    lackProjectionBlockedIsTrue :
      lackProjectionBlocked ≡ true

    survivorAsCastrationBlocked :
      Bool

    survivorAsCastrationBlockedIsTrue :
      survivorAsCastrationBlocked ≡ true

    humanPollutantPromotion :
      Bool

    humanPollutantPromotionIsFalse :
      humanPollutantPromotion ≡ false

    dominationPromotion :
      Bool

    dominationPromotionIsFalse :
      dominationPromotion ≡ false

    psychoanalyticDiagnosisPromoted :
      Bool

    psychoanalyticDiagnosisPromotedIsFalse :
      psychoanalyticDiagnosisPromoted ≡ false

    bridgeReading :
      String

open SemioticPhallicLackAmalekBridge public

canonicalSemioticPhallicLackAmalekBridge :
  SemioticPhallicLackAmalekBridge
canonicalSemioticPhallicLackAmalekBridge =
  mkSemioticPhallicLackAmalekBridge
    canonicalPhallicSignSurfaces
    refl
    canonicalSemioticOppositions
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    "Semiotics is treated as cybernetics of meaning: the bridge tracks phallic sign failure, lack/gash, and Amalek risk while blocking human-pollutant promotion and survivor-as-castration coding."

canonicalHumanPollutantPromotionFalse :
  humanPollutantPromotion canonicalSemioticPhallicLackAmalekBridge ≡ false
canonicalHumanPollutantPromotionFalse =
  humanPollutantPromotionIsFalse canonicalSemioticPhallicLackAmalekBridge

canonicalDominationPromotionFalse :
  dominationPromotion canonicalSemioticPhallicLackAmalekBridge ≡ false
canonicalDominationPromotionFalse =
  dominationPromotionIsFalse canonicalSemioticPhallicLackAmalekBridge

canonicalPsychoanalyticDiagnosisPromotedFalse :
  psychoanalyticDiagnosisPromoted canonicalSemioticPhallicLackAmalekBridge ≡ false
canonicalPsychoanalyticDiagnosisPromotedFalse =
  psychoanalyticDiagnosisPromotedIsFalse canonicalSemioticPhallicLackAmalekBridge

canonicalLackProjectionBlockedTrue :
  lackProjectionBlocked canonicalSemioticPhallicLackAmalekBridge ≡ true
canonicalLackProjectionBlockedTrue =
  lackProjectionBlockedIsTrue canonicalSemioticPhallicLackAmalekBridge

canonicalSurvivorAsCastrationBlockedTrue :
  survivorAsCastrationBlocked canonicalSemioticPhallicLackAmalekBridge ≡ true
canonicalSurvivorAsCastrationBlockedTrue =
  survivorAsCastrationBlockedIsTrue canonicalSemioticPhallicLackAmalekBridge
