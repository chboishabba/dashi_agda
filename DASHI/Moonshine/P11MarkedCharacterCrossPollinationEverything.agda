module DASHI.Moonshine.P11MarkedCharacterCrossPollinationEverything where

------------------------------------------------------------------------
-- Focused aggregate for the PR #572 -> #567 character-observation weld.
--
-- Existing source-native arithmetic remains authoritative in
-- P11AristotleHeckeCrossPollinationEverything.  This layer adds only:
--
-- * the exact existing-Phase3 C3 character carrier from PR #572;
-- * restriction of the actual p=11 deck S3 representation to C3;
-- * strict separation of the Brandt-vs-standard (T3,T5,F) collision;
-- * reflection parity completing the S3-type observer;
-- * p=37 non-Ogg regular-S3 / C3-character multiplicity prediction;
-- * the observation-refinement no-decoder theorem.
--
-- No C9 or F9 carrier is identified with a marked supersingular carrier.
------------------------------------------------------------------------

import DASHI.Moonshine.P11AristotleHeckeCrossPollinationEverything
import DASHI.Foundations.Phase3RootCharacterWeldExact
import DASHI.Moonshine.P11MarkedX2DeckCharacterSeparationExact
import DASHI.Moonshine.P11MarkedObservationRefinementExact
import DASHI.Moonshine.P37NonOggFullLevel2DeckCharacterControlExact
import DASHI.Moonshine.P11MarkedDeckCharacterHighestAlphaRegression
