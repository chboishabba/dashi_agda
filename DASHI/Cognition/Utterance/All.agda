module DASHI.Cognition.Utterance.All where

open import DASHI.Cognition.Utterance.LayeredMeaningCore public
open import DASHI.Cognition.Utterance.AdmissibilityGate public
open import DASHI.Cognition.Utterance.YeGrievanceInvariantExample public

-- The PNF/IR semantic-learning tranche is intentionally checked through the
-- established utterance aggregate: EventPNF depends only on LayeredMeaningCore,
-- so this import is acyclic and forces the existing focused Agda CI to validate
-- candidate/resolution algebra, operational IR, memory, learning, braid,
-- multilingual, NASHI, completion, measurement, and Calabi-Yau boundaries.
import DASHI.Cognition.PNF.PNFIRLearningEverything
