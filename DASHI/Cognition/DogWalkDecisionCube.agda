module DASHI.Cognition.DogWalkDecisionCube where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Core.TernaryDecisionCube using (Cube3; cube3; allCube3; length)

------------------------------------------------------------------------
-- The three axes isolated in the conversation.
--
-- Each axis has a negative pole, a neutral/coupled state, and a positive
-- pole.  The axis labels are semantic; the common carrier remains Trit.

-- Physical control / causal force:
--   pos = human controls movement
--   zer = coupled or mutual movement
--   neg = dog controls movement
physicalControl : Trit → Trit
physicalControl t = t

-- Intent / initiation:
--   pos = human initiates or plans
--   zer = no unique initiator
--   neg = dog initiates or plans
intentControl : Trit → Trit
intentControl t = t

-- Conventional semantic role:
--   pos = human walks dog
--   zer = joint or unresolved framing
--   neg = dog walks human
roleControl : Trit → Trit
roleControl t = t

record DogWalkState : Set where
  constructor dogWalk
  field
    physical : Trit
    intent : Trit
    role : Trit

open DogWalkState public

asCube : DogWalkState → Cube3
asCube (dogWalk p i r) = cube3 p i r

------------------------------------------------------------------------
-- Complete 3 × 3 × 3 enumeration.
-- Ordering is grouped by semantic role, then physical control, then intent.

allDogWalkStates : List DogWalkState
allDogWalkStates =
  -- role = pos: conventional "human walks dog"
  dogWalk pos pos pos ∷ dogWalk pos zer pos ∷ dogWalk pos neg pos ∷
  dogWalk zer pos pos ∷ dogWalk zer zer pos ∷ dogWalk zer neg pos ∷
  dogWalk neg pos pos ∷ dogWalk neg zer pos ∷ dogWalk neg neg pos ∷

  -- role = zer: joint, neutral, or unresolved framing
  dogWalk pos pos zer ∷ dogWalk pos zer zer ∷ dogWalk pos neg zer ∷
  dogWalk zer pos zer ∷ dogWalk zer zer zer ∷ dogWalk zer neg zer ∷
  dogWalk neg pos zer ∷ dogWalk neg zer zer ∷ dogWalk neg neg zer ∷

  -- role = neg: inverted "dog walks human"
  dogWalk pos pos neg ∷ dogWalk pos zer neg ∷ dogWalk pos neg neg ∷
  dogWalk zer pos neg ∷ dogWalk zer zer neg ∷ dogWalk zer neg neg ∷
  dogWalk neg pos neg ∷ dogWalk neg zer neg ∷ dogWalk neg neg neg ∷ []

allDogWalkStates-has-27-states :
  length allDogWalkStates ≡
  suc (suc (suc (suc (suc (suc (suc (suc (suc
  (suc (suc (suc (suc (suc (suc (suc (suc (suc
  (suc (suc (suc (suc (suc (suc (suc (suc (suc zero)))))))))))))))))))))))))))
allDogWalkStates-has-27-states = refl

------------------------------------------------------------------------
-- Named points discussed in the thread.

canonicalHumanWalksDog : DogWalkState
canonicalHumanWalksDog = dogWalk pos pos pos

coupledWalk : DogWalkState
coupledWalk = dogWalk zer zer zer

classicDogWalksHuman : DogWalkState
classicDogWalksHuman = dogWalk neg zer neg

maximalRoleInversion : DogWalkState
maximalRoleInversion = dogWalk neg neg neg

skateboardPull : DogWalkState
skateboardPull = dogWalk neg pos neg

------------------------------------------------------------------------
-- Humor is not identified with a single state.  It is a mismatch surface:
-- the asserted semantic role can invert while physical and intentional
-- axes remain conventional, coupled, or only partially inverted.

data RoleMismatch : DogWalkState → Set where
  ironicHumanControl : RoleMismatch (dogWalk pos pos neg)
  creditedDogInitiation : RoleMismatch (dogWalk pos neg neg)
  coupledInversion : RoleMismatch (dogWalk zer zer neg)
  physicallyJustifiedInversion : RoleMismatch (dogWalk neg zer neg)

-- The joke phrase quotients several distinct latent states to one wording.
data WalkPhrase : Set where
  humanWalksDog dogWalksHuman walksTogether : WalkPhrase

phrase : DogWalkState → WalkPhrase
phrase (dogWalk _ _ pos) = humanWalksDog
phrase (dogWalk _ _ zer) = walksTogether
phrase (dogWalk _ _ neg) = dogWalksHuman

same-inverted-phrase-different-latent-state :
  phrase (dogWalk pos pos neg) ≡ phrase (dogWalk neg neg neg)
same-inverted-phrase-different-latent-state = refl
