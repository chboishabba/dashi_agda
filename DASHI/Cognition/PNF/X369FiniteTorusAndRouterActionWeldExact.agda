module DASHI.Cognition.PNF.X369FiniteTorusAndRouterActionWeldExact where

-- X369 P1: reuse the ORIGINAL finite 3x3 torus Fourier carrier and
-- verify the directed-channel C3 algebra on its exact polynomial
-- signature. These are mathematical source-function contracts, not
-- claims about trained floating-point parameters, a semantic task or
-- physical NS/YM gauge dynamics.
--
-- Original owners: FiniteThreeCycleTorusExact,
-- BalancedTernaryFourierModeExact, and the Leech Python
-- models/trialectic_wave_prior.py directed_trialectic_invariants.
-- The finite character action and signed neural history require
-- their own source-bound transport for the latter claim.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat using (ℕ; _+_; _*_)
open import Data.Nat.Properties using (+-assoc; +-comm)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Common.FiniteThreeCycleTorusExact as Torus
import DASHI.Biology.BalancedTernaryFourierModeExact as Fourier

-- Existing original C3^2 finite torus: pair of symbolic eigencharacters.
CharacterPair : Set
CharacterPair = Fourier.C3Phase × Fourier.C3Phase

sameTorusCharacterPair :
  Torus.Torus3x3 → Torus.Torus3x3 → CharacterPair
sameTorusCharacterPair mode point =
  Fourier.firstCharacter mode point ,
  Fourier.secondCharacter mode point

-- Two independently commuting generators act on the SAME mode and
-- point, rather than on an invented nine-element group.
sameTorusFirstCharacterEigen :
  ∀ mode point →
  sameTorusCharacterPair mode (Torus.translateFirst point)
  ≡ (Fourier.multiplyPhase
       (Fourier.firstCharacter mode point)
       (Fourier.firstEigenphase mode) ,
      Fourier.secondCharacter mode point)
sameTorusFirstCharacterEigen mode point
  rewrite Fourier.firstTranslationEigen mode point
        | Fourier.secondCharacterIgnoresFirstTranslation mode point = refl

sameTorusSecondCharacterEigen :
  ∀ mode point →
  sameTorusCharacterPair mode (Torus.translateSecond point)
  ≡ (Fourier.firstCharacter mode point ,
      Fourier.multiplyPhase
        (Fourier.secondCharacter mode point)
        (Fourier.secondEigenphase mode))
sameTorusSecondCharacterEigen mode point
  rewrite Fourier.firstCharacterIgnoresSecondTranslation mode point
        | Fourier.secondTranslationEigen mode point = refl

sameTorusFirstActionOrderThree :
  ∀ point →
  Torus.translateFirst
    (Torus.translateFirst (Torus.translateFirst point)) ≡ point
sameTorusFirstActionOrderThree = Torus.translateFirstCubed

sameTorusSecondActionOrderThree :
  ∀ point →
  Torus.translateSecond
    (Torus.translateSecond (Torus.translateSecond point)) ≡ point
sameTorusSecondActionOrderThree = Torus.translateSecondCubed

sameTorusActionsCommute :
  ∀ point →
  Torus.translateFirst (Torus.translateSecond point)
  ≡ Torus.translateSecond (Torus.translateFirst point)
sameTorusActionsCommute = Torus.translationsCommute

-- Finite polynomial model of the SOURCE directed trialectic channels.
-- ℕ is chosen only for a small self-contained semiring witness; an
-- additional ℤ/ℚ/real carrier map is needed for signed Leech activations.
record Triple : Set where
  constructor triple
  field
    a b c : ℕ

rotateTriple : Triple → Triple
rotateTriple (triple a b c) = triple b c a

record Directed : Set where
  constructor directed
  field
    self cyclic anticyclic : ℕ

sum3 : ℕ → ℕ → ℕ → ℕ
sum3 a b c = (a + b) + c

directedChannels : Triple → Triple → Directed
directedChannels (triple a b c) (triple A B C) =
  directed (sum3 (a * A) (b * B) (c * C))
           (sum3 (a * B) (b * C) (c * A))
           (sum3 (a * C) (b * A) (c * B))

rotateSum3 : ∀ a b c → sum3 b c a ≡ sum3 a b c
rotateSum3 a b c =
  trans (+-comm (b + c) a) (sym (+-assoc a b c))

directedChannelsSimultaneousC3Invariant :
  ∀ x h → directedChannels (rotateTriple x) (rotateTriple h)
           ≡ directedChannels x h
directedChannelsSimultaneousC3Invariant
    (triple a b c) (triple A B C)
  rewrite rotateSum3 (a * A) (b * B) (c * C)
        | rotateSum3 (a * B) (b * C) (c * A)
        | rotateSum3 (a * C) (b * A) (c * B) = refl

-- Exact one-sided counterexample: same total amplitude, changed directed
-- face channel. Diagonal C3 is a NEGATIVE control, not a destructive
-- relative-phase intervention.
relativePhaseOriginalChannels :
  directedChannels (triple 1 0 0) (triple 1 0 0)
  ≡ directed 1 0 0
relativePhaseOriginalChannels = refl

relativePhaseShiftedChannels :
  directedChannels (rotateTriple (triple 1 0 0)) (triple 1 0 0)
  ≡ directed 0 1 0
relativePhaseShiftedChannels = refl

-- This finite witness is not a theorem about the full neural source.
-- F2/F3 and F6 require selected checkpoint, actual routing/logit
-- consumer, signed-real carrier, trained phase and a causal CE receipt.
