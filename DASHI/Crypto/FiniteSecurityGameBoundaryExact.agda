module DASHI.Crypto.FiniteSecurityGameBoundaryExact where

------------------------------------------------------------------------
-- FINITE SECURITY-GAME BOUNDARY
--
-- Correctness, exact leakage, computational recovery, and distinguishing are
-- different propositions.  This finite binary game gives an exact bridge:
-- exact recovery of a protected Boolean label yields a perfect distinguisher.
-- Failure to construct such a witness is not promoted into a security proof.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record BinaryProtectedGame : Set₁ where
  constructor binaryProtectedGame
  field
    Hidden Observation : Set
    left right : Hidden
    observe : Hidden → Observation
    protected : Hidden → Bool
    leftLabel : protected left ≡ false
    rightLabel : protected right ≡ true

open BinaryProtectedGame public

Adversary : BinaryProtectedGame → Set
Adversary game = Observation game → Bool

record PerfectDistinguisher
    (game : BinaryProtectedGame)
    (adversary : Adversary game) : Set where
  constructor perfectDistinguisher
  field
    guessesLeft : adversary (observe game (left game)) ≡ false
    guessesRight : adversary (observe game (right game)) ≡ true

open PerfectDistinguisher public

record ExactProtectedRecovery (game : BinaryProtectedGame) : Set₁ where
  constructor exactProtectedRecovery
  field
    recover : Observation game → Bool
    exact : ∀ hidden → recover (observe game hidden) ≡ protected game hidden

open ExactProtectedRecovery public

exactRecoveryYieldsPerfectDistinguisher :
  ∀ {game : BinaryProtectedGame}
    (recovery : ExactProtectedRecovery game) →
  PerfectDistinguisher game (recover recovery)
exactRecoveryYieldsPerfectDistinguisher {game} recovery =
  perfectDistinguisher
    (trans (exact recovery (left game)) (leftLabel game))
    (trans (exact recovery (right game)) (rightLabel game))

------------------------------------------------------------------------
-- A same-observation fibre containing both labels forbids a perfect observer-
-- only distinguisher, hence forbids exact protected-label recovery.
------------------------------------------------------------------------

record ChallengeObservationCollision (game : BinaryProtectedGame) : Set where
  constructor challengeObservationCollision
  field
    sameObservation : observe game (left game) ≡ observe game (right game)

open ChallengeObservationCollision public

collisionRefutesPerfectDistinguisher :
  ∀ {game : BinaryProtectedGame}
    {adversary : Adversary game} →
  ChallengeObservationCollision game →
  PerfectDistinguisher game adversary → ⊥
collisionRefutesPerfectDistinguisher {game} collision perfect =
  falseNotTrue falseEqualsTrue
  where
  falseEqualsTrue : false ≡ true
  falseEqualsTrue =
    trans
      (sym (guessesLeft perfect))
      (trans
        (cong adversary (sameObservation collision))
        (guessesRight perfect))

  falseNotTrue : false ≡ true → ⊥
  falseNotTrue ()

collisionRefutesExactRecovery :
  ∀ {game : BinaryProtectedGame} →
  ChallengeObservationCollision game →
  ExactProtectedRecovery game → ⊥
collisionRefutesExactRecovery collision recovery =
  collisionRefutesPerfectDistinguisher collision
    (exactRecoveryYieldsPerfectDistinguisher recovery)

------------------------------------------------------------------------
-- Finite success numerator: perfect success is 2/2, random-guess baseline is
-- represented as 1/2.  We keep numerators exact and avoid pretending this is a
-- full probabilistic IND-CCA formalisation.
------------------------------------------------------------------------

successFalse : Bool → Nat
successFalse false = 1
successFalse true = 0

successTrue : Bool → Nat
successTrue false = 0
successTrue true = 1

successNumerator :
  (game : BinaryProtectedGame) → Adversary game → Nat
successNumerator game adversary =
  successFalse (adversary (observe game (left game))) +
  successTrue (adversary (observe game (right game)))

perfectSuccessNumerator :
  ∀ {game : BinaryProtectedGame}
    {adversary : Adversary game} →
  PerfectDistinguisher game adversary →
  successNumerator game adversary ≡ 2
perfectSuccessNumerator perfect
  rewrite guessesLeft perfect | guessesRight perfect = refl

randomGuessBaselineNumerator : Nat
randomGuessBaselineNumerator = 1

record GameClaimBoundary : Set where
  constructor gameClaimBoundary
  field
    exactLeakImpliesPerfectGameBreak : Bool
    exactLeakImpliesPerfectGameBreakIsTrue :
      exactLeakImpliesPerfectGameBreak ≡ true
    absenceOfKnownBreakProvesSecurity : Bool
    absenceOfKnownBreakProvesSecurityIsFalse :
      absenceOfKnownBreakProvesSecurity ≡ false

canonicalGameClaimBoundary : GameClaimBoundary
canonicalGameClaimBoundary = gameClaimBoundary true refl false refl
