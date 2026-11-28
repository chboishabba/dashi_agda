module DASHI.Mathematics.Complexity.PNPStandardStackCandidateRunExact where

-- Actual Candidate.candidateProgramBits and StandardExactRun, with the
-- numeric split-stack inverse and exact quotient/remainder transitions.
-- Raw ordered FRACTRAN compilation still has its own native priority weld.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Bool using (Bool)
open import Data.Nat.Base using (_<_)
open import Data.Nat.DivMod using
  (_/_; _%_; [m+kn]%n≡m%n; m<n⇒m%n≡m; m<n⇒m/n≡0;
   m*n/n≡m; +-distrib-/-∣ʳ)
open import Data.Nat.Divisibility using (_∣_; divides)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)
import DASHI.Mathematics.Complexity.StandardSingleTapeMachineExact as S
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeStandardRunExact as R
import DASHI.Mathematics.Complexity.PNPStandardStackNumericExact as Stack
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteTapeProgramCodeExact as Code
import DASHI.Mathematics.Complexity.StandardFiniteTapePresentationExact as Presented
import DASHI.Mathematics.Complexity.ConcreteTapeStandardLanguageEquivalenceExact as Language

pred : Nat → Nat
pred zero = zero
pred (suc n) = n

atLeastOne : Nat → Nat
atLeastOne zero = suc zero
atLeastOne (suc n) = suc n

module Numeric {State Symbol : Set}
    (machine : S.StandardSingleTapeMachine State Symbol)
    (baseMinusTwo : Nat) (digit : Symbol → Nat) (symbol : Nat → Symbol)
    (blankZero : digit (S.blank machine) ≡ zero)
    (digitBound : ∀ a → digit a < suc (suc baseMinusTwo))
    (decodeDigit : ∀ a → symbol (digit a) ≡ a) where

  base = suc (suc baseMinusTwo)
  module P = Stack.Stack machine base digit blankZero
  open P using (Packed; packed; pack; value; length)

  remainder : ∀ a xs → value (a ∷ xs) % base ≡ digit a
  remainder a xs rewrite N.*-comm base (value xs) =
    trans ([m+kn]%n≡m%n (digit a) (value xs) base)
      (m<n⇒m%n≡m (digitBound a))

  quotient : ∀ a xs → value (a ∷ xs) / base ≡ value xs
  quotient a xs rewrite N.*-comm base (value xs)
    | +-distrib-/-∣ʳ (digit a) (divides (value xs) refl)
    | m<n⇒m/n≡0 (digitBound a)
    | m*n/n≡m (value xs) base = refl

  decodeWord : Nat → Nat → List Symbol
  decodeWord zero v = []
  decodeWord (suc n) v = symbol (v % base) ∷ decodeWord n (v / base)

  decodeWordExact : ∀ xs → decodeWord (length xs) (value xs) ≡ xs
  decodeWordExact [] = refl
  decodeWordExact (a ∷ xs)
    rewrite remainder a xs | quotient a xs | decodeDigit a | decodeWordExact xs = refl

  unpack : Packed → S.StandardConfiguration machine
  unpack (packed q l r ln rn) =
    S.standard-configuration (decodeWord ln l) q (symbol (r % base))
      (decodeWord (pred rn) (r / base))

  unpackPack : ∀ c → unpack (pack c) ≡ c
  unpackPack (S.standard-configuration l q a r)
    rewrite remainder a r | quotient a r | decodeDigit a |
      decodeWordExact l | decodeWordExact r = refl

  applyPacked : Packed → S.StandardTransition State Symbol → Packed
  applyPacked (packed q l r ln rn) (S.standard-transition q' b L.moveRight) =
    packed q' (digit b + base * l) (r / base) (suc ln) (atLeastOne (pred rn))
  applyPacked (packed q l r ln rn) (S.standard-transition q' b L.moveLeft) =
    packed q' (l / base) (l % base + base * (digit b + base * (r / base)))
      (pred ln) (suc rn)
  applyPacked (packed q l r ln rn) (S.standard-transition q' b L.stayPut) =
    packed q' l (digit b + base * (r / base)) ln rn

  applyExact : ∀ c t → applyPacked (pack c) t ≡ pack (S.standardApplyTransition machine c t)
  applyExact (S.standard-configuration l q a []) (S.standard-transition q' b L.moveRight)
    rewrite quotient a [] = symRight
    where
      symRight : packed q' (digit b + base * value l) zero (suc (length l)) 1
        ≡ pack (S.standardApplyTransition machine (S.standard-configuration l q a [])
          (S.standard-transition q' b L.moveRight))
      symRight = sym (P.moveRightExact l q a [] q' b)
  applyExact (S.standard-configuration l q a (r ∷ rs)) (S.standard-transition q' b L.moveRight)
    rewrite quotient a (r ∷ rs) = refl
  applyExact (S.standard-configuration [] q a r) (S.standard-transition q' b L.moveLeft)
    rewrite quotient a r | blankZero = refl
  applyExact (S.standard-configuration (l ∷ ls) q a r) (S.standard-transition q' b L.moveLeft)
    rewrite quotient a r | remainder l ls | quotient l ls = refl
  applyExact (S.standard-configuration l q a r) (S.standard-transition q' b L.stayPut)
    rewrite quotient a r = refl

  mapPack : Maybe (S.StandardConfiguration machine) → Maybe Packed
  mapPack nothing = nothing
  mapPack (just c) = just (pack c)

  next : Packed → Maybe Packed
  next p@(packed q l r ln rn) with S.transition machine q (symbol (r % base))
  ... | nothing = nothing
  ... | just t = just (applyPacked p t)

  nextExact : ∀ c → next (pack c) ≡ mapPack (S.standardNext machine c)
  nextExact c@(S.standard-configuration l q a r)
    rewrite remainder a r | decodeDigit a
    with S.transition machine q a
  ... | nothing = refl
  ... | just t = cong just (applyExact c t)

  run : Nat → Packed → Maybe Packed
  run zero p = just p
  run (suc n) p with next p
  ... | nothing = nothing
  ... | just q = run n q

  runExact : ∀ {n start finish} → R.StandardExactRun machine n start finish →
    run n (pack start) ≡ just (pack finish)
  runExact R.standardRunDone = refl
  runExact (R.standardRunStep {current = c} edge rest)
    rewrite nextExact c | edge = runExact rest

  decodeRun : Maybe Packed → Maybe (S.StandardConfiguration machine)
  decodeRun nothing = nothing
  decodeRun (just p) = just (unpack p)

  runDecodeExact : ∀ {n start finish} → R.StandardExactRun machine n start finish →
    decodeRun (run n (pack start)) ≡ just finish
  runDecodeExact {finish = finish} execution
    rewrite runExact execution | unpackPack finish = refl

module Actual {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    (standard : Candidate.StandardFiniteCandidateCode candidate) where

  presentation = Candidate.presentation standard
  concrete = Candidate.candidateConcreteMachine standard
  machine = Presented.finitePresentedStandardMachine presentation
  sc = Candidate.candidateStateCoverage standard
  ac = Candidate.candidateSymbolCoverage standard

  programView : Code.StaticProgramView concrete
  programView = Code.decodeStaticProgramView concrete sc ac (Candidate.candidateProgramBits standard)

  programExact : programView ≡ Code.canonicalStaticProgramView concrete
  programExact = Code.decodeEncodeStaticProgramView concrete sc ac

  module RunWithDigits (baseMinusTwo : Nat)
      (digit : Presented.Symbol presentation → Nat)
      (symbol : Nat → Presented.Symbol presentation)
      (blankZero : digit (S.blank machine) ≡ zero)
      (digitBound : ∀ a → digit a < suc (suc baseMinusTwo))
      (decodeDigit : ∀ a → symbol (digit a) ≡ a) where

    module NRun = Numeric machine baseMinusTwo digit symbol blankZero digitBound decodeDigit

    start : Cook.BooleanFormula → S.StandardConfiguration machine
    start f = Language.guardedStandardStart (Candidate.encodeFormula standard f)
      (Candidate.exactSteps standard f)

    decodedEndpoint : (f : Cook.BooleanFormula) →
      NRun.decodeRun (NRun.run (Candidate.exactSteps standard f) (NRun.P.pack (start f)))
      ≡ just (Candidate.finish standard f)
    decodedEndpoint f = NRun.runDecodeExact (Candidate.execution standard f)

    endpointDecision : (f : Cook.BooleanFormula) →
      L.decideEqual (Presented.finiteState presentation)
        (S.state (Candidate.finish standard f)) (Code.acceptingControl programView)
      ≡ Direct.decide candidate f
    endpointDecision f rewrite programExact = Candidate.decisionExact standard f

-- The decoder is length-aware, including trailing blanks. The actual parsed
-- program is definitionally the original standard rule table after programExact.
-- Native finite digit enumeration, ordered fraction compiler and physical
-- same-target machine clock remain separate from this numeric run theorem.
