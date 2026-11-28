module DASHI.Mathematics.Complexity.PNPStackFiniteDigitOwnerExact where

-- Construct the digit codec from the actual advertised finite enumeration,
-- moving the witnessed blank to the front without increasing its extent.
-- No assumed injective numeral assignment is needed.
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as N
open import Relation.Binary.PropositionalEquality using (cong; sym)
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as L
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as C
import DASHI.Mathematics.Complexity.PNPStandardStackCandidateRunExact as Run
import DASHI.Mathematics.Complexity.PNotEqualsNPStandardFiniteCandidateCodeExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook

delete : ∀ {A : Set} {b : A} {xs} → C.Member b xs → List A
delete (C.here {xs}) = xs
delete (C.there {y} m) = y ∷ delete m

deleteLength : ∀ {A : Set} {b : A} {xs} (m : C.Member b xs) →
  suc (C.listLength (delete m)) ≡ C.listLength xs
deleteLength C.here = refl
deleteLength (C.there m) = cong suc (deleteLength m)

retain : ∀ {A : Set} {b x : A} {xs}
  (m : C.Member b xs) → C.Member x xs → C.Member x (b ∷ delete m)
retain C.here C.here = C.here
retain C.here (C.there k) = C.there k
retain (C.there m) C.here = C.there C.here
retain (C.there m) (C.there k) with retain m k
... | C.here = C.here
... | C.there j = C.there (C.there j)

rank : ∀ {A : Set} → L.FiniteEnumeration A → A → List A → Nat
rank e x [] = zero
rank e x (y ∷ ys) with L.decideEqual e x y
... | true = zero
... | false = suc (rank e x ys)

read : ∀ {A : Set} → A → List A → Nat → A
read b [] n = b
read b (x ∷ xs) zero = x
read b (x ∷ xs) (suc n) = read b xs n

rankBound : ∀ {A : Set} (e : L.FiniteEnumeration A) {x xs} →
  C.Member x xs → rank e x xs < C.listLength xs
rankBound e {x} (C.here {xs}) rewrite L.decideEqualRefl e x = s≤s z≤n
rankBound e {x} (C.there {y} m) with L.decideEqual e x y
... | true = s≤s z≤n
... | false = s≤s (rankBound e m)

rankRead : ∀ {A : Set} (e : L.FiniteEnumeration A) (b : A) {x xs} →
  C.Member x xs → read b xs (rank e x xs) ≡ x
rankRead e b {x} (C.here {xs}) rewrite L.decideEqualRefl e x = refl
rankRead e b {x} (C.there {y} m) with L.decideEqual e x y in eq
... | true = sym (L.decideEqualSound e {x} {y} eq)
... | false = rankRead e b m

padBase : ∀ n → n ≤ suc (suc (Run.pred (Run.pred n)))
padBase zero = z≤n
padBase (suc zero) = s≤s z≤n
padBase (suc (suc n)) = N.≤-refl

module Digits {A : Set} (e : L.FiniteEnumeration A)
  (coverage : C.EnumerationCoverage e) (blank : A) where

  m = C.listed coverage blank
  alphabet : List A
  alphabet = blank ∷ delete m

  alphabetLength : C.listLength alphabet ≡ C.listLength (L.values e)
  alphabetLength = deleteLength m

  baseMinusTwo : Nat
  baseMinusTwo = Run.pred (Run.pred (C.listLength alphabet))

  digit : A → Nat
  digit x = rank e x alphabet

  symbol : Nat → A
  symbol = read blank alphabet

  blankZero : digit blank ≡ zero
  blankZero rewrite L.decideEqualRefl e blank = refl

  digitBound : ∀ x → digit x < suc (suc baseMinusTwo)
  digitBound x = N.≤-trans (rankBound e (retain m (C.listed coverage x)))
    (padBase (C.listLength alphabet))

  decodeDigit : ∀ x → symbol (digit x) ≡ x
  decodeDigit x = rankRead e blank (retain m (C.listed coverage x))

module Actual {cost : PR.PolynomialCostModel Cook.BooleanFormula}
  {candidate : Direct.PolynomialSATDeciderCandidate cost}
  (standard : Candidate.StandardFiniteCandidateCode candidate) where

  concrete = Candidate.candidateConcreteMachine standard
  module D = Digits (L.finiteSymbol concrete) (Candidate.candidateSymbolCoverage standard)
    (L.blank concrete)
  module ActualRun = Run.Actual standard
  module Decoded = ActualRun.RunWithDigits D.baseMinusTwo D.digit D.symbol
    D.blankZero D.digitBound D.decodeDigit

  -- Decoded.decodedEndpoint and Decoded.endpointDecision now require
  -- only the actual original candidate, not a supplied digit witness.
  -- The numeric macro model is not yet the native raw fraction interpreter.
