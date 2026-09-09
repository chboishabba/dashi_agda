module DASHI.ComputerScience.GodelArithmeticBase12NatRetractionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Maybe using (just; nothing)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat.Base using (_<_; _≤_; NonZero; nonZero; z≤n; s≤s)
open import Data.Nat.DivMod using (_/_; _%_; m/n<m)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded-fast)

import DASHI.ComputerScience.GodelArithmeticPrefixStreamCodecExact as Stream
import DASHI.ComputerScience.GodelArithmeticBase12StreamStepExact as Step

------------------------------------------------------------------------
-- TOTAL NAT -> TOKEN-STREAM DECODER
--
-- The arithmetic step is already exact:
--   encoded head = code % 12
--   encoded tail = code / 12.
--
-- Here we close totality by well-founded recursion on the Nat code.  For every
-- positive n, n / 12 < n because 12 >= 2.  This is the same accessibility
-- recursion pattern already used elsewhere in DASHI for strict Nat descent.
------------------------------------------------------------------------

baseAtLeastTwo : 2 ≤ Step.base
baseAtLeastTwo = s≤s (s≤s z≤n)

quotientSmaller :
  (n : Nat) →
  {{_ : NonZero n}} →
  n / Step.base < n
quotientSmaller n = m/n<m n Step.base baseAtLeastTwo

decodeTokenStreamAcc :
  (n : Nat) →
  Acc _<_ n →
  List Stream.SyntaxToken
decodeTokenStreamAcc zero _ = []
decodeTokenStreamAcc n@(suc _) (acc smaller)
  with Step.digitToken (n % Step.base)
... | nothing = []
... | just token =
  token ∷
  decodeTokenStreamAcc
    (n / Step.base)
    (smaller (quotientSmaller n))

decodeTokenStream : Nat → List Stream.SyntaxToken
decodeTokenStream n = decodeTokenStreamAcc n (<-wellFounded-fast n)

------------------------------------------------------------------------
-- Exact left inverse on every encoded token stream.
--
-- The theorem quantifies over ANY accessibility witness.  Therefore the proof
-- does not rely on proof identity between the externally supplied witness and
-- the recursively manufactured witness for the quotient.
------------------------------------------------------------------------

decodeEncodeTokenStreamAcc :
  (tokens : List Stream.SyntaxToken) →
  (access : Acc _<_ (Step.encodeTokenStream tokens)) →
  decodeTokenStreamAcc (Step.encodeTokenStream tokens) access ≡ tokens
decodeEncodeTokenStreamAcc [] access = refl

decodeEncodeTokenStreamAcc (Stream.natZeroToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.natZeroToken rest
        | Step.encodedTailQuotient Stream.natZeroToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.natZeroToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.natSuccToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.natSuccToken rest
        | Step.encodedTailQuotient Stream.natSuccToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.natSuccToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.termVariableToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.termVariableToken rest
        | Step.encodedTailQuotient Stream.termVariableToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.termVariableToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.termZeroToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.termZeroToken rest
        | Step.encodedTailQuotient Stream.termZeroToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.termZeroToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.termSuccessorToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.termSuccessorToken rest
        | Step.encodedTailQuotient Stream.termSuccessorToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.termSuccessorToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.termAddToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.termAddToken rest
        | Step.encodedTailQuotient Stream.termAddToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.termAddToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.termMultiplyToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.termMultiplyToken rest
        | Step.encodedTailQuotient Stream.termMultiplyToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.termMultiplyToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.formulaEqualToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.formulaEqualToken rest
        | Step.encodedTailQuotient Stream.formulaEqualToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.formulaEqualToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.formulaFalseToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.formulaFalseToken rest
        | Step.encodedTailQuotient Stream.formulaFalseToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.formulaFalseToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.formulaImplyToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.formulaImplyToken rest
        | Step.encodedTailQuotient Stream.formulaImplyToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.formulaImplyToken ∷ rest))))
  = refl

decodeEncodeTokenStreamAcc (Stream.formulaForallToken ∷ rest) (acc smaller)
  rewrite Step.encodedHeadRemainder Stream.formulaForallToken rest
        | Step.encodedTailQuotient Stream.formulaForallToken rest
        | decodeEncodeTokenStreamAcc rest
            (smaller (quotientSmaller
              (Step.encodeTokenStream (Stream.formulaForallToken ∷ rest))))
  = refl

decodeEncodeTokenStream :
  (tokens : List Stream.SyntaxToken) →
  decodeTokenStream (Step.encodeTokenStream tokens) ≡ tokens
decodeEncodeTokenStream tokens =
  decodeEncodeTokenStreamAcc
    tokens
    (<-wellFounded-fast (Step.encodeTokenStream tokens))

------------------------------------------------------------------------
-- Formula -> Nat -> formula retraction.
------------------------------------------------------------------------

encodeFormulaNat : Stream.Syntax.ArithmeticFormula → Nat
encodeFormulaNat formula =
  Step.encodeTokenStream (Stream.encodeFormula formula)

decodeFormulaNat : Nat → Stream.Syntax.ArithmeticFormula
decodeFormulaNat n =
  Stream.decodeFormula (decodeTokenStream n)

decodeEncodeFormulaNat :
  (formula : Stream.Syntax.ArithmeticFormula) →
  decodeFormulaNat (encodeFormulaNat formula) ≡ formula
decodeEncodeFormulaNat formula
  rewrite decodeEncodeTokenStream (Stream.encodeFormula formula)
        | Stream.decodeEncodeFormula formula
  = refl

------------------------------------------------------------------------
-- Boundary: a concrete syntax/Nat retraction still does not by itself provide
-- internal arithmetic representability of code substitution.
------------------------------------------------------------------------

data FormulaNatRetractionImpliesRepresentability : Set where

data FormulaNatRetractionImpliesGodelFirst : Set where

natRetractionDoesNotSupplyRepresentability :
  FormulaNatRetractionImpliesRepresentability → ⊥
natRetractionDoesNotSupplyRepresentability ()

natRetractionDoesNotSupplyGodelFirst :
  FormulaNatRetractionImpliesGodelFirst → ⊥
natRetractionDoesNotSupplyGodelFirst ()

record GodelArithmeticBase12NatRetractionBoundary : Set where
  constructor godelArithmeticBase12NatRetractionBoundary
  field
    wellFoundedNatDecoderOwned : Bool
    tokenStreamNatLeftInverseOwned : Bool
    formulaNatLeftInverseOwned : Bool
    internalSelfSubstitutionRepresentabilityOwned : Bool
    diagonalLemmaOwnedForConcreteArithmetic : Bool

canonicalGodelArithmeticBase12NatRetractionBoundary :
  GodelArithmeticBase12NatRetractionBoundary
canonicalGodelArithmeticBase12NatRetractionBoundary =
  godelArithmeticBase12NatRetractionBoundary
    true true true false false
