module DASHI.Analysis.CollatzSyracuseSharpBarrierPrimitiveASTExact where

------------------------------------------------------------------------
-- EXACT TYPED AST FOR THE SHARP-BARRIER CONTINUATION PROGRAMME
--
-- Syntax and theorem evidence are intentionally separated.
--
-- `PrimitiveAST m n` is only a typed continuation program: starting with a
-- parity word of length m it produces one of length n.  Syntax itself proves
-- neither that the produced word is an ACTUAL Syracuse prefix nor that it is
-- contracting nor that its sharp barrier falls.
--
-- Those facts are carried explicitly by proof records below.  This prevents
-- local laws for `0`, `10`, or conditionally-safe `1` from being silently
-- promoted into the universal Collatz producer.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Nat using (_<_; _≤_)
open import Data.Product using (Σ; _,_)

import DASHI.Core.BinaryBranchOutcomeEnumerationExact as Binary
import DASHI.NumberTheory.Collatz.SyracuseExact as Syracuse
import DASHI.NumberTheory.Collatz.SyracuseParityItineraryExact as Itinerary
import DASHI.NumberTheory.Collatz.SyracuseAffineIterateExact as Affine
import DASHI.Analysis.CollatzSyracuseParadoxicalPrefixExact as Paradox
import DASHI.Analysis.CollatzSyracuseSharpBarrierThresholdExact as Sharp
import DASHI.Analysis.CollatzSyracuseAffinePrefixTransitionExact as Prefix
import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as Zero
import DASHI.Analysis.CollatzSyracuseSharpBarrierOneZeroTransitionExact as OneZero
import DASHI.Analysis.CollatzSyracuseInfiniteSurvivorAffineObstructionExact as Survivor

------------------------------------------------------------------------
-- Primitive syntax.
------------------------------------------------------------------------

data PrimitiveStep : Nat → Nat → Set where
  late0  : {m : Nat} → PrimitiveStep m (suc m)
  late1  : {m : Nat} → PrimitiveStep m (suc m)
  late10 : {m : Nat} → PrimitiveStep m (suc (suc m))

data PrimitiveAST : Nat → Nat → Set where
  done : {m : Nat} → PrimitiveAST m m
  _▷_ :
    {m n k : Nat} →
    PrimitiveStep m n →
    PrimitiveAST n k →
    PrimitiveAST m k

infixr 5 _▷_

applyStep :
  {m n : Nat} →
  PrimitiveStep m n →
  Binary.BinaryWord m →
  Binary.BinaryWord n
applyStep late0 word = Zero.appendZero word
applyStep late1 word = Prefix.appendOne word
applyStep late10 word = OneZero.appendOneZero word

applyAST :
  {m n : Nat} →
  PrimitiveAST m n →
  Binary.BinaryWord m →
  Binary.BinaryWord n
applyAST done word = word
applyAST (step ▷ rest) word = applyAST rest (applyStep step word)

------------------------------------------------------------------------
-- Paid-vs-open syntax classification.
--
-- `late0` and `late10` have unconditional contracting-prefix continuation
-- theorems once the input word is already contracting.  `late1` does not:
-- it requires the exact safe-gap side condition 3^s < 2g.
------------------------------------------------------------------------

data UnconditionallyBarrierSafeStep :
    {m n : Nat} → PrimitiveStep m n → Set where
  safeLate0 : {m : Nat} → UnconditionallyBarrierSafeStep (late0 {m})
  safeLate10 : {m : Nat} → UnconditionallyBarrierSafeStep (late10 {m})

------------------------------------------------------------------------
-- Exact proof-carrying transition state.
------------------------------------------------------------------------

record ContractingState {m : Nat} (word : Binary.BinaryWord m) : Set where
  constructor contractingState
  field
    coefficient : Paradox.ContractingCoefficientGap word

open ContractingState public

sharpBarrier :
  {m : Nat} →
  (word : Binary.BinaryWord m) →
  ContractingState word →
  Nat
sharpBarrier word state =
  Sharp.quotientByPositive
    (Affine.affineAdditiveTerm word)
    (Paradox.gap (coefficient state))
    (Paradox.gapPositive (coefficient state))

record CertifiedStep
    {m n : Nat}
    (step : PrimitiveStep m n)
    (word : Binary.BinaryWord m)
    (source : ContractingState word) : Set where
  constructor certifiedStep
  field
    target : ContractingState (applyStep step word)
    barrierNonincrease :
      sharpBarrier (applyStep step word) target
      ≤ sharpBarrier word source

open CertifiedStep public

------------------------------------------------------------------------
-- Every invariant not definitionally enforced by the AST is explicit here.
------------------------------------------------------------------------

record ActualCertifiedPath
    {n : Nat}
    (x : Syracuse.PositiveNat)
    (ast : PrimitiveAST zero n) : Set where
  constructor actualCertifiedPath
  field
    actualWord :
      applyAST ast Binary.end ≡ Itinerary.parityWord n x

    contracting :
      ContractingState (applyAST ast Binary.end)

    barrierBelowStart :
      sharpBarrier (applyAST ast Binary.end) contracting
      < Syracuse.toNat x

open ActualCertifiedPath public

------------------------------------------------------------------------
-- KEY OPEN LEMMA / ONLY THEOREM-STRENGTH INHABITANT.
--
-- For every nontrivial literal start, construct a finite typed continuation
-- AST whose evaluated word is the ACTUAL parity prefix, is contracting, and
-- whose exact sharp barrier lies below the fixed start.
--
-- This is a typed AST normal form of the already-owned universal correction-
-- escape source.  No inhabitant is supplied here.
------------------------------------------------------------------------

record UniversalASTBarrierEscapeSource : Set₁ where
  field
    escape :
      (x : Syracuse.PositiveNat) →
      1 < Syracuse.toNat x →
      Σ Nat (λ n →
        Σ (PrimitiveAST zero n) (λ ast →
          ActualCertifiedPath x ast))

open UniversalASTBarrierEscapeSource public

------------------------------------------------------------------------
-- Equivalence-facing source socket.
--
-- The pre-existing terminal source remains canonical theorem authority.  This
-- field records that an AST producer must eventually compile to that source;
-- it is intentionally a source interface rather than an assumed theorem.
------------------------------------------------------------------------

record ASTToCanonicalEscapeCompiler : Set₁ where
  field
    compile :
      UniversalASTBarrierEscapeSource →
      Survivor.UniversalContractingCorrectionEscapeSource

------------------------------------------------------------------------
-- Bounded invariant inventory.
------------------------------------------------------------------------

record PrimitiveASTBoundary : Set where
  constructor primitiveASTBoundary
  field
    typedPrimitiveASTPaid : Nat
    totalWordEvaluatorPaid : Nat
    lengthPreservedByIndices : Nat
    syntaxSeparatedFromActualOrbitProof : Nat
    syntaxSeparatedFromContractionProof : Nat
    syntaxSeparatedFromBarrierProof : Nat
    certifiedPathCarriesAllInvariants : Nat
    lateZeroUnconditionallySafeClassified : Nat
    lateOneZeroUnconditionallySafeClassified : Nat
    lateOneRequiresExactSideCondition : Nat

    everyASTIsActualSyracusePrefix : Nat
    everyASTIsContracting : Nat
    everyASTLowersBarrier : Nat
    localMonotonicityPromotedToUniversalEscape : Nat
    universalBarrierEscapeProducerPaid : Nat

canonicalPrimitiveASTBoundary : PrimitiveASTBoundary
canonicalPrimitiveASTBoundary =
  primitiveASTBoundary
    1 1 1 1 1 1 1 1 1 1
    0 0 0 0 0
