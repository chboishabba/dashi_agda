module DASHI.Mathematics.Complexity.PNotEqualsNPTerminalPrefixCompletenessVerifierExact where

------------------------------------------------------------------------
-- TERMINAL PREFIX COMPLETENESS + EXECUTABLE FINITE TERMINAL VERIFIER
--
-- Every RestrictionDerivation records one literal Shannon bit per step.  Given
-- any assignment for the variables still remaining at the current node, we can
-- push that suffix back through the derivation to obtain a full root-length
-- assignment.  At a zero-variable terminal node the suffix is empty, so every
-- terminal derivation is represented by a complete literal prefix.
--
-- The same recursion gives an executable verifier for terminal labels:
--
--   verifyTerminalTree q phi
--
-- explores both Shannon children until arity zero, where it compares the
-- finite-state terminal label against literal evaluation.  If the root check
-- returns true, every reachable zero-variable derivation has the correct
-- terminal label.  No SAT oracle or satisfiability predicate is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin)
open import Data.Vec.Base using (Vec; []; _∷_)

import DASHI.Mathematics.Complexity.BooleanFormulaSATSelfReductionExact as SAT
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family
import DASHI.Mathematics.Complexity.PNotEqualsNPQ1FiniteCandidateSemanticAdmissionExact as Candidate
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalFutureCongruenceExact as FutureSAT

------------------------------------------------------------------------
-- Fully apply a complete assignment to a same-width indexed formula.
------------------------------------------------------------------------

fullyRestrict :
  ∀ {variables : Nat} →
  Vec Bool variables →
  SAT.BooleanFormula variables →
  SAT.BooleanFormula zero
fullyRestrict [] formula =
  formula
fullyRestrict (bit ∷ bits) formula =
  fullyRestrict bits (SAT.restrictHead bit formula)

------------------------------------------------------------------------
-- Push a remaining-variable suffix back through an existing derivation.
------------------------------------------------------------------------

completePrefixFrom :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables} →
  Family.RestrictionDerivation root current →
  Vec Bool currentVariables →
  Vec Bool rootVariables
completePrefixFrom Family.restrictionRoot suffix =
  suffix
completePrefixFrom
    (Family.restrictionFalse derivation)
    suffix =
  completePrefixFrom derivation (false ∷ suffix)
completePrefixFrom
    (Family.restrictionTrue derivation)
    suffix =
  completePrefixFrom derivation (true ∷ suffix)

------------------------------------------------------------------------
-- Exact replay theorem.
------------------------------------------------------------------------

completePrefixReplay :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables}
    (derivation : Family.RestrictionDerivation root current)
    (suffix : Vec Bool currentVariables) →
  fullyRestrict
    (completePrefixFrom derivation suffix)
    root
  ≡
  fullyRestrict suffix current
completePrefixReplay Family.restrictionRoot suffix =
  refl
completePrefixReplay
    (Family.restrictionFalse derivation)
    suffix =
  completePrefixReplay derivation (false ∷ suffix)
completePrefixReplay
    (Family.restrictionTrue derivation)
    suffix =
  completePrefixReplay derivation (true ∷ suffix)

------------------------------------------------------------------------
-- Terminal specialization.
------------------------------------------------------------------------

terminalPrefix :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {terminal : SAT.BooleanFormula zero} →
  Family.RestrictionDerivation root terminal →
  Vec Bool rootVariables
terminalPrefix derivation =
  completePrefixFrom derivation []

terminalPrefixReplay :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {terminal : SAT.BooleanFormula zero}
    (derivation : Family.RestrictionDerivation root terminal) →
  fullyRestrict (terminalPrefix derivation) root
  ≡
  terminal
terminalPrefixReplay derivation =
  completePrefixReplay derivation []

------------------------------------------------------------------------
-- Transition-table fold on literal prefixes, independent of semantic
-- admission.
------------------------------------------------------------------------

foldCandidateState :
  ∀ {rootVariables prefixLength : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root) →
  Vec Bool prefixLength →
  Fin (Candidate.stateCount candidate) →
  Fin (Candidate.stateCount candidate)
foldCandidateState candidate [] state =
  state
foldCandidateState candidate (bit ∷ bits) state =
  foldCandidateState
    candidate
    bits
    (Candidate.step candidate state bit)

foldAfterDerivation :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (derivation : Family.RestrictionDerivation root current)
    (suffix : Vec Bool currentVariables) →
  foldCandidateState
    candidate
    suffix
    (Candidate.candidateSelect candidate derivation)
  ≡
  foldCandidateState
    candidate
    (completePrefixFrom derivation suffix)
    (Candidate.rootState candidate)
foldAfterDerivation candidate Family.restrictionRoot suffix =
  refl
foldAfterDerivation candidate
    (Family.restrictionFalse derivation)
    suffix =
  foldAfterDerivation candidate derivation (false ∷ suffix)
foldAfterDerivation candidate
    (Family.restrictionTrue derivation)
    suffix =
  foldAfterDerivation candidate derivation (true ∷ suffix)

terminalGeneratedStateIsPrefixFold :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {terminal : SAT.BooleanFormula zero}
    (candidate : Candidate.TransitionTableCandidate root)
    (derivation : Family.RestrictionDerivation root terminal) →
  Candidate.candidateSelect candidate derivation
  ≡
  foldCandidateState
    candidate
    (terminalPrefix derivation)
    (Candidate.rootState candidate)
terminalGeneratedStateIsPrefixFold candidate derivation =
  foldAfterDerivation candidate derivation []

------------------------------------------------------------------------
-- Boolean equality and conjunction receipts.
------------------------------------------------------------------------

boolEq : Bool → Bool → Bool
boolEq false false = true
boolEq false true = false
boolEq true false = false
boolEq true true = true

boolEqTrueImpliesEqual :
  ∀ left right →
  boolEq left right ≡ true →
  left ≡ right
boolEqTrueImpliesEqual false false proof = refl
boolEqTrueImpliesEqual false true ()
boolEqTrueImpliesEqual true false ()
boolEqTrueImpliesEqual true true proof = refl

andTrueLeft :
  ∀ left right →
  SAT.andBool left right ≡ true →
  left ≡ true
andTrueLeft false right ()
andTrueLeft true false ()
andTrueLeft true true proof = refl

andTrueRight :
  ∀ left right →
  SAT.andBool left right ≡ true →
  right ≡ true
andTrueRight false right ()
andTrueRight true false ()
andTrueRight true true proof = refl

------------------------------------------------------------------------
-- Executable exhaustive verifier over the literal Shannon tree.
------------------------------------------------------------------------

verifyTerminalTree :
  ∀ {variables rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (terminalLabel : Fin (Candidate.stateCount candidate) → Bool) →
  Fin (Candidate.stateCount candidate) →
  SAT.BooleanFormula variables →
  Bool
verifyTerminalTree {variables = zero}
    candidate terminalLabel state formula =
  boolEq
    (terminalLabel state)
    (SAT.evaluate formula FutureSAT.emptyAssignment)
verifyTerminalTree {variables = suc remaining}
    candidate terminalLabel state formula =
  SAT.andBool
    (verifyTerminalTree
      candidate
      terminalLabel
      (Candidate.step candidate state false)
      (SAT.restrictHead false formula))
    (verifyTerminalTree
      candidate
      terminalLabel
      (Candidate.step candidate state true)
      (SAT.restrictHead true formula))

------------------------------------------------------------------------
-- Verification follows any reachable derivation.
------------------------------------------------------------------------

verifierFollowsDerivation :
  ∀ {rootVariables currentVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {current : SAT.BooleanFormula currentVariables}
    (candidate : Candidate.TransitionTableCandidate root)
    (terminalLabel : Fin (Candidate.stateCount candidate) → Bool)
    (derivation : Family.RestrictionDerivation root current) →
  verifyTerminalTree
    candidate
    terminalLabel
    (Candidate.rootState candidate)
    root
  ≡ true →
  verifyTerminalTree
    candidate
    terminalLabel
    (Candidate.candidateSelect candidate derivation)
    current
  ≡ true
verifierFollowsDerivation
    candidate
    terminalLabel
    Family.restrictionRoot
    rootVerified =
  rootVerified
verifierFollowsDerivation
    candidate
    terminalLabel
    (Family.restrictionFalse {current = current} derivation)
    rootVerified =
  falseBranch
  where
    parentState : Fin (Candidate.stateCount candidate)
    parentState = Candidate.candidateSelect candidate derivation

    parentVerified :
      verifyTerminalTree candidate terminalLabel parentState current ≡ true
    parentVerified =
      verifierFollowsDerivation
        candidate terminalLabel derivation rootVerified

    falseBranch :
      verifyTerminalTree
        candidate
        terminalLabel
        (Candidate.step candidate parentState false)
        (SAT.restrictHead false current)
      ≡ true
    falseBranch =
      andTrueLeft
        (verifyTerminalTree
          candidate terminalLabel
          (Candidate.step candidate parentState false)
          (SAT.restrictHead false current))
        (verifyTerminalTree
          candidate terminalLabel
          (Candidate.step candidate parentState true)
          (SAT.restrictHead true current))
        parentVerified
verifierFollowsDerivation
    candidate
    terminalLabel
    (Family.restrictionTrue {current = current} derivation)
    rootVerified =
  trueBranch
  where
    parentState : Fin (Candidate.stateCount candidate)
    parentState = Candidate.candidateSelect candidate derivation

    parentVerified :
      verifyTerminalTree candidate terminalLabel parentState current ≡ true
    parentVerified =
      verifierFollowsDerivation
        candidate terminalLabel derivation rootVerified

    trueBranch :
      verifyTerminalTree
        candidate
        terminalLabel
        (Candidate.step candidate parentState true)
        (SAT.restrictHead true current)
      ≡ true
    trueBranch =
      andTrueRight
        (verifyTerminalTree
          candidate terminalLabel
          (Candidate.step candidate parentState false)
          (SAT.restrictHead false current))
        (verifyTerminalTree
          candidate terminalLabel
          (Candidate.step candidate parentState true)
          (SAT.restrictHead true current))
        parentVerified

------------------------------------------------------------------------
-- Direct soundness at every terminal derivation.
------------------------------------------------------------------------

terminalVerifierSound :
  ∀ {rootVariables : Nat}
    {root : SAT.BooleanFormula rootVariables}
    {terminal : SAT.BooleanFormula zero}
    (candidate : Candidate.TransitionTableCandidate root)
    (terminalLabel : Fin (Candidate.stateCount candidate) → Bool) →
  verifyTerminalTree
    candidate
    terminalLabel
    (Candidate.rootState candidate)
    root
  ≡ true →
  (derivation : Family.RestrictionDerivation root terminal) →
  terminalLabel
    (Candidate.candidateSelect candidate derivation)
  ≡
  SAT.evaluate terminal FutureSAT.emptyAssignment
terminalVerifierSound
    candidate
    terminalLabel
    rootVerified
    derivation =
  boolEqTrueImpliesEqual
    (terminalLabel
      (Candidate.candidateSelect candidate derivation))
    (SAT.evaluate terminal FutureSAT.emptyAssignment)
    (verifierFollowsDerivation
      candidate
      terminalLabel
      derivation
      rootVerified)

------------------------------------------------------------------------
-- Max-cut receipt.
--
-- A terminal-label theorem no longer needs an external quantification over
-- arbitrary terminal derivations.  It is enough to execute one finite Boolean
-- verifier on the root transition system and prove that the computed result is
-- true.  Prefix completeness remains available as an exact diagnostic/witness
-- for each terminal path.
------------------------------------------------------------------------
