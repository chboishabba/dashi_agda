{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21StrictSATBoundedCertificateNPBoundaryExact where

------------------------------------------------------------------------
-- K00: SAME STRICT SAT WORD, FINITE POLYNOMIALLY SHORT CERTIFICATE.
--
-- The earlier strict Cook verifier is a real Boolean procedure.
-- The canonical-input decoder left inverse now bounds its accepted
-- certificate by the *input word itself*, even for an arbitrary input.
--
-- This module closes all semantic and certificate-size inequalities
-- needed by the same-word SAT InNP result. It then exposes precisely
-- the two independent executable-machine resource obligations.
-- These remain parameters until the concrete machine-clock/size
-- definitions certify them; this file never promotes their existence.
--
-- It also transports the original Cook-Levin exact-budget acceptance
-- iff to the SAME strictly parsed word with a bounded finite witness.
-- Sources: Cook 1971, Leonid Levin 1973; DASHI prior theorem owners.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.Product using (Σ; _×_; _,_)
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21CookStrictSATLanguageExact as SAT
import DASHI.Mathematics.Complexity.Karp21CookExecutableFiniteVerifierBidiExact as Verify
import DASHI.Mathematics.Complexity.Karp21CookAllWordCertificateBoundExact as Canonical
import DASHI.Mathematics.Complexity.Karp21CookLevinConcreteBitWordReuseExact as K00
import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Tape
import DASHI.Mathematics.Complexity.ConcreteTapeCanonicalCellBitsExact as Cell
import DASHI.Mathematics.Complexity.ConcreteTapeRuleSelectorExact as Rules
import DASHI.Mathematics.Complexity.ConcreteTapeInputInitialRowExact as Input
import DASHI.Mathematics.Complexity.ConcreteTapeCookLevinExactBudgetIff as Runs

-- The certificate is exactly List Bool; length is measured by the
-- canonical FiniteWordSizeExact source owner, NOT a separate metric.
strictSATCertificateAdmissible :
  Word.BitWord → Word.BitWord → Set
strictSATCertificateAdmissible word certificate =
  Word.encodingSize certificate ≤ Word.encodingSize word

BoundedStrictSATWitnessYES : Word.BitWord → Set
BoundedStrictSATWitnessYES word =
  Σ Word.BitWord
    (λ certificate →
      strictSATCertificateAdmissible word certificate
      × Verify.verifyStrictCookSATWord word certificate ≡ true)

strictSATToBoundedWitness :
  (word : Word.BitWord) →
  PR.accepts SAT.strictSATLanguage word →
  BoundedStrictSATWitnessYES word
strictSATToBoundedWitness word sat
  with Verify.strictCookExecutableVerifierComplete word sat
... | certificate , verified =
  certificate ,
    ( Canonical.k00StrictAcceptedWordCertificateBound
        word certificate verified
    , verified )

boundedWitnessToStrictSAT :
  (word : Word.BitWord) →
  BoundedStrictSATWitnessYES word →
  PR.accepts SAT.strictSATLanguage word
boundedWitnessToStrictSAT word
  (certificate , (bounded , verified)) =
  Verify.strictCookExecutableVerifierSound word
    (certificate , verified)

k00StrictSATBoundedWitnessBidi :
  (word : Word.BitWord) →
  PR.Iff
    (PR.accepts SAT.strictSATLanguage word)
    (BoundedStrictSATWitnessYES word)
k00StrictSATBoundedWitnessBidi word =
  PR.iff
    (strictSATToBoundedWitness word)
    (boundedWitnessToStrictSAT word)

-- An actual PR.InNP result from *exactly* the remaining clock and
-- generic model bound certificates. These are not filled by opaque
-- Bool "done" markers; they must inhabit the chosen nondegenerate
-- machine-cost interpretation.
k00StrictSATInNPFromConcreteResourceReceipts :
  (cost : PR.PolynomialCostModel Word.BitWord) →
  PR.polynomialTimeVerifier cost Verify.verifyStrictCookSATWord →
  PR.polynomialCertificateBound cost strictSATCertificateAdmissible →
  PR.InNP cost SAT.strictSATLanguage
k00StrictSATInNPFromConcreteResourceReceipts
  cost verifierClock certificateBound =
  record
    { PR.Certificate = Word.BitWord
    ; PR.verifies = Verify.verifyStrictCookSATWord
    ; PR.certificateAdmissible = strictSATCertificateAdmissible
    ; PR.sound = λ word certificate _ verified →
        Verify.strictCookExecutableVerifierSound word
          (certificate , verified)
    ; PR.complete = strictSATToBoundedWitness
    ; PR.polynomialVerification = verifierClock
    ; PR.polynomialCertificateSize = certificateBound
    }

------------------------------------------------------------------------
-- The actual exact-budget Cook-Levin machine also consumes the SAME
-- bounded certificate. No fresh SAT carrier and no oracle.
------------------------------------------------------------------------

concreteRunToBoundedStrictSATWitness :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  Runs.ExactBudgetAcceptingRun input steps →
  BoundedStrictSATWitnessYES
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
concreteRunToBoundedStrictSATWitness
  states symbols nonempty input steps run =
  strictSATToBoundedWitness
    (K00.guardedCookLevinBitWord states symbols nonempty input steps)
    (K00.exactRunToStrictCookSATWordAcceptance
      states symbols nonempty input steps run)

boundedStrictSATWitnessToConcreteRun :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  BoundedStrictSATWitnessYES
    (K00.guardedCookLevinBitWord states symbols nonempty input steps) →
  Runs.ExactBudgetAcceptingRun input steps
boundedStrictSATWitnessToConcreteRun
  states symbols nonempty input steps witness =
  K00.strictCookSATWordAcceptanceToRun
    states symbols nonempty input steps
    (boundedWitnessToStrictSAT
      (K00.guardedCookLevinBitWord states symbols nonempty input steps)
      witness)

------------------------------------------------------------------------
-- Universe-correct BIDI: Runs.ExactBudgetAcceptingRun : Set₁, whereas
-- PR.Iff is defined ONLY for two Set-valued propositions.
-- Reusing PR.Iff here was ill-sorted, not a missing typeclass instance.
------------------------------------------------------------------------

record ExactRunWitnessIff (Run : Set₁) (Witness : Set) : Set₁ where
  constructor exact-run-iff
  field
    runToWitness : Run → Witness
    witnessToRun : Witness → Run

k00ConcreteTapeRunBoundedStrictSATWitnessBidi :
  ∀ {machine : Tape.ConcreteTapeMachine}
    (states : Cell.EnumerationCoverage (Tape.finiteState machine))
    (symbols : Cell.EnumerationCoverage (Tape.finiteSymbol machine))
    (nonempty : Rules.NonemptyRuleTable machine)
    (input : Input.InputWord machine)
    (steps : Nat) →
  ExactRunWitnessIff
    (Runs.ExactBudgetAcceptingRun input steps)
    (BoundedStrictSATWitnessYES
      (K00.guardedCookLevinBitWord states symbols nonempty input steps))
k00ConcreteTapeRunBoundedStrictSATWitnessBidi
  states symbols nonempty input steps =
  exact-run-iff
    (concreteRunToBoundedStrictSATWitness
      states symbols nonempty input steps)
    (boundedStrictSATWitnessToConcreteRun
      states symbols nonempty input steps)
