module DASHI.Foundations.WetteArithmeticTransitionBridgeExact where

------------------------------------------------------------------------
-- WETTE / DASHI ARITHMETIC-TRANSITION BRIDGE
--
-- Wette's historical transition rules are intentionally not guessed here.
-- Instead, this adapter says exactly what a recovered arithmetic rule must
-- provide to inhabit the repository's existing prime-exponent transport lane.
--
-- Each generator supplies an existing ScalarTransportStep.  Consequently the
-- machine transition carries an exact multiplication-only Goedel-scalar law:
--
--   p * G(next) = q * G(current)
--
-- No division over Nat and no metamathematical consequence is inferred.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import MonsterOntos using (SSP; toNat)
open import Ontology.GodelLattice using (FactorVec)
import Ontology.GodelScalarization as GS
import DASHI.Foundations.WetteConstructiveAutomatonExact as WetteMachine

record CertifiedArithmeticTransitionFamily : Set₁ where
  field
    Generator : Set
    debitPrime : Generator → SSP
    creditPrime : Generator → SSP
    transition :
      (g : Generator) →
      (state : FactorVec) →
      GS.ScalarTransportStep
        (debitPrime g)
        (creditPrime g)
        state

open CertifiedArithmeticTransitionFamily public

arithmeticStep :
  (family : CertifiedArithmeticTransitionFamily) →
  Generator family → FactorVec → FactorVec
arithmeticStep family g state =
  GS.target (transition family g state)

arithmeticStepScalarLaw :
  (family : CertifiedArithmeticTransitionFamily) →
  (g : Generator family) →
  (state : FactorVec) →
  toNat (debitPrime family g) * GS.G (arithmeticStep family g state)
    ≡ toNat (creditPrime family g) * GS.G state
arithmeticStepScalarLaw family g state =
  GS.transportScalarLaw (transition family g state)

------------------------------------------------------------------------
-- Adapter into the existing KernelInternal-based Wette machine surface.
-- The arithmetic transport family itself is total, so this generic adapter
-- uses the trivial admissible shell.  A historical reconstruction may replace
-- it with a stricter source-level admissibility predicate.
------------------------------------------------------------------------

trivialArithmeticMachine :
  CertifiedArithmeticTransitionFamily → WetteMachine.WetteMachineSpec
trivialArithmeticMachine family =
  record
    { State = FactorVec
    ; Generator = Generator family
    ; admissible = λ _ → true
    ; step = arithmeticStep family
    ; preservesAdmissible = λ _ _ _ → refl
    }

arithmeticMachineStepIsCertified :
  (family : CertifiedArithmeticTransitionFamily) →
  (g : Generator family) →
  (state : FactorVec) →
  toNat (debitPrime family g)
    * GS.G (WetteMachine.step (trivialArithmeticMachine family) g state)
    ≡ toNat (creditPrime family g) * GS.G state
arithmeticMachineStepIsCertified = arithmeticStepScalarLaw
