module DASHI.Mathematics.Complexity.PSubsetNPTrivialCertificateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Stephen A. Cook,
-- "The complexity of theorem-proving procedures",
-- Proceedings of STOC 1971, 151--158.
-- DOI: 10.1145/800157.805047.
--
-- Richard M. Karp,
-- "Reducibility Among Combinatorial Problems", 1972.
-- No DOI is asserted for the original conference chapter here.
--
-- DASHI CONTRIBUTION
--
-- Close the repository's P subset NP bridge in its own language/verifier cost
-- model.  A polynomial-time decider becomes an NP verifier with the unique
-- unit certificate.  The only extra cost assumptions are stated explicitly:
-- ignoring a unit certificate preserves polynomial verification time, and the
-- unit certificate family has a polynomial size bound.
--
-- This is the standard exact inclusion P subseteq NP.  It does not prove
-- Cook--Levin, NP-completeness of SAT, or P=NP.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Agda.Builtin.Sigma using (Σ)

import DASHI.Mathematics.Complexity.PolynomialReductionExact as Complexity

record TrivialCertificateCostClosure
    {Word : Set}
    (cost : Complexity.PolynomialCostModel Word) : Set₁ where
  field
    deciderAsUnitVerifierPolynomial :
      (decider : Word → Bool) →
      Complexity.polynomialTimeDecider cost decider →
      Complexity.polynomialTimeVerifier cost
        (λ word (_ : ⊤) → decider word)

    unitCertificateBoundPolynomial :
      Complexity.polynomialCertificateBound cost
        (λ word (_ : ⊤) → ⊤)

open TrivialCertificateCostClosure public

promotePToNPWithUnitCertificate :
  ∀ {Word} {cost : Complexity.PolynomialCostModel Word} →
  TrivialCertificateCostClosure cost →
  (language : Complexity.Language Word) →
  Complexity.InP cost language →
  Complexity.InNP cost language
promotePToNPWithUnitCertificate closure language languageInP = record
  { Certificate = ⊤
  ; verifies = λ word certificate →
      Complexity.decide languageInP word
  ; certificateAdmissible = λ word certificate → ⊤
  ; sound = λ word certificate admissible accepted →
      Complexity.sound languageInP word accepted
  ; complete = λ word accepted →
      tt , (tt , Complexity.complete languageInP word accepted)
  ; polynomialVerification =
      deciderAsUnitVerifierPolynomial closure
        (Complexity.decide languageInP)
        (Complexity.polynomialDecision languageInP)
  ; polynomialCertificateSize =
      unitCertificateBoundPolynomial closure
  }

pIncludedInNPFromTrivialCertificate :
  ∀ {Word} {cost : Complexity.PolynomialCostModel Word} →
  TrivialCertificateCostClosure cost →
  Complexity.PIncludedInNP cost
pIncludedInNPFromTrivialCertificate closure = record
  { promotePToNP = λ language languageInP →
      promotePToNPWithUnitCertificate closure language languageInP
  }

unitCertificateCompletenessWitness :
  ∀ {Word} {cost : Complexity.PolynomialCostModel Word}
    (closure : TrivialCertificateCostClosure cost)
    (language : Complexity.Language Word)
    (languageInP : Complexity.InP cost language)
    word →
  Complexity.accepts language word →
  Σ ⊤ (λ certificate →
    ⊤ ×
    Complexity.InNP.verifies
      (promotePToNPWithUnitCertificate closure language languageInP)
      word certificate
    ≡ true)
unitCertificateCompletenessWitness closure language languageInP word accepted =
  Complexity.InNP.complete
    (promotePToNPWithUnitCertificate closure language languageInP)
    word accepted

npCompleteTargetInPNowUsesConstructedPSubsetNP :
  ∀ {Word} {cost : Complexity.PolynomialCostModel Word}
    (closure : TrivialCertificateCostClosure cost)
    (target : Complexity.Language Word) →
  Complexity.NPComplete cost target →
  Complexity.InP cost target →
  Complexity.PEqualsNP cost
npCompleteTargetInPNowUsesConstructedPSubsetNP closure target completeTarget targetInP =
  Complexity.npCompleteInPImpliesPEqualsNP
    (pIncludedInNPFromTrivialCertificate closure)
    target completeTarget targetInP
