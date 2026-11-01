module DASHI.Analysis.RiemannConstructedRealPhaseCoherenceExact where

open import Agda.Builtin.Equality using (_≡_; refl; sym; trans; cong)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

open import DASHI.Analysis.ConstructiveRealSpine
open import DASHI.Analysis.ConcreteComplex
open import DASHI.Analysis.MarxConstructiveRealRingNormalisation
import DASHI.Analysis.RiemannConstructedComplexCharacterCoreExact as CharacterCore

------------------------------------------------------------------------
-- BIDI DESCENT FOR H_X^phase
--
-- The earlier character core exposed
--
--   -(t u) + b u = (b - t) u
--
-- as a missing real-phase theorem.  Existing constructive-real infrastructure
-- already supplies:
--
--   b - t = b + (-t)                         subAsAddNeg
--   (b + (-t)) u = b u + ((-t) u)            distribRight
--   x + y = y + x                            addComm
--
-- Hence the whole RH-specific phase theorem reduces to one ordinary ring law:
--
--   -(t u) = (-t) u.
--
-- This owner keeps that leaf generic and proves the RH phase identity from it;
-- no character-, pole-, or Riemann-specific normalization is inserted here.
------------------------------------------------------------------------

record ConstructedRealNegationMultiplicationLaw
    (R : ConstructedOrderedCompleteReal) : Set₁ where
  field
    negMulRight :
      (t u : Real R) →
      neg R (_*_ R t u) ≡ _*_ R (neg R t) u

open ConstructedRealNegationMultiplicationLaw public

phaseCoherenceFromRingNormalisation :
  ∀ {R : ConstructedOrderedCompleteReal} →
  (N : ConstructedRealRingNormalisationLaws R) →
  ConstructedRealNegationMultiplicationLaw R →
  (b t u : Real R) →
  _+_ R (neg R (_*_ R t u)) (_*_ R b u)
  ≡ _*_ R (_-_ R b t) u
phaseCoherenceFromRingNormalisation {R} N M b t u =
  trans
    (cong (λ x → _+_ R x (_*_ R b u)) (negMulRight M t u))
    (trans
      (addComm R (_*_ R (neg R t) u) (_*_ R b u))
      (trans
        (sym (distribRight R b (neg R t) u))
        (cong (λ x → _*_ R x u) (sym (subAsAddNeg N b t)))))

realPhaseCoherenceFromRingNormalisation :
  (C : ConstructedComplexPackage) →
  (N : ConstructedRealRingNormalisationLaws (real (realPackage C))) →
  ConstructedRealNegationMultiplicationLaw (real (realPackage C)) →
  CharacterCore.RealPhaseCoherence C
realPhaseCoherenceFromRingNormalisation C N M =
  record
    { phaseGap = phaseCoherenceFromRingNormalisation N M
    }

record RealPhaseCoherenceReductionBoundary : Set where
  constructor real-phase-coherence-reduction-boundary
  field
    subAsAddNegAlreadyOwnedByRingNormalisation : Bool
    subAsAddNegAlreadyOwnedByRingNormalisationIsTrue :
      subAsAddNegAlreadyOwnedByRingNormalisation ≡ true

    distributivityAlreadyOwnedByConstructedRealSpine : Bool
    distributivityAlreadyOwnedByConstructedRealSpineIsTrue :
      distributivityAlreadyOwnedByConstructedRealSpine ≡ true

    phaseCoherenceRequiresIndependentRHSpecificAxiom : Bool
    phaseCoherenceRequiresIndependentRHSpecificAxiomIsFalse :
      phaseCoherenceRequiresIndependentRHSpecificAxiom ≡ false

    negationMultiplicationLawStillRequired : Bool
    negationMultiplicationLawStillRequiredIsTrue :
      negationMultiplicationLawStillRequired ≡ true

    rhDerived : Bool
    rhDerivedIsFalse : rhDerived ≡ false

    nextTheorem : String

realPhaseCoherenceReductionBoundary : RealPhaseCoherenceReductionBoundary
realPhaseCoherenceReductionBoundary =
  real-phase-coherence-reduction-boundary
    true refl
    true refl
    false refl
    true refl
    false refl
    "Prove neg (t * u) = (neg t) * u on the selected constructed real carrier; the RH phase-gap identity then follows from existing ring normalization and distributivity."
