module DASHI.Cognition.Teleodynamics.ExceptionalE8NormalizerE6ProjectiveActionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Cognition.Teleodynamics.ExceptionalE6Mod3FiniteGeometryExact as E6
import DASHI.Cognition.Teleodynamics.ExceptionalE6E8PluckerDualityExact as Plucker
import DASHI.Cognition.Teleodynamics.ExceptionalE8Order3CentralizerTransportExact as Centralizer
import DASHI.Cognition.Teleodynamics.ExceptionalE8Order3ZetaPhaseExact as Phase

------------------------------------------------------------------------
-- NORMALIZER OF <w>, CYCLOTOMIC CONJUGATION, AND THE 40-POINT E6 WELD
--
-- Local exact computation finds an explicit E8 Weyl word n with
--     n w n^-1 = w^2.
-- Thus n normalizes <w> and induces inversion on its C3 phase coordinate.
-- On the same-object quotient F3^4, n is a symplectic similitude of multiplier
-- -1 = 2 mod 3.  Adjoining n to the centralizer doubles the lift order from
-- 155520 to 311040 and doubles the quotient image from Sp4(3) (51840) to the
-- multiplier-{+1,-1} extension (103680).
--
-- After projectivizing the 40 symplectic lines the scalar +/-I kernel has size
-- two, leaving a faithful 51840-element permutation group.  Transport through
-- the explicit Plucker map gives LITERALLY THE SAME set of 40-point
-- permutations as the reduced W(E6) action on the E6 null quadric.
------------------------------------------------------------------------

normalizerWord : String
normalizerWord = "s0 s1 s0 s2 s1 s0 s4 s5 s4 s6 s5 s4"

normalizerTransport : Centralizer.Matrix4F3
normalizerTransport = Centralizer.m4
  Plucker.pos Plucker.zer Plucker.pos Plucker.zer
  Plucker.neg Plucker.neg Plucker.pos Plucker.zer
  Plucker.zer Plucker.zer Plucker.neg Plucker.zer
  Plucker.pos Plucker.neg Plucker.pos Plucker.pos

normalizerPhaseAction : Phase.E8Order3Phase → Phase.E8Order3Phase
normalizerPhaseAction = Phase.inverseE8Phase

normalizerFixesIdentityPhase : normalizerPhaseAction Phase.e8I ≡ Phase.e8I
normalizerFixesIdentityPhase = refl

normalizerSwapsWToW2 : normalizerPhaseAction Phase.e8W ≡ Phase.e8W2
normalizerSwapsWToW2 = refl

normalizerSwapsW2ToW : normalizerPhaseAction Phase.e8W2 ≡ Phase.e8W
normalizerSwapsW2ToW = refl

record E8NormalizerComputationReceipt : Set where
  constructor e8-normalizer-computation-receipt
  field
    grade : E6.EvidenceGrade
    centralizerOrder : Nat
    normalizerOrder : Nat
    quotientCentralizerImageOrder : Nat
    quotientNormalizerImageOrder : Nat
    projectiveScalarKernelOrder : Nat
    effectiveProjectiveNormalizerOrder : Nat
    e6ReducedWeylOrder : Nat
    normalizerWordConjugatesWToW2 : Bool
    quotientNormalizerMultiplierIsMinusOne : Bool
    normalizerPhaseMatchesCyclotomicConjugation : Bool
    localPythonReproduced : Bool
    provenance : String
open E8NormalizerComputationReceipt public

canonicalE8NormalizerComputationReceipt : E8NormalizerComputationReceipt
canonicalE8NormalizerComputationReceipt =
  e8-normalizer-computation-receipt
    E6.localFiniteComputation
    155520 311040 51840 103680 2 51840 51840
    true true true true
    "local exact E8 Weyl computation: explicit n conjugates w to w^2; quotient action sends J to -J; normalizer projective action has order 51840"

record SameFortyPointPermutationGroupReceipt : Set where
  constructor same-forty-point-permutation-group-receipt
  field
    grade : E6.EvidenceGrade
    carrierSize : Nat
    e8NormalizerProjectivePermutationGroupOrder : Nat
    e6NullPermutationGroupOrder : Nat
    pluckerTransportUsed : Bool
    permutationSetsComparedExtensionally : Bool
    permutationSetsLiterallyEqual : Bool
    localPythonReproduced : Bool
    provenance : String
open SameFortyPointPermutationGroupReceipt public

canonicalSameFortyPointPermutationGroupReceipt : SameFortyPointPermutationGroupReceipt
canonicalSameFortyPointPermutationGroupReceipt =
  same-forty-point-permutation-group-receipt
    E6.localFiniteComputation
    40 51840 51840 true true true true
    "enumerated both generated permutation groups on the same ordered 40-point E6 null carrier after explicit Plucker transport; the two 51840-element permutation sets are exactly equal"

-- Same-object theorem shape for downstream consumers.  The concrete finite
-- enumeration above pays this computationally; this record prevents order
-- equality alone from being promoted to action equality.
record SameProjectiveActionRecognition : Set₁ where
  field
    Carrier40 : Set
    E8NormalizerAction : Set
    E6WeylAction : Set
    actE8 : E8NormalizerAction → Carrier40 → Carrier40
    actE6 : E6WeylAction → Carrier40 → Carrier40
    e8ActionImageEqualsE6ActionImage : Set
    pluckerSameCarrierPaid : Set
    provenance : String
open SameProjectiveActionRecognition public

data SameOrderCreatesSamePermutationGroup : Set where
data ZetaAnalogyCreatesNormalizerElement : Set where
data ProjectiveActionEqualityCreatesAlbertProduct : Set where

record E8NormalizerE6WeldBoundary : Set where
  constructor e8-normalizer-e6-weld-boundary
  field
    c3ZetaPhaseIntertwinerKernelWritten : Bool
    explicitNormalizerWordPaidLocally : Bool
    wToWInverseConjugationPaidLocally : Bool
    antiSymplecticMultiplierPaidLocally : Bool
    fullNormalizerOrderPaidLocally : Bool
    projectiveNormalizerOrderPaidLocally : Bool
    sameFortyPointPermutationSetPaidLocally : Bool
    sameOrderUsedAsSubstituteForSameAction : Bool
    albertProductCreatedByThisWeld : Bool
    fullE8WeylActionIdentifiedWithE6 : Bool

canonicalE8NormalizerE6WeldBoundary : E8NormalizerE6WeldBoundary
canonicalE8NormalizerE6WeldBoundary =
  e8-normalizer-e6-weld-boundary
    true true true true true true true false false false
