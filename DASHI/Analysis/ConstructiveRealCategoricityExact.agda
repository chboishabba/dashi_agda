module DASHI.Analysis.ConstructiveRealCategoricityExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
import DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact as Capability
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Canonical constructive-real categoricity through rational approximants.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
--
-- Theorem 5.4 constructs, for every real, an explicit Cauchy sequence of
-- rationals converging to it.  Theorem 5.7 then builds the canonical map
--
--   source real -> rational approximants -> target rational embedding -> limit
--
-- and proves that all real-number structures are isomorphic.  The canonical map
-- below is therefore a definition, not an opaque existential field.
------------------------------------------------------------------------

record CommonRationalApproximationBridge
    (Source Target : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    Q : Set
    sourceFromQ : Q → Spine.Carrier Source
    targetFromQ : Q → Spine.Carrier Target

    sourceRationalApproximation : Spine.Carrier Source → Nat → Q
    targetRationalSequence : (Nat → Q) → Spine.Sequence Target

    targetSequenceAt : ∀ sequence index →
      Spine._≈_ Target
        (Spine.sequenceAt Target (targetRationalSequence sequence) index)
        (targetFromQ (sequence index))

    targetApproximationCauchy : ∀ value →
      Spine.IsCauchy Target
        (targetRationalSequence (sourceRationalApproximation value))

    sourceApproximationRealization :
      (value : Spine.Carrier Source) → Set
    rationalApproximationAlgorithmExact : Set

open CommonRationalApproximationBridge public

canonicalMap :
  ∀ {Source Target} →
  CommonRationalApproximationBridge Source Target →
  Spine.Carrier Source → Spine.Carrier Target
canonicalMap {Target = Target} bridge value =
  fst
    (Spine.cauchyLimit Target
      (targetRationalSequence bridge (sourceRationalApproximation bridge value))
      (targetApproximationCauchy bridge value))

canonicalMapConverges :
  ∀ {Source Target}
    (bridge : CommonRationalApproximationBridge Source Target)
    (value : Spine.Carrier Source) →
  Spine.ConvergesTo Target
    (targetRationalSequence bridge (sourceRationalApproximation bridge value))
    (canonicalMap bridge value)
canonicalMapConverges {Target = Target} bridge value =
  snd
    (Spine.cauchyLimit Target
      (targetRationalSequence bridge (sourceRationalApproximation bridge value))
      (targetApproximationCauchy bridge value))

record CanonicalHomomorphismEvidence
    {Source Target : Spine.SetoidOrderedCompleteReal}
    (sourceField : Capability.ConstructiveOrderedFieldCapability Source)
    (targetField : Capability.ConstructiveOrderedFieldCapability Target)
    (bridge : CommonRationalApproximationBridge Source Target) : Set₁ where
  field
    homomorphism :
      Capability.ConstructiveRealHomomorphism
        Source Target sourceField targetField
    mapIsCanonical : ∀ value →
      Capability.map homomorphism value ≡ canonicalMap bridge value
    derivedLaws : Capability.DerivedHomomorphismLaws homomorphism
    completeCompatibility : Capability.CompleteHomomorphismCompatibility homomorphism
    rationalApproximationLimitPreserved :
      (value : Spine.Carrier Source) → Set

open CanonicalHomomorphismEvidence public

canonicalSetoidMorphism :
  ∀ {Source Target sourceField targetField bridge} →
  CanonicalHomomorphismEvidence sourceField targetField bridge →
  Spine.SetoidRealMorphism Source Target
canonicalSetoidMorphism evidence =
  Capability.asSetoidRealMorphism
    (homomorphism evidence)
    (derivedLaws evidence)

record ConstructiveRealCategoricityAuthority
    (Left Right : Spine.SetoidOrderedCompleteReal) : Set₂ where
  field
    leftField : Capability.ConstructiveOrderedFieldCapability Left
    rightField : Capability.ConstructiveOrderedFieldCapability Right

    forwardBridge : CommonRationalApproximationBridge Left Right
    backwardBridge : CommonRationalApproximationBridge Right Left

    forwardEvidence :
      CanonicalHomomorphismEvidence leftField rightField forwardBridge
    backwardEvidence :
      CanonicalHomomorphismEvidence rightField leftField backwardBridge

    leftRoundTrip : ∀ value →
      Spine._≈_ Left
        (canonicalMap backwardBridge (canonicalMap forwardBridge value))
        value
    rightRoundTrip : ∀ value →
      Spine._≈_ Right
        (canonicalMap forwardBridge (canonicalMap backwardBridge value))
        value

    canonicalForwardUnique :
      ∀ (candidate :
          Capability.ConstructiveRealHomomorphism
            Left Right leftField rightField) →
        Capability.DerivedHomomorphismLaws candidate →
        Capability.CompleteHomomorphismCompatibility candidate →
        ((value : Spine.Carrier Left) → Set) →
        ∀ value →
          Spine._≈_ Right
            (Capability.map candidate value)
            (canonicalMap forwardBridge value)

    canonicalBackwardUnique :
      ∀ (candidate :
          Capability.ConstructiveRealHomomorphism
            Right Left rightField leftField) →
        Capability.DerivedHomomorphismLaws candidate →
        Capability.CompleteHomomorphismCompatibility candidate →
        ((value : Spine.Carrier Right) → Set) →
        ∀ value →
          Spine._≈_ Left
            (Capability.map candidate value)
            (canonicalMap backwardBridge value)

open ConstructiveRealCategoricityAuthority public

categoricityAsSetoidEquivalence :
  ∀ {Left Right} →
  ConstructiveRealCategoricityAuthority Left Right →
  Spine.SetoidRealEquivalence Left Right
categoricityAsSetoidEquivalence authority = record
  { toRight = canonicalSetoidMorphism (forwardEvidence authority)
  ; toLeft = canonicalSetoidMorphism (backwardEvidence authority)
  ; leftRoundTrip = leftRoundTrip authority
  ; rightRoundTrip = rightRoundTrip authority
  ; reflectsLe = Capability.reflectsLe (derivedLaws (forwardEvidence authority))
  ; reflectsLt = Capability.reflectsLt (derivedLaws (forwardEvidence authority))
  }

------------------------------------------------------------------------
-- Cauchy-completion presentation.
--
-- Theorem 4.1 of Geuvers--Niqui proves that Cauchy sequences over an
-- Archimedean constructive ordered field form a real-number structure.  This
-- record makes the representation comparison explicit for backends that are
-- both completions of the same rational carrier but use different sequence and
-- equality encodings.
------------------------------------------------------------------------

record CommonCauchyCompletionPresentation
    (Left Right : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    forward : CommonRationalApproximationBridge Left Right
    backward : CommonRationalApproximationBridge Right Left
    sameRationalCarrier : Q forward ≡ Q backward
    leftIsCauchyCompletionOfRationals : Set
    rightIsCauchyCompletionOfRationals : Set
    epsilonCauchyDefinitionSelected : Set
    reciprocalNaturalDefinitionEquivalentAfterArchimedeanProof : Set

open CommonCauchyCompletionPresentation public

canonicalMapDefinitionLevel : ProofLevel
canonicalMapDefinitionLevel = machineChecked

categoricityAuthorityDefinitionLevel : ProofLevel
categoricityAuthorityDefinitionLevel = machineChecked

canonicalHomomorphismAndUniquenessInputsLevel : ProofLevel
canonicalHomomorphismAndUniquenessInputsLevel = conditional

commonCauchyCompletionPresentationInputsLevel : ProofLevel
commonCauchyCompletionPresentationInputsLevel = conditional
