module DASHI.Analysis.ConstructiveRealCapabilityHierarchyExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Sigma using (Σ; _,_)
import Data.Nat.Base as NatOrder
open import Data.Sum.Base using (_⊎_)

import DASHI.Analysis.ConstructedRealBackendSpineExact as Spine
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Layered constructive-real capabilities.
--
-- Herman Geuvers and Milad Niqui,
-- "Constructive Reals in Coq: Axioms and Categoricity",
-- Types for Proofs and Programs, LNCS 2277 (2002), 79--95.
-- DOI: 10.1007/3-540-45842-5_6.
--
-- The paper treats a real-number structure as a Cauchy-complete Archimedean
-- constructive ordered field, with apartness, strong extensionality and an
-- explicit natural-number majorant.  This module keeps DASHI's small setoid
-- backend intact and adds those capabilities as siblings rather than inflating
-- SetoidOrderedCompleteReal into one monolithic record.
------------------------------------------------------------------------

data ⊥ : Set where

record _×_ (A B : Set) : Set where
  constructor pair
  field
    first : A
    second : B

open _×_ public

AbsSmall :
  (R : Spine.SetoidOrderedCompleteReal) →
  Spine.Carrier R → Spine.Carrier R → Set
AbsSmall R epsilon value =
  Spine._<_ R (Spine.neg R epsilon) value × Spine._<_ R value epsilon

record ConstructiveOrderedFieldCapability
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  infix 15 _#_
  field
    _#_ : Spine.Carrier R → Spine.Carrier R → Set

    apartIrreflexive : ∀ x → _#_ x x → ⊥
    apartSymmetric : ∀ {x y} → _#_ x y → _#_ y x
    apartCotransitive : ∀ {x y} → _#_ x y → ∀ z → _#_ x z ⊎ _#_ z y
    apartTight : ∀ {x y} → (_#_ x y → ⊥) → Spine._≈_ R x y

    ltIrreflexive : ∀ x → Spine._<_ R x x → ⊥
    ltTransitive : ∀ {x y z} →
      Spine._<_ R x y → Spine._<_ R y z → Spine._<_ R x z
    ltCotransitive : ∀ {x y} →
      Spine._<_ R x y → ∀ z → Spine._<_ R x z ⊎ Spine._<_ R z y
    ltAsymmetric : ∀ {x y} → Spine._<_ R x y → Spine._<_ R y x → ⊥
    apartnessFromOrder : ∀ {x y} →
      (Spine._<_ R x y ⊎ Spine._<_ R y x) → _#_ x y
    orderFromApartness : ∀ {x y} →
      _#_ x y → Spine._<_ R x y ⊎ Spine._<_ R y x

    addRespectsLt : ∀ {x y} → Spine._<_ R x y → ∀ z →
      Spine._<_ R (Spine._+_ R x z) (Spine._+_ R y z)
    positiveMulRespectsLt : ∀ {x y} →
      Spine._<_ R (Spine.zero R) x →
      Spine._<_ R (Spine.zero R) y →
      Spine._<_ R (Spine.zero R) (Spine._*_ R x y)

    reciprocal : (x : Spine.Carrier R) → _#_ x (Spine.zero R) → Spine.Carrier R
    reciprocalLeft : ∀ x x#0 →
      Spine._≈_ R
        (Spine._*_ R x (reciprocal x x#0))
        (Spine.one R)
    reciprocalStronglyExtensional : ∀ {x y} x#0 y#0 →
      _#_ (reciprocal x x#0) (reciprocal y y#0) → _#_ x y

open ConstructiveOrderedFieldCapability public

------------------------------------------------------------------------
-- Rational embedding, density and natural majorization.
--
-- The attached Geuvers--Niqui reference takes natural majorization as its
-- Archimedean primitive.  Some constructive-analysis presentations instead use
-- rational density.  We keep both notions and require an explicit bridge before
-- deriving one from the other; this avoids silently identifying non-equivalent
-- formulations outside the hypotheses where the equivalence is proved.
------------------------------------------------------------------------

record RationalEmbeddingStructure
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    Q : Set
    _≈Q_ : Q → Q → Set
    _<Q_ _≤Q_ : Q → Q → Set
    zeroQ oneQ : Q
    addQ subQ mulQ : Q → Q → Q
    negQ : Q → Q

    fromQ : Q → Spine.Carrier R
    fromQCong : ∀ {q r} → _≈Q_ q r → Spine._≈_ R (fromQ q) (fromQ r)
    fromQZero : Spine._≈_ R (fromQ zeroQ) (Spine.zero R)
    fromQOne : Spine._≈_ R (fromQ oneQ) (Spine.one R)
    fromQAdd : ∀ q r →
      Spine._≈_ R (fromQ (addQ q r)) (Spine._+_ R (fromQ q) (fromQ r))
    fromQSub : ∀ q r →
      Spine._≈_ R (fromQ (subQ q r)) (Spine._-_ R (fromQ q) (fromQ r))
    fromQMul : ∀ q r →
      Spine._≈_ R (fromQ (mulQ q r)) (Spine._*_ R (fromQ q) (fromQ r))
    fromQNeg : ∀ q → Spine._≈_ R (fromQ (negQ q)) (Spine.neg R (fromQ q))
    rationalLtPreserved : ∀ {q r} → _<Q_ q r → Spine._<_ R (fromQ q) (fromQ r)
    rationalLtReflected : ∀ {q r} → Spine._<_ R (fromQ q) (fromQ r) → _<Q_ q r
    rationalLePreserved : ∀ {q r} → _≤Q_ q r → Spine._≤_ R (fromQ q) (fromQ r)

open RationalEmbeddingStructure public

record RationalDensityStructure
    (R : Spine.SetoidOrderedCompleteReal)
    (Q : RationalEmbeddingStructure R) : Set₁ where
  field
    rationalDense : ∀ {x y} → Spine._<_ R x y →
      Σ (RationalEmbeddingStructure.Q Q)
        (λ q →
          Spine._<_ R x (fromQ Q q) ×
          Spine._<_ R (fromQ Q q) y)

open RationalDensityStructure public

record NaturalMajorizationStructure
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    fromNat : Nat → Spine.Carrier R
    fromNatZero : Spine._≈_ R (fromNat zero) (Spine.zero R)
    fromNatSuc : ∀ n →
      Spine._≈_ R (fromNat (suc n))
        (Spine._+_ R (fromNat n) (Spine.one R))
    naturalMajorant : ∀ x → Σ Nat (λ n → Spine._<_ R x (fromNat n))

open NaturalMajorizationStructure public

record DensityMajorizationBridge
    (R : Spine.SetoidOrderedCompleteReal)
    (Q : RationalEmbeddingStructure R)
    (density : RationalDensityStructure R Q)
    (majorization : NaturalMajorizationStructure R) : Set₁ where
  field
    densityDerivedFromMajorization : ∀ {x y} → Spine._<_ R x y →
      Σ (RationalEmbeddingStructure.Q Q)
        (λ q → Spine._<_ R x (fromQ Q q) × Spine._<_ R (fromQ Q q) y)
    majorizationDerivedFromDensity : ∀ x →
      Σ Nat (λ n → Spine._<_ R x (fromNat majorization n))

open DensityMajorizationBridge public

archimedeanCeiling :
  ∀ {R Q density majorization} →
  DensityMajorizationBridge R Q density majorization →
  (x : Spine.Carrier R) →
  Σ Nat (λ n → Spine._<_ R x (fromNat majorization n))
archimedeanCeiling bridge = majorizationDerivedFromDensity bridge

------------------------------------------------------------------------
-- Effective Cauchy and convergence witnesses.
------------------------------------------------------------------------

data CauchyDefinitionMode : Set where
  epsilonIndexed : CauchyDefinitionMode
  reciprocalNaturalIndexed : CauchyDefinitionMode

record EffectiveConvergenceStructure
    (R : Spine.SetoidOrderedCompleteReal) : Set₁ where
  field
    mode : CauchyDefinitionMode
    Precision : Set
    radius : Precision → Spine.Carrier R
    radiusPositive : ∀ precision → Spine._<_ R (Spine.zero R) (radius precision)

    cauchyModulus : ∀ sequence → Spine.IsCauchy R sequence →
      (precision : Precision) →
      Σ Nat
        (λ cutoff → ∀ index → NatOrder._≤_ cutoff index →
          AbsSmall R (radius precision)
            (Spine._-_ R
              (Spine.sequenceAt R sequence index)
              (Spine.sequenceAt R sequence cutoff)))

    convergenceModulus : ∀ sequence limit → Spine.ConvergesTo R sequence limit →
      (precision : Precision) →
      Σ Nat
        (λ cutoff → ∀ index → NatOrder._≤_ cutoff index →
          AbsSmall R (radius precision)
            (Spine._-_ R
              (Spine.sequenceAt R sequence index)
              limit))

    cauchyModulusSound : ∀ sequence → Set
    convergenceModulusSound : ∀ sequence limit → Set
    epsilonAndReciprocalDefinitionsAgreeUnderArchimedeanBridge : Set

open EffectiveConvergenceStructure public

------------------------------------------------------------------------
-- Geuvers--Niqui minimal homomorphisms and derived transport laws.
------------------------------------------------------------------------

record ConstructiveRealHomomorphism
    (Source Target : Spine.SetoidOrderedCompleteReal)
    (sourceField : ConstructiveOrderedFieldCapability Source)
    (targetField : ConstructiveOrderedFieldCapability Target) : Set₁ where
  field
    map : Spine.Carrier Source → Spine.Carrier Target
    stronglyExtensional : ∀ {x y} →
      ConstructiveOrderedFieldCapability._#_ targetField (map x) (map y) →
      ConstructiveOrderedFieldCapability._#_ sourceField x y
    preservesLt : ∀ {x y} → Spine._<_ Source x y → Spine._<_ Target (map x) (map y)
    preservesAdd : ∀ x y →
      Spine._≈_ Target
        (map (Spine._+_ Source x y))
        (Spine._+_ Target (map x) (map y))
    preservesMul : ∀ x y →
      Spine._≈_ Target
        (map (Spine._*_ Source x y))
        (Spine._*_ Target (map x) (map y))

open ConstructiveRealHomomorphism public

record DerivedHomomorphismLaws
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : ConstructiveOrderedFieldCapability Source}
    {targetField : ConstructiveOrderedFieldCapability Target}
    (hom : ConstructiveRealHomomorphism Source Target sourceField targetField) : Set₁ where
  field
    respectsEquality : ∀ {x y} → Spine._≈_ Source x y →
      Spine._≈_ Target (map hom x) (map hom y)
    preservesApartness : ∀ {x y} →
      ConstructiveOrderedFieldCapability._#_ sourceField x y →
      ConstructiveOrderedFieldCapability._#_ targetField (map hom x) (map hom y)
    reflectsLt : ∀ {x y} → Spine._<_ Target (map hom x) (map hom y) →
      Spine._<_ Source x y
    preservesLe : ∀ {x y} → Spine._≤_ Source x y →
      Spine._≤_ Target (map hom x) (map hom y)
    reflectsLe : ∀ {x y} → Spine._≤_ Target (map hom x) (map hom y) →
      Spine._≤_ Source x y
    preservesZero : Spine._≈_ Target (map hom (Spine.zero Source)) (Spine.zero Target)
    preservesOne : Spine._≈_ Target (map hom (Spine.one Source)) (Spine.one Target)
    preservesSub : ∀ x y →
      Spine._≈_ Target
        (map hom (Spine._-_ Source x y))
        (Spine._-_ Target (map hom x) (map hom y))
    preservesNeg : ∀ x →
      Spine._≈_ Target (map hom (Spine.neg Source x)) (Spine.neg Target (map hom x))
    preservesAbs : ∀ x →
      Spine._≈_ Target (map hom (Spine.abs Source x)) (Spine.abs Target (map hom x))
    preservesReciprocal : ∀ x x#0 →
      Spine._≈_ Target
        (map hom (reciprocal sourceField x x#0))
        (reciprocal targetField (map hom x) (preservesApartness x#0))

open DerivedHomomorphismLaws public

asSetoidRealMorphism :
  ∀ {Source Target sourceField targetField}
    (hom : ConstructiveRealHomomorphism Source Target sourceField targetField) →
  DerivedHomomorphismLaws hom →
  Spine.SetoidRealMorphism Source Target
asSetoidRealMorphism hom derived = record
  { map = map hom
  ; respectsEquality = respectsEquality derived
  ; preservesZero = preservesZero derived
  ; preservesOne = preservesOne derived
  ; preservesAdd = preservesAdd hom
  ; preservesSub = preservesSub derived
  ; preservesMul = preservesMul hom
  ; preservesNeg = preservesNeg derived
  ; preservesAbs = preservesAbs derived
  ; preservesLe = preservesLe derived
  ; preservesLt = preservesLt hom
  }

record RationalHomomorphismCompatibility
    {Source Target : Spine.SetoidOrderedCompleteReal}
    (sourceQ : RationalEmbeddingStructure Source)
    (targetQ : RationalEmbeddingStructure Target)
    (commonRational : Set)
    (decodeSource : commonRational → RationalEmbeddingStructure.Q sourceQ)
    (decodeTarget : commonRational → RationalEmbeddingStructure.Q targetQ)
    {sourceField : ConstructiveOrderedFieldCapability Source}
    {targetField : ConstructiveOrderedFieldCapability Target}
    (hom : ConstructiveRealHomomorphism Source Target sourceField targetField) : Set₁ where
  field
    preservesRationalEmbedding : ∀ q →
      Spine._≈_ Target
        (map hom (fromQ sourceQ (decodeSource q)))
        (fromQ targetQ (decodeTarget q))

open RationalHomomorphismCompatibility public

record CompleteHomomorphismCompatibility
    {Source Target : Spine.SetoidOrderedCompleteReal}
    {sourceField : ConstructiveOrderedFieldCapability Source}
    {targetField : ConstructiveOrderedFieldCapability Target}
    (hom : ConstructiveRealHomomorphism Source Target sourceField targetField) : Set₁ where
  field
    mapSequence : Spine.Sequence Source → Spine.Sequence Target
    sequenceMapPointwise : ∀ sequence index →
      Spine._≈_ Target
        (Spine.sequenceAt Target (mapSequence sequence) index)
        (map hom (Spine.sequenceAt Source sequence index))
    preservesCauchy : ∀ sequence → Spine.IsCauchy Source sequence →
      Spine.IsCauchy Target (mapSequence sequence)
    preservesLimits : ∀ sequence limit → Spine.ConvergesTo Source sequence limit →
      Spine.ConvergesTo Target (mapSequence sequence) (map hom limit)

open CompleteHomomorphismCompatibility public

constructiveOrderedFieldCapabilityLevel : ProofLevel
constructiveOrderedFieldCapabilityLevel = machineChecked

rationalDensityAndMajorizationSeparationLevel : ProofLevel
rationalDensityAndMajorizationSeparationLevel = machineChecked

effectiveConvergenceCapabilityLevel : ProofLevel
effectiveConvergenceCapabilityLevel = machineChecked

minimalHomomorphismDefinitionLevel : ProofLevel
minimalHomomorphismDefinitionLevel = machineChecked

derivedHomomorphismLawsInputsLevel : ProofLevel
derivedHomomorphismLawsInputsLevel = conditional
