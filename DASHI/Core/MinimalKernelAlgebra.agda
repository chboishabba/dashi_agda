module DASHI.Core.MinimalKernelAlgebra where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)

------------------------------------------------------------------------
-- Ternary carrier and exact derived support/sign factorisation
------------------------------------------------------------------------

TernaryState : Set → Set
TernaryState X = X → Trit

pointwiseInvolution : {X : Set} → TernaryState X → TernaryState X
pointwiseInvolution s x = inv (s x)

pointwiseInvolutionLaw :
  {X : Set} (s : TernaryState X) (x : X) →
  pointwiseInvolution (pointwiseInvolution s) x ≡ s x
pointwiseInvolutionLaw s x = inv-invol (s x)

data Sign : Set where
  negative : Sign
  positive : Sign

data SupportSign : Set where
  inactive : SupportSign
  active   : Sign → SupportSign

encodeSupportSign : Trit → SupportSign
encodeSupportSign neg = active negative
encodeSupportSign zer = inactive
encodeSupportSign pos = active positive

decodeSupportSign : SupportSign → Trit
decodeSupportSign inactive          = zer
decodeSupportSign (active negative) = neg
decodeSupportSign (active positive) = pos

decodeEncodeSupportSign : (t : Trit) → decodeSupportSign (encodeSupportSign t) ≡ t
decodeEncodeSupportSign neg = refl
decodeEncodeSupportSign zer = refl
decodeEncodeSupportSign pos = refl

encodeDecodeSupportSign : (p : SupportSign) → encodeSupportSign (decodeSupportSign p) ≡ p
encodeDecodeSupportSign inactive          = refl
encodeDecodeSupportSign (active negative) = refl
encodeDecodeSupportSign (active positive) = refl

activityMask : Trit → Bool
activityMask neg = true
activityMask zer = false
activityMask pos = true

-- The Bool is a derived support observation.  It is not the primitive state.
maskAgreesWithFactorisation : (t : Trit) → Bool
maskAgreesWithFactorisation neg = true
maskAgreesWithFactorisation zer = true
maskAgreesWithFactorisation pos = true

------------------------------------------------------------------------
-- Symmetry action and minimal universal algebra
------------------------------------------------------------------------

record SymmetryAction (Γ S : Set) : Set₁ where
  field
    identity : Γ
    compose  : Γ → Γ → Γ
    act      : Γ → S → S

    leftIdentity  : (γ : Γ) → compose identity γ ≡ γ
    rightIdentity : (γ : Γ) → compose γ identity ≡ γ
    associative   : (α β γ : Γ) →
      compose (compose α β) γ ≡ compose α (compose β γ)

    identityActs : (s : S) → act identity s ≡ s
    composeActs  : (α β : Γ) (s : S) →
      act (compose α β) s ≡ act α (act β s)

record MinimalKernelAlgebra (Γ S : Set) : Set₁ where
  field
    symmetry   : SymmetryAction Γ S
    involution : S → S
    kernel     : S → S

    involutionLaw : (s : S) → involution (involution s) ≡ s
    kernelSymmetryEquivariant : (γ : Γ) (s : S) →
      kernel (SymmetryAction.act symmetry γ s) ≡
      SymmetryAction.act symmetry γ (kernel s)
    kernelInvolutionEquivariant : (s : S) →
      kernel (involution s) ≡ involution (kernel s)

------------------------------------------------------------------------
-- Composition algebra: the generated transformation monoid
------------------------------------------------------------------------

Operator : Set → Set
Operator S = S → S

identityOperator : {S : Set} → Operator S
identityOperator s = s

infixr 9 _∘op_

_∘op_ : {S : Set} → Operator S → Operator S → Operator S
(f ∘op g) s = f (g s)

operatorAssociative :
  {S : Set} (f g h : Operator S) (s : S) →
  ((f ∘op g) ∘op h) s ≡ (f ∘op (g ∘op h)) s
operatorAssociative f g h s = refl

operatorLeftIdentity :
  {S : Set} (f : Operator S) (s : S) →
  (identityOperator ∘op f) s ≡ f s
operatorLeftIdentity f s = refl

operatorRightIdentity :
  {S : Set} (f : Operator S) (s : S) →
  (f ∘op identityOperator) s ≡ f s
operatorRightIdentity f s = refl

data KernelGenerator (Γ : Set) : Set where
  kernelGenerator     : KernelGenerator Γ
  involutionGenerator : KernelGenerator Γ
  symmetryGenerator   : Γ → KernelGenerator Γ

evaluateGenerator :
  {Γ S : Set} → MinimalKernelAlgebra Γ S → KernelGenerator Γ → Operator S
evaluateGenerator A kernelGenerator = MinimalKernelAlgebra.kernel A
evaluateGenerator A involutionGenerator = MinimalKernelAlgebra.involution A
evaluateGenerator A (symmetryGenerator γ) =
  SymmetryAction.act (MinimalKernelAlgebra.symmetry A) γ

KernelWord : Set → Set
KernelWord Γ = List (KernelGenerator Γ)

evaluateWord :
  {Γ S : Set} → MinimalKernelAlgebra Γ S → KernelWord Γ → Operator S
evaluateWord A [] = identityOperator
evaluateWord A (generator ∷ rest) =
  evaluateWord A rest ∘op evaluateGenerator A generator

------------------------------------------------------------------------
-- Quotient compatibility without assuming a primitive set-quotient type
------------------------------------------------------------------------

record Equivalence (S : Set) : Set₁ where
  infix 4 _≈_
  field
    _≈_    : S → S → Set
    reflexive  : (s : S) → s ≈ s
    symmetric  : {s t : S} → s ≈ t → t ≈ s
    transitive : {r s t : S} → r ≈ s → s ≈ t → r ≈ t

record QuotientCompatible
  {Γ S : Set}
  (A : MinimalKernelAlgebra Γ S)
  (E : Equivalence S) : Set₁ where
  open Equivalence E
  field
    kernelCompatible : {s t : S} → s ≈ t →
      MinimalKernelAlgebra.kernel A s ≈ MinimalKernelAlgebra.kernel A t
    involutionCompatible : {s t : S} → s ≈ t →
      MinimalKernelAlgebra.involution A s ≈
      MinimalKernelAlgebra.involution A t
    symmetryCompatible : (γ : Γ) {s t : S} → s ≈ t →
      SymmetryAction.act (MinimalKernelAlgebra.symmetry A) γ s ≈
      SymmetryAction.act (MinimalKernelAlgebra.symmetry A) γ t

record QuotientObservation {S Q : Set} (E : Equivalence S) : Set₁ where
  open Equivalence E
  field
    observe : S → Q
    respectsEquivalence : {s t : S} → s ≈ t → observe s ≡ observe t

------------------------------------------------------------------------
-- One exact RG/coarse-graining square, optionally observed after quotient
------------------------------------------------------------------------

record QuotientRGStep
  {Γ₀ Γ₁ S₀ S₁ Q : Set}
  (fine   : MinimalKernelAlgebra Γ₀ S₀)
  (coarse : MinimalKernelAlgebra Γ₁ S₁) : Set₁ where
  field
    coarseGrain : S₀ → S₁
    quotientObserve : S₁ → Q
    commutesAfterQuotient : (s : S₀) →
      quotientObserve
        (coarseGrain (MinimalKernelAlgebra.kernel fine s))
      ≡
      quotientObserve
        (MinimalKernelAlgebra.kernel coarse (coarseGrain s))

------------------------------------------------------------------------
-- Optional ordered/action extension
--
-- A mismatch count is merely diagnostic unless supplied here with an actual
-- descent proof.  MDL/action monotonicity is therefore an additional law,
-- not a consequence of the bare kernel algebra.
------------------------------------------------------------------------

record ActionDescent
  {Γ S : Set}
  (A : MinimalKernelAlgebra Γ S) : Set₁ where
  field
    Cost : Set
    _≤cost_ : Cost → Cost → Set
    action : S → Cost
    kernelNonIncreasing : (s : S) →
      action (MinimalKernelAlgebra.kernel A s) ≤cost action s
