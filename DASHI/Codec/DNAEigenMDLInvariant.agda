module DASHI.Codec.DNAEigenMDLInvariant where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _≤_; z≤n)

open import DASHI.Core.Prelude using (_×_; _,_)
open import DASHI.Codec.DNAFirstFormalism using
  ( Base; A; C; G; T; complement )
open import DASHI.Codec.DNACarrierFibre using
  ( BaseFibre
  ; ChemicalPair; atPair; cgPair
  ; ComplementPhase; primaryPhase; mirrorPhase
  ; encodeBaseFibre; decodeBaseFibre
  ; chemicalPair; complementPhase; flipComplementPhase
  ; decode-encode-base
  )

------------------------------------------------------------------------
-- Reconstructive representative plus residual.
-- The representative is the primary member of the chemical quotient; the
-- residual is the complement-orbit phase. Unlike a feature-only residual,
-- this pair reconstructs the exact nucleotide.

representative : Base → Base
representative A = A
representative T = A
representative C = C
representative G = C

residual : Base → ComplementPhase
residual = complementPhase

reconstruct : Base → ComplementPhase → Base
reconstruct A primaryPhase = A
reconstruct A mirrorPhase = T
reconstruct C primaryPhase = C
reconstruct C mirrorPhase = G
reconstruct T p = reconstruct A p
reconstruct G p = reconstruct C p

reconstruct-representative-residual :
  ∀ b → reconstruct (representative b) (residual b) ≡ b
reconstruct-representative-residual A = refl
reconstruct-representative-residual C = refl
reconstruct-representative-residual G = refl
reconstruct-representative-residual T = refl

representative-complement-invariant :
  ∀ b → representative (complement b) ≡ representative b
representative-complement-invariant A = refl
representative-complement-invariant C = refl
representative-complement-invariant G = refl
representative-complement-invariant T = refl

residual-complement-equivariant :
  ∀ b → residual (complement b) ≡ flipComplementPhase (residual b)
residual-complement-equivariant A = refl
residual-complement-equivariant C = refl
residual-complement-equivariant G = refl
residual-complement-equivariant T = refl

------------------------------------------------------------------------
-- Finite MDL/action selection over the two residual phases.
-- One unit is charged precisely when a candidate phase fails to reconstruct
-- the observed base from its selected representative.

phaseAction : Base → ComplementPhase → Nat
phaseAction A primaryPhase = zero
phaseAction A mirrorPhase = suc zero
phaseAction T primaryPhase = suc zero
phaseAction T mirrorPhase = zero
phaseAction C primaryPhase = zero
phaseAction C mirrorPhase = suc zero
phaseAction G primaryPhase = suc zero
phaseAction G mirrorPhase = zero

selectedActionZero : ∀ b → phaseAction b (residual b) ≡ zero
selectedActionZero A = refl
selectedActionZero C = refl
selectedActionZero G = refl
selectedActionZero T = refl

selectedActionMinimal :
  ∀ b candidate → phaseAction b (residual b) ≤ phaseAction b candidate
selectedActionMinimal A primaryPhase = z≤n
selectedActionMinimal A mirrorPhase = z≤n
selectedActionMinimal C primaryPhase = z≤n
selectedActionMinimal C mirrorPhase = z≤n
selectedActionMinimal G primaryPhase = z≤n
selectedActionMinimal G mirrorPhase = z≤n
selectedActionMinimal T primaryPhase = z≤n
selectedActionMinimal T mirrorPhase = z≤n

inducedUpdate : Base → Base
inducedUpdate = representative

representativeFixed : ∀ b → inducedUpdate (representative b) ≡ representative b
representativeFixed A = refl
representativeFixed C = refl
representativeFixed G = refl
representativeFixed T = refl

record EigenMDLReceipt : Set where
  field
    exactReconstruction :
      ∀ b → reconstruct (representative b) (residual b) ≡ b
    representativeIsFixed :
      ∀ b → inducedUpdate (representative b) ≡ representative b
    selectedResidualMinimal :
      ∀ b candidate → phaseAction b (residual b) ≤ phaseAction b candidate
    representativeMirrorLaw :
      ∀ b → representative (complement b) ≡ representative b
    residualMirrorLaw :
      ∀ b → residual (complement b) ≡ flipComplementPhase (residual b)

baseEigenMDLReceipt : EigenMDLReceipt
baseEigenMDLReceipt = record
  { exactReconstruction = reconstruct-representative-residual
  ; representativeIsFixed = representativeFixed
  ; selectedResidualMinimal = selectedActionMinimal
  ; representativeMirrorLaw = representative-complement-invariant
  ; residualMirrorLaw = residual-complement-equivariant
  }

------------------------------------------------------------------------
-- Operational exact invariant. BaseFibre is not advertised as a short CRC;
-- it is an injective two-coordinate invariant that detects every single-base
-- substitution. Shorter sketches can later be layered on with stated bounds.


data ⊥ : Set where

_≢_ : ∀ {X : Set} → X → X → Set
x ≢ y = x ≡ y → ⊥

cong : ∀ {X Y : Set} (f : X → Y) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

baseInvariant : Base → BaseFibre
baseInvariant = encodeBaseFibre

baseInvariant-injective :
  ∀ {x y} → baseInvariant x ≡ baseInvariant y → x ≡ y
baseInvariant-injective {x} {y} eq
  rewrite decode-encode-base x
        | decode-encode-base y = cong decodeBaseFibre eq

baseInvariant-detects-substitution :
  ∀ {x y} → x ≢ y → baseInvariant x ≢ baseInvariant y
baseInvariant-detects-substitution different sameInvariant =
  different (baseInvariant-injective sameInvariant)

wordInvariant : List Base → List BaseFibre
wordInvariant [] = []
wordInvariant (b ∷ bs) = baseInvariant b ∷ wordInvariant bs

wordDecodeInvariant : List BaseFibre → List Base
wordDecodeInvariant [] = []
wordDecodeInvariant (f ∷ fs) = decodeBaseFibre f ∷ wordDecodeInvariant fs

wordInvariant-roundtrip :
  ∀ xs → wordDecodeInvariant (wordInvariant xs) ≡ xs
wordInvariant-roundtrip [] = refl
wordInvariant-roundtrip (b ∷ bs)
  rewrite decode-encode-base b | wordInvariant-roundtrip bs = refl

wordInvariant-injective :
  ∀ {xs ys} → wordInvariant xs ≡ wordInvariant ys → xs ≡ ys
wordInvariant-injective {xs} {ys} eq
  rewrite wordInvariant-roundtrip xs
        | wordInvariant-roundtrip ys = cong wordDecodeInvariant eq

wordInvariant-detects-change :
  ∀ {xs ys} → xs ≢ ys → wordInvariant xs ≢ wordInvariant ys
wordInvariant-detects-change different sameInvariant =
  different (wordInvariant-injective sameInvariant)
