module DASHI.Codec.DNACarrierFibre where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Core.Prelude using (_×_; _,_)
open import DASHI.Codec.DNAFirstFormalism using
  ( Base
  ; A
  ; C
  ; G
  ; T
  ; complement
  )

data ChemicalPair : Set where
  atPair : ChemicalPair
  cgPair : ChemicalPair

data ComplementPhase : Set where
  primaryPhase : ComplementPhase
  mirrorPhase : ComplementPhase

BaseFibre : Set
BaseFibre = ChemicalPair × ComplementPhase

encodeBaseFibre : Base → BaseFibre
encodeBaseFibre A = atPair , primaryPhase
encodeBaseFibre T = atPair , mirrorPhase
encodeBaseFibre C = cgPair , primaryPhase
encodeBaseFibre G = cgPair , mirrorPhase

decodeBaseFibre : BaseFibre → Base
decodeBaseFibre (atPair , primaryPhase) = A
decodeBaseFibre (atPair , mirrorPhase) = T
decodeBaseFibre (cgPair , primaryPhase) = C
decodeBaseFibre (cgPair , mirrorPhase) = G

decode-encode-base : ∀ b → decodeBaseFibre (encodeBaseFibre b) ≡ b
decode-encode-base A = refl
decode-encode-base C = refl
decode-encode-base G = refl
decode-encode-base T = refl

encode-decode-base : ∀ f → encodeBaseFibre (decodeBaseFibre f) ≡ f
encode-decode-base (atPair , primaryPhase) = refl
encode-decode-base (atPair , mirrorPhase) = refl
encode-decode-base (cgPair , primaryPhase) = refl
encode-decode-base (cgPair , mirrorPhase) = refl

flipComplementPhase : ComplementPhase → ComplementPhase
flipComplementPhase primaryPhase = mirrorPhase
flipComplementPhase mirrorPhase = primaryPhase

flipComplementPhase-involutive :
  ∀ p → flipComplementPhase (flipComplementPhase p) ≡ p
flipComplementPhase-involutive primaryPhase = refl
flipComplementPhase-involutive mirrorPhase = refl

complementFibre : BaseFibre → BaseFibre
complementFibre (q , p) = q , flipComplementPhase p

complementFibre-involutive :
  ∀ f → complementFibre (complementFibre f) ≡ f
complementFibre-involutive (atPair , primaryPhase) = refl
complementFibre-involutive (atPair , mirrorPhase) = refl
complementFibre-involutive (cgPair , primaryPhase) = refl
complementFibre-involutive (cgPair , mirrorPhase) = refl

encodeBaseFibre-complement-equivariant :
  ∀ b → encodeBaseFibre (complement b) ≡ complementFibre (encodeBaseFibre b)
encodeBaseFibre-complement-equivariant A = refl
encodeBaseFibre-complement-equivariant C = refl
encodeBaseFibre-complement-equivariant G = refl
encodeBaseFibre-complement-equivariant T = refl

chemicalPair : Base → ChemicalPair
chemicalPair b = first (encodeBaseFibre b)
  where
  first : ∀ {X Y : Set} → X × Y → X
  first (x , _) = x

complementPhase : Base → ComplementPhase
complementPhase b = second (encodeBaseFibre b)
  where
  second : ∀ {X Y : Set} → X × Y → Y
  second (_ , y) = y

chemicalPair-complement-invariant :
  ∀ b → chemicalPair (complement b) ≡ chemicalPair b
chemicalPair-complement-invariant A = refl
chemicalPair-complement-invariant C = refl
chemicalPair-complement-invariant G = refl
chemicalPair-complement-invariant T = refl

encodeBaseFibre-injective :
  ∀ {x y} → encodeBaseFibre x ≡ encodeBaseFibre y → x ≡ y
encodeBaseFibre-injective {A} {A} refl = refl
encodeBaseFibre-injective {A} {C} ()
encodeBaseFibre-injective {A} {G} ()
encodeBaseFibre-injective {A} {T} ()
encodeBaseFibre-injective {C} {A} ()
encodeBaseFibre-injective {C} {C} refl = refl
encodeBaseFibre-injective {C} {G} ()
encodeBaseFibre-injective {C} {T} ()
encodeBaseFibre-injective {G} {A} ()
encodeBaseFibre-injective {G} {C} ()
encodeBaseFibre-injective {G} {G} refl = refl
encodeBaseFibre-injective {G} {T} ()
encodeBaseFibre-injective {T} {A} ()
encodeBaseFibre-injective {T} {C} ()
encodeBaseFibre-injective {T} {G} ()
encodeBaseFibre-injective {T} {T} refl = refl
