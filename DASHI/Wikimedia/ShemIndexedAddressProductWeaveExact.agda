module DASHI.Wikimedia.ShemIndexedAddressProductWeaveExact where

-- DASHI downstream native source for the H2/H8 source-address carrier.
-- Source coordinates, letter values and occupancy are distinct.
open import DASHI.Core.Prelude
open import DASHI.Core.IndexedWeaveHyperfabricExact using (IndexedWeave)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv; inv-invol)
import DASHI.Wikimedia.KeyShoeIndexedTrigramWeaveExact as K

data Occupancy (A : Set) : Set where
  missing : Occupancy A
  occupied : A → Occupancy A

record Address : Set where
  constructor addr
  field
    row : Trit
    phase high low : Bool
    a b : Trit

flip : Bool → Bool
flip false = true
flip true = false

flip² : (x : Bool) → flip (flip x) ≡ x
flip² false = refl
flip² true = refl

-- q = 4*phase+2*high+low, r = row+1.
S A P : Address → Address
S (addr neg p h l a b) = addr neg p h l a b
S (addr pos p h l a b) = addr pos p h l a b
S (addr zer p h l a b) = addr zer (flip p) (flip h) (flip l) (inv a) (inv b)
A (addr r p h l a b) = addr (inv r) (flip p) (flip h) (flip l) (inv a) (inv b)
P (addr r p h l a b) = addr r (flip p) h l a b

S² : (x : Address) → S (S x) ≡ x
S² (addr neg p h l a b) = refl
S² (addr pos p h l a b) = refl
S² (addr zer p h l a b)
  rewrite flip² p | flip² h | flip² l | inv-invol a | inv-invol b = refl

A² : (x : Address) → A (A x) ≡ x
A² (addr r p h l a b)
  rewrite inv-invol r | flip² p | flip² h | flip² l | inv-invol a | inv-invol b = refl

P² : (x : Address) → P (P x) ≡ x
P² (addr r p h l a b) rewrite flip² p = refl

toggle : {X : Set} → Bool → (X → X) → X → X
toggle false f x = x
toggle true f x = f x

toggle² : {X : Set} (b : Bool) (f : X → X) →
  ((x : X) → f (f x) ≡ x) → (x : X) → toggle b f (toggle b f x) ≡ x
toggle² false f law x = refl
toggle² true f law x = law x

record SourceMask : Set where
  constructor sourceMask
  field s a p : Bool

encodeAddress decodeAddress : SourceMask → Address → Address
encodeAddress (sourceMask s a p) x = toggle p P (toggle a A (toggle s S x))
decodeAddress (sourceMask s a p) x = toggle s S (toggle a A (toggle p P x))

decodeEncodeAddress : (m : SourceMask) (x : Address) →
  decodeAddress m (encodeAddress m x) ≡ x
decodeEncodeAddress (sourceMask s a p) x
  rewrite toggle² p P P² (toggle a A (toggle s S x))
        | toggle² a A A² (toggle s S x)
        | toggle² s S S² x = refl

encodeDecodeAddress : (m : SourceMask) (x : Address) →
  encodeAddress m (decodeAddress m x) ≡ x
encodeDecodeAddress (sourceMask s a p) x
  rewrite toggle² s S S² (toggle a A (toggle p P x))
        | toggle² a A A² (toggle p P x)
        | toggle² p P P² x = refl

sourceWeave : IndexedWeave SourceMask (λ _ → Address)
sourceWeave = K.chartWeave encodeAddress decodeAddress decodeEncodeAddress encodeDecodeAddress

-- Generic product of reversible chart families. No source/letter actor
-- identification is entailed by this product.
productChartWeave : {I J B C : Set} {X : I → Set} {Y : J → Set} →
  (e : (i : I) → B → X i) (d : (i : I) → X i → B) →
  ((i : I) (b : B) → d i (e i b) ≡ b) →
  ((i : I) (x : X i) → e i (d i x) ≡ x) →
  (f : (j : J) → C → Y j) (g : (j : J) → Y j → C) →
  ((j : J) (c : C) → g j (f j c) ≡ c) →
  ((j : J) (y : Y j) → f j (g j y) ≡ y) →
  IndexedWeave (I × J) (λ ij → X (fst ij) × Y (snd ij))
productChartWeave e d de ed f g gf fg = K.chartWeave
  (λ { (i , j) (b , c) → e i b , f j c })
  (λ { (i , j) (x , y) → d i x , g j y })
  (λ { (i , j) (b , c) → cong₂ _,_ (de i b) (gf j c) })
  (λ { (i , j) (x , y) → cong₂ _,_ (ed i x) (fg j y) })

sourceLetterWeave : IndexedWeave (SourceMask × K.Mask) (λ _ → Address × K.Triple)
sourceLetterWeave = productChartWeave
  encodeAddress decodeAddress decodeEncodeAddress encodeDecodeAddress
  K.encode K.decode K.decodeEncode K.encodeDecode

-- All three source occurrence addresses are retained, independently of
-- whether a chart transformation breaks equal-column alignment.
record OccurrenceTriple : Set where
  constructor occurrences
  field first middle last : Address

encodeOccurrences decodeOccurrences : SourceMask → OccurrenceTriple → OccurrenceTriple
encodeOccurrences m (occurrences a b c) =
  occurrences (encodeAddress m a) (encodeAddress m b) (encodeAddress m c)
decodeOccurrences m (occurrences a b c) =
  occurrences (decodeAddress m a) (decodeAddress m b) (decodeAddress m c)

occurrencesDecodeEncode : (m : SourceMask) (x : OccurrenceTriple) →
  decodeOccurrences m (encodeOccurrences m x) ≡ x
occurrencesDecodeEncode m (occurrences a b c)
  rewrite decodeEncodeAddress m a | decodeEncodeAddress m b | decodeEncodeAddress m c = refl

occurrencesEncodeDecode : (m : SourceMask) (x : OccurrenceTriple) →
  encodeOccurrences m (decodeOccurrences m x) ≡ x
occurrencesEncodeDecode m (occurrences a b c)
  rewrite encodeDecodeAddress m a | encodeDecodeAddress m b | encodeDecodeAddress m c = refl

occurrenceLetterWeave :
  IndexedWeave (SourceMask × K.Mask) (λ _ → OccurrenceTriple × K.Triple)
occurrenceLetterWeave = productChartWeave
  encodeOccurrences decodeOccurrences occurrencesDecodeEncode occurrencesEncodeDecode
  K.encode K.decode K.decodeEncode K.encodeDecode
