{-# OPTIONS --safe #-}
module DASHI.Wikimedia.KeyShoeIndexedTrigramWeaveExact where

-- DASHI downstream construction. Source R13 wheel remains provisional.
-- Zero is an added value, never a missing glyph.
open import DASHI.Core.Prelude
open import DASHI.Core.IndexedWeaveHyperfabricExact using (IndexedWeave)
import DASHI.Wikimedia.KeyShoeCLARAR13DihedralExact as R

data Value : Set where
  zeroValue : Value
  signedSlot : R.LetterSlot → Value

inverseValue : Value → Value
inverseValue zeroValue = zeroValue
inverseValue (signedSlot (R.slot b s)) = signedSlot (R.slot (R.reflectBody b) s)

negativeValue : Value → Value
negativeValue zeroValue = zeroValue
negativeValue (signedSlot x) = signedSlot (R.pairSwap x)

inverse² : (v : Value) → inverseValue (inverseValue v) ≡ v
inverse² zeroValue = refl
inverse² (signedSlot (R.slot b s)) rewrite R.reflectBodyInvolutive b = refl

negative² : (v : Value) → negativeValue (negativeValue v) ≡ v
negative² zeroValue = refl
negative² (signedSlot x) rewrite R.pairSwapInvolutive x = refl

record Triple : Set where
  constructor tri
  field left middle right : Value

mapTriple : (Value → Value) → Triple → Triple
mapTriple f (tri a b c) = tri (f a) (f b) (f c)

inversion sign reversal : Triple → Triple
inversion = mapTriple inverseValue
sign = mapTriple negativeValue
reversal (tri a b c) = tri c b a

inversion² : (x : Triple) → inversion (inversion x) ≡ x
inversion² (tri a b c) rewrite inverse² a | inverse² b | inverse² c = refl

sign² : (x : Triple) → sign (sign x) ≡ x
sign² (tri a b c) rewrite negative² a | negative² b | negative² c = refl

reversal² : (x : Triple) → reversal (reversal x) ≡ x
reversal² (tri a b c) = refl

record Mask : Set where
  constructor mask
  field i n w : Bool

toggle : Bool → (Triple → Triple) → Triple → Triple
toggle false f x = x
toggle true f x = f x

toggle² : (b : Bool) (f : Triple → Triple) →
  ((x : Triple) → f (f x) ≡ x) →
  (x : Triple) → toggle b f (toggle b f x) ≡ x
toggle² false f p x = refl
toggle² true f p x = p x

encode : Mask → Triple → Triple
encode (mask i n w) x = toggle w reversal (toggle n sign (toggle i inversion x))

decode : Mask → Triple → Triple
decode (mask i n w) x = toggle i inversion (toggle n sign (toggle w reversal x))

decodeEncode : (m : Mask) (x : Triple) → decode m (encode m x) ≡ x
decodeEncode (mask i n w) x
  rewrite toggle² w reversal reversal² (toggle n sign (toggle i inversion x))
        | toggle² n sign sign² (toggle i inversion x)
        | toggle² i inversion inversion² x = refl

encodeDecode : (m : Mask) (x : Triple) → encode m (decode m x) ≡ x
encodeDecode (mask i n w) x
  rewrite toggle² i inversion inversion² (toggle n sign (toggle w reversal x))
        | toggle² n sign sign² (toggle w reversal x)
        | toggle² w reversal reversal² x = refl

-- Generic native chart constructor, with a canonical residual, not an empty one.
chartWeave : {Index Base : Set} {State : Index → Set} →
  (e : (m : Index) → Base → State m) →
  (d : (m : Index) → State m → Base) →
  ((m : Index) (x : Base) → d m (e m x) ≡ x) →
  ((m : Index) (x : State m) → e m (d m x) ≡ x) →
  IndexedWeave Index State
chartWeave {Index} {Base} e d de ed = record
  { Path = λ _ _ → ⊤
  ; idPath = λ _ → tt
  ; _∙_ = λ _ _ → tt
  ; pathIdLeft = λ { tt → refl }
  ; pathIdRight = λ { tt → refl }
  ; pathAssoc = λ _ _ _ → refl
  ; transport = λ {source} {target} _ x → e target (d source x)
  ; transportId = ed
  ; transportComp = λ {i} {j} {k} _ _ x →
      sym (cong (e k) (de j (d i x)))
  ; Residual = λ _ → Base
  ; stateResidual = d
  ; residualAfter = λ {source} _ x → d source x
  ; residualId = λ _ _ → refl
  }

letterWeave : IndexedWeave Mask (λ _ → Triple)
letterWeave = chartWeave encode decode decodeEncode encodeDecode

canonicalResidualTransport : (m n : Mask) (x : Triple) →
  decode n (encode n (decode m x)) ≡ decode m x
canonicalResidualTransport m n x = decodeEncode n (decode m x)

-- The native weave is total on triples. A source-attested orbit predicate
-- is not assumed: pull back any chosen predicate along decode.
-- Any observation-only actor must respect the observation's fibres.
noObservationDescent : {Address Glyph : Set} →
  (observe : Address → Glyph) (move : Address → Address) →
  (p q : Address) → observe p ≡ observe q →
  (observe (move p) ≡ observe (move q) → ⊥) →
  (actor : Glyph → Glyph) →
  ((x : Address) → observe (move x) ≡ actor (observe x)) → ⊥
noObservationDescent observe move p q same different actor square =
  different (trans (square p) (trans (cong actor same) (sym (square q))))
