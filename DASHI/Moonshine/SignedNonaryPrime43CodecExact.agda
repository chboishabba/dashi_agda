module DASHI.Moonshine.SignedNonaryPrime43CodecExact where
-- Source-written, kernel pending. Reuse the existing support/sign codec.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Codec.BalancedTritBitFibre using
  (Sign; positiveSign; negativeSign; invertSign; TritFibre; zeroFibre; signedFibre)
import DASHI.Moonshine.CM163Hecke41Signed43TorusExact as Torus

data Hex : Set where
  hex : Trit → Sign → Hex

-- The actual nonary sheet: T × (zero or sign).
-- Six removes the entire zero sheet. Seven retains only its centre.
data Seven : Set where
  centre : Seven
  active : Hex → Seven

data Word42 : Set where
  one : Hex → Word42
  two : Hex → Hex → Word42

data Word43 : Set where
  empty : Word43
  live : Word42 → Word43

split : Word42 → Seven → Word42
split w centre = w
split (one h) (active k) = two k h
split (two h j) (active k) = two k j

phase : Trit → Trit
phase neg = zer
phase zer = pos
phase pos = neg

flipHex : Hex → Hex
flipHex (hex t s) = hex t (invertSign s)

rotateHex : Hex → Hex
rotateHex (hex t s) = hex (phase t) s

flip : Word42 → Word42
flip (one h) = one (flipHex h)
flip (two k h) = two k (flipHex h)

rotate : Word42 → Word42
rotate (one h) = one (rotateHex h)
rotate (two k h) = two k (rotateHex h)

encode : Word42 → Fin 42
encode (one (hex neg positiveSign)) = (fz)
encode (one (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))
encode (one (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))
encode (one (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fz))))))))
encode (one (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))
encode (one (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))
encode (two (hex neg positiveSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))
encode (two (hex neg positiveSign) (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))
encode (two (hex neg positiveSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))
encode (two (hex neg positiveSign) (hex zer negativeSign)) = (fs (fz))
encode (two (hex neg positiveSign) (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))
encode (two (hex neg positiveSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))
encode (two (hex neg negativeSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))
encode (two (hex neg negativeSign) (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))
encode (two (hex neg negativeSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))
encode (two (hex neg negativeSign) (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))
encode (two (hex neg negativeSign) (hex pos positiveSign)) = (fs (fs (fz)))
encode (two (hex neg negativeSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))
encode (two (hex zer positiveSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))
encode (two (hex zer positiveSign) (hex neg negativeSign)) = (fs (fs (fs (fz))))
encode (two (hex zer positiveSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))
encode (two (hex zer positiveSign) (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))
encode (two (hex zer positiveSign) (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))
encode (two (hex zer positiveSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))
encode (two (hex zer negativeSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))
encode (two (hex zer negativeSign) (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))
encode (two (hex zer negativeSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fz)))))
encode (two (hex zer negativeSign) (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))
encode (two (hex zer negativeSign) (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))
encode (two (hex zer negativeSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))
encode (two (hex pos positiveSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))
encode (two (hex pos positiveSign) (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))
encode (two (hex pos positiveSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))
encode (two (hex pos positiveSign) (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))
encode (two (hex pos positiveSign) (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))
encode (two (hex pos positiveSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fz))))))
encode (two (hex pos negativeSign) (hex neg positiveSign)) = (fs (fs (fs (fs (fs (fs (fz)))))))
encode (two (hex pos negativeSign) (hex neg negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))
encode (two (hex pos negativeSign) (hex zer positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))
encode (two (hex pos negativeSign) (hex zer negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))
encode (two (hex pos negativeSign) (hex pos positiveSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))
encode (two (hex pos negativeSign) (hex pos negativeSign)) = (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))))

decode : Fin 42 → Word42
decode (fz) = (one (hex neg positiveSign))
decode (fs (fz)) = (two (hex neg positiveSign) (hex zer negativeSign))
decode (fs (fs (fz))) = (two (hex neg negativeSign) (hex pos positiveSign))
decode (fs (fs (fs (fz)))) = (two (hex zer positiveSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fz))))) = (two (hex zer negativeSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fz)))))) = (two (hex pos positiveSign) (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fz))))))) = (two (hex pos negativeSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = (one (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = (two (hex neg positiveSign) (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = (two (hex neg negativeSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = (two (hex zer positiveSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = (two (hex zer negativeSign) (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = (two (hex pos positiveSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = (two (hex pos negativeSign) (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = (one (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = (two (hex neg positiveSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = (two (hex neg negativeSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = (two (hex zer positiveSign) (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = (two (hex zer negativeSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = (two (hex pos positiveSign) (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = (two (hex pos negativeSign) (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = (one (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = (two (hex neg positiveSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = (two (hex neg negativeSign) (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = (two (hex zer positiveSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = (two (hex zer negativeSign) (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = (two (hex pos positiveSign) (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = (two (hex pos negativeSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = (one (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = (two (hex neg positiveSign) (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = (two (hex neg negativeSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = (two (hex zer positiveSign) (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = (two (hex zer negativeSign) (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = (two (hex pos positiveSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = (two (hex pos negativeSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = (one (hex pos negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = (two (hex neg positiveSign) (hex neg positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = (two (hex neg negativeSign) (hex zer negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = (two (hex zer positiveSign) (hex pos positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = (two (hex zer negativeSign) (hex neg negativeSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = (two (hex pos positiveSign) (hex zer positiveSign))
decode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = (two (hex pos negativeSign) (hex pos negativeSign))

encodeDecode : ∀ e → encode (decode e) ≡ e
encodeDecode (fz) = refl
encodeDecode (fs (fz)) = refl
encodeDecode (fs (fs (fz))) = refl
encodeDecode (fs (fs (fs (fz)))) = refl
encodeDecode (fs (fs (fs (fs (fz))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fz)))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fz))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fz)))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz))))))))))))))))))))))))))))))))))))))))) = refl
encodeDecode (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fs (fz)))))))))))))))))))))))))))))))))))))))))) = refl

decodeEncode : ∀ w → decode (encode w) ≡ w
decodeEncode (one (hex neg positiveSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex zer negativeSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex pos positiveSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex neg negativeSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex zer positiveSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex pos negativeSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex neg positiveSign)) = refl
decodeEncode (one (hex zer negativeSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex pos positiveSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex neg negativeSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex zer positiveSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex pos negativeSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex neg positiveSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex zer negativeSign)) = refl
decodeEncode (one (hex pos positiveSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex neg negativeSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex zer positiveSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex pos negativeSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex neg positiveSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex zer negativeSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex pos positiveSign)) = refl
decodeEncode (one (hex neg negativeSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex zer positiveSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex pos negativeSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex neg positiveSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex zer negativeSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex pos positiveSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex neg negativeSign)) = refl
decodeEncode (one (hex zer positiveSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex pos negativeSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex neg positiveSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex zer negativeSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex pos positiveSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex neg negativeSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex zer positiveSign)) = refl
decodeEncode (one (hex pos negativeSign)) = refl
decodeEncode (two (hex neg positiveSign) (hex neg positiveSign)) = refl
decodeEncode (two (hex neg negativeSign) (hex zer negativeSign)) = refl
decodeEncode (two (hex zer positiveSign) (hex pos positiveSign)) = refl
decodeEncode (two (hex zer negativeSign) (hex neg negativeSign)) = refl
decodeEncode (two (hex pos positiveSign) (hex zer positiveSign)) = refl
decodeEncode (two (hex pos negativeSign) (hex pos negativeSign)) = refl

flipRead : ∀ w → encode (flip w) ≡ Torus.halfTurn (encode w)
flipRead (one (hex neg positiveSign)) = refl
flipRead (two (hex neg positiveSign) (hex zer negativeSign)) = refl
flipRead (two (hex neg negativeSign) (hex pos positiveSign)) = refl
flipRead (two (hex zer positiveSign) (hex neg negativeSign)) = refl
flipRead (two (hex zer negativeSign) (hex zer positiveSign)) = refl
flipRead (two (hex pos positiveSign) (hex pos negativeSign)) = refl
flipRead (two (hex pos negativeSign) (hex neg positiveSign)) = refl
flipRead (one (hex zer negativeSign)) = refl
flipRead (two (hex neg positiveSign) (hex pos positiveSign)) = refl
flipRead (two (hex neg negativeSign) (hex neg negativeSign)) = refl
flipRead (two (hex zer positiveSign) (hex zer positiveSign)) = refl
flipRead (two (hex zer negativeSign) (hex pos negativeSign)) = refl
flipRead (two (hex pos positiveSign) (hex neg positiveSign)) = refl
flipRead (two (hex pos negativeSign) (hex zer negativeSign)) = refl
flipRead (one (hex pos positiveSign)) = refl
flipRead (two (hex neg positiveSign) (hex neg negativeSign)) = refl
flipRead (two (hex neg negativeSign) (hex zer positiveSign)) = refl
flipRead (two (hex zer positiveSign) (hex pos negativeSign)) = refl
flipRead (two (hex zer negativeSign) (hex neg positiveSign)) = refl
flipRead (two (hex pos positiveSign) (hex zer negativeSign)) = refl
flipRead (two (hex pos negativeSign) (hex pos positiveSign)) = refl
flipRead (one (hex neg negativeSign)) = refl
flipRead (two (hex neg positiveSign) (hex zer positiveSign)) = refl
flipRead (two (hex neg negativeSign) (hex pos negativeSign)) = refl
flipRead (two (hex zer positiveSign) (hex neg positiveSign)) = refl
flipRead (two (hex zer negativeSign) (hex zer negativeSign)) = refl
flipRead (two (hex pos positiveSign) (hex pos positiveSign)) = refl
flipRead (two (hex pos negativeSign) (hex neg negativeSign)) = refl
flipRead (one (hex zer positiveSign)) = refl
flipRead (two (hex neg positiveSign) (hex pos negativeSign)) = refl
flipRead (two (hex neg negativeSign) (hex neg positiveSign)) = refl
flipRead (two (hex zer positiveSign) (hex zer negativeSign)) = refl
flipRead (two (hex zer negativeSign) (hex pos positiveSign)) = refl
flipRead (two (hex pos positiveSign) (hex neg negativeSign)) = refl
flipRead (two (hex pos negativeSign) (hex zer positiveSign)) = refl
flipRead (one (hex pos negativeSign)) = refl
flipRead (two (hex neg positiveSign) (hex neg positiveSign)) = refl
flipRead (two (hex neg negativeSign) (hex zer negativeSign)) = refl
flipRead (two (hex zer positiveSign) (hex pos positiveSign)) = refl
flipRead (two (hex zer negativeSign) (hex neg negativeSign)) = refl
flipRead (two (hex pos positiveSign) (hex zer positiveSign)) = refl
flipRead (two (hex pos negativeSign) (hex pos negativeSign)) = refl

-- Arithmetic phase multiplication by 6, since 3^28 = 6 mod 43.
open import DASHI.Foundations.Base369Nat using (_%_)
rotateRead : ∀ w → Torus.unitLabel (encode (rotate w)) ≡ (6 * Torus.unitLabel (encode w)) % 43
rotateRead (one (hex neg positiveSign)) = refl
rotateRead (two (hex neg positiveSign) (hex zer negativeSign)) = refl
rotateRead (two (hex neg negativeSign) (hex pos positiveSign)) = refl
rotateRead (two (hex zer positiveSign) (hex neg negativeSign)) = refl
rotateRead (two (hex zer negativeSign) (hex zer positiveSign)) = refl
rotateRead (two (hex pos positiveSign) (hex pos negativeSign)) = refl
rotateRead (two (hex pos negativeSign) (hex neg positiveSign)) = refl
rotateRead (one (hex zer negativeSign)) = refl
rotateRead (two (hex neg positiveSign) (hex pos positiveSign)) = refl
rotateRead (two (hex neg negativeSign) (hex neg negativeSign)) = refl
rotateRead (two (hex zer positiveSign) (hex zer positiveSign)) = refl
rotateRead (two (hex zer negativeSign) (hex pos negativeSign)) = refl
rotateRead (two (hex pos positiveSign) (hex neg positiveSign)) = refl
rotateRead (two (hex pos negativeSign) (hex zer negativeSign)) = refl
rotateRead (one (hex pos positiveSign)) = refl
rotateRead (two (hex neg positiveSign) (hex neg negativeSign)) = refl
rotateRead (two (hex neg negativeSign) (hex zer positiveSign)) = refl
rotateRead (two (hex zer positiveSign) (hex pos negativeSign)) = refl
rotateRead (two (hex zer negativeSign) (hex neg positiveSign)) = refl
rotateRead (two (hex pos positiveSign) (hex zer negativeSign)) = refl
rotateRead (two (hex pos negativeSign) (hex pos positiveSign)) = refl
rotateRead (one (hex neg negativeSign)) = refl
rotateRead (two (hex neg positiveSign) (hex zer positiveSign)) = refl
rotateRead (two (hex neg negativeSign) (hex pos negativeSign)) = refl
rotateRead (two (hex zer positiveSign) (hex neg positiveSign)) = refl
rotateRead (two (hex zer negativeSign) (hex zer negativeSign)) = refl
rotateRead (two (hex pos positiveSign) (hex pos positiveSign)) = refl
rotateRead (two (hex pos negativeSign) (hex neg negativeSign)) = refl
rotateRead (one (hex zer positiveSign)) = refl
rotateRead (two (hex neg positiveSign) (hex pos negativeSign)) = refl
rotateRead (two (hex neg negativeSign) (hex neg positiveSign)) = refl
rotateRead (two (hex zer positiveSign) (hex zer negativeSign)) = refl
rotateRead (two (hex zer negativeSign) (hex pos positiveSign)) = refl
rotateRead (two (hex pos positiveSign) (hex neg negativeSign)) = refl
rotateRead (two (hex pos negativeSign) (hex zer positiveSign)) = refl
rotateRead (one (hex pos negativeSign)) = refl
rotateRead (two (hex neg positiveSign) (hex neg positiveSign)) = refl
rotateRead (two (hex neg negativeSign) (hex zer negativeSign)) = refl
rotateRead (two (hex zer positiveSign) (hex pos positiveSign)) = refl
rotateRead (two (hex zer negativeSign) (hex neg negativeSign)) = refl
rotateRead (two (hex pos positiveSign) (hex zer positiveSign)) = refl
rotateRead (two (hex pos negativeSign) (hex pos negativeSign)) = refl

chart : Word42 → Fin 42
chart w = Torus.decode (encode w)

unChart : Fin 42 → Word42
unChart k = decode (Torus.encode k)

open import Relation.Binary.PropositionalEquality using (cong; trans)
chartRoundTrip : ∀ w → unChart (chart w) ≡ w
chartRoundTrip w = trans (cong decode (Torus.encodeDecode (encode w))) (decodeEncode w)

wordRoundTrip : ∀ k → chart (unChart k) ≡ k
wordRoundTrip k = trans (cong Torus.decode (encodeDecode (Torus.encode k))) (Torus.decodeEncode k)

-- The depth-dependent sign action is on the final letter only.
-- It is not the simultaneous antipode of both letters.
