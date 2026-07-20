module DASHI.Codec.TriadicGlobalInversionFold where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.TriadicMaskSign using
  ( Trit3
  ; tri3
  ; neg
  ; zero
  ; pos
  ; Sign
  ; minus
  ; plus
  ; Unit
  ; unit
  )

------------------------------------------------------------------------
-- Canonical representatives for T³ under global inversion u ↦ -u.
-- The zero state is fixed.  Every other orbit has two members, selected by
-- one polarity value.  Canonical nonzero representatives have first nonzero
-- coordinate positive.
------------------------------------------------------------------------

data Orbit14 : Set where
  q000 : Orbit14
  q00p q0p0 qp00 : Orbit14
  q0pn q0pp qpn0 qpp0 : Orbit14
  qp0n qp0p : Orbit14
  qpnn qpnp qppn qppp : Orbit14

PolarityPayload : Orbit14 → Set
PolarityPayload q000 = Unit
PolarityPayload _    = Sign

record Fold14 : Set where
  constructor fold14
  field
    orbit    : Orbit14
    polarity : PolarityPayload orbit

open Fold14 public

canonical : Orbit14 → Trit3
canonical q000 = tri3 zero zero zero
canonical q00p = tri3 zero zero pos
canonical q0p0 = tri3 zero pos  zero
canonical qp00 = tri3 pos  zero zero
canonical q0pn = tri3 zero pos  neg
canonical q0pp = tri3 zero pos  pos
canonical qpn0 = tri3 pos  neg  zero
canonical qpp0 = tri3 pos  pos  zero
canonical qp0n = tri3 pos  zero neg
canonical qp0p = tri3 pos  zero pos
canonical qpnn = tri3 pos  neg  neg
canonical qpnp = tri3 pos  neg  pos
canonical qppn = tri3 pos  pos  neg
canonical qppp = tri3 pos  pos  pos

negate : Trit3 → Trit3
negate (tri3 neg  neg  neg)  = tri3 pos  pos  pos
negate (tri3 neg  neg  zero) = tri3 pos  pos  zero
negate (tri3 neg  neg  pos)  = tri3 pos  pos  neg
negate (tri3 neg  zero neg)  = tri3 pos  zero pos
negate (tri3 neg  zero zero) = tri3 pos  zero zero
negate (tri3 neg  zero pos)  = tri3 pos  zero neg
negate (tri3 neg  pos  neg)  = tri3 pos  neg  pos
negate (tri3 neg  pos  zero) = tri3 pos  neg  zero
negate (tri3 neg  pos  pos)  = tri3 pos  neg  neg
negate (tri3 zero neg  neg)  = tri3 zero pos  pos
negate (tri3 zero neg  zero) = tri3 zero pos  zero
negate (tri3 zero neg  pos)  = tri3 zero pos  neg
negate (tri3 zero zero neg)  = tri3 zero zero pos
negate (tri3 zero zero zero) = tri3 zero zero zero
negate (tri3 zero zero pos)  = tri3 zero zero neg
negate (tri3 zero pos  neg)  = tri3 zero neg  pos
negate (tri3 zero pos  zero) = tri3 zero neg  zero
negate (tri3 zero pos  pos)  = tri3 zero neg  neg
negate (tri3 pos  neg  neg)  = tri3 neg  pos  pos
negate (tri3 pos  neg  zero) = tri3 neg  pos  zero
negate (tri3 pos  neg  pos)  = tri3 neg  pos  neg
negate (tri3 pos  zero neg)  = tri3 neg  zero pos
negate (tri3 pos  zero zero) = tri3 neg  zero zero
negate (tri3 pos  zero pos)  = tri3 neg  zero neg
negate (tri3 pos  pos  neg)  = tri3 neg  neg  pos
negate (tri3 pos  pos  zero) = tri3 neg  neg  zero
negate (tri3 pos  pos  pos)  = tri3 neg  neg  neg

decodeFold14 : Fold14 → Trit3
decodeFold14 (fold14 q000 unit) = canonical q000
decodeFold14 (fold14 q00p plus) = canonical q00p
decodeFold14 (fold14 q00p minus) = negate (canonical q00p)
decodeFold14 (fold14 q0p0 plus) = canonical q0p0
decodeFold14 (fold14 q0p0 minus) = negate (canonical q0p0)
decodeFold14 (fold14 qp00 plus) = canonical qp00
decodeFold14 (fold14 qp00 minus) = negate (canonical qp00)
decodeFold14 (fold14 q0pn plus) = canonical q0pn
decodeFold14 (fold14 q0pn minus) = negate (canonical q0pn)
decodeFold14 (fold14 q0pp plus) = canonical q0pp
decodeFold14 (fold14 q0pp minus) = negate (canonical q0pp)
decodeFold14 (fold14 qpn0 plus) = canonical qpn0
decodeFold14 (fold14 qpn0 minus) = negate (canonical qpn0)
decodeFold14 (fold14 qpp0 plus) = canonical qpp0
decodeFold14 (fold14 qpp0 minus) = negate (canonical qpp0)
decodeFold14 (fold14 qp0n plus) = canonical qp0n
decodeFold14 (fold14 qp0n minus) = negate (canonical qp0n)
decodeFold14 (fold14 qp0p plus) = canonical qp0p
decodeFold14 (fold14 qp0p minus) = negate (canonical qp0p)
decodeFold14 (fold14 qpnn plus) = canonical qpnn
decodeFold14 (fold14 qpnn minus) = negate (canonical qpnn)
decodeFold14 (fold14 qpnp plus) = canonical qpnp
decodeFold14 (fold14 qpnp minus) = negate (canonical qpnp)
decodeFold14 (fold14 qppn plus) = canonical qppn
decodeFold14 (fold14 qppn minus) = negate (canonical qppn)
decodeFold14 (fold14 qppp plus) = canonical qppp
decodeFold14 (fold14 qppp minus) = negate (canonical qppp)

encodeFold14 : Trit3 → Fold14
encodeFold14 (tri3 zero zero zero) = fold14 q000 unit
encodeFold14 (tri3 zero zero pos)  = fold14 q00p plus
encodeFold14 (tri3 zero zero neg)  = fold14 q00p minus
encodeFold14 (tri3 zero pos  zero) = fold14 q0p0 plus
encodeFold14 (tri3 zero neg  zero) = fold14 q0p0 minus
encodeFold14 (tri3 pos  zero zero) = fold14 qp00 plus
encodeFold14 (tri3 neg  zero zero) = fold14 qp00 minus
encodeFold14 (tri3 zero pos  neg)  = fold14 q0pn plus
encodeFold14 (tri3 zero neg  pos)  = fold14 q0pn minus
encodeFold14 (tri3 zero pos  pos)  = fold14 q0pp plus
encodeFold14 (tri3 zero neg  neg)  = fold14 q0pp minus
encodeFold14 (tri3 pos  neg  zero) = fold14 qpn0 plus
encodeFold14 (tri3 neg  pos  zero) = fold14 qpn0 minus
encodeFold14 (tri3 pos  pos  zero) = fold14 qpp0 plus
encodeFold14 (tri3 neg  neg  zero) = fold14 qpp0 minus
encodeFold14 (tri3 pos  zero neg)  = fold14 qp0n plus
encodeFold14 (tri3 neg  zero pos)  = fold14 qp0n minus
encodeFold14 (tri3 pos  zero pos)  = fold14 qp0p plus
encodeFold14 (tri3 neg  zero neg)  = fold14 qp0p minus
encodeFold14 (tri3 pos  neg  neg)  = fold14 qpnn plus
encodeFold14 (tri3 neg  pos  pos)  = fold14 qpnn minus
encodeFold14 (tri3 pos  neg  pos)  = fold14 qpnp plus
encodeFold14 (tri3 neg  pos  neg)  = fold14 qpnp minus
encodeFold14 (tri3 pos  pos  neg)  = fold14 qppn plus
encodeFold14 (tri3 neg  neg  pos)  = fold14 qppn minus
encodeFold14 (tri3 pos  pos  pos)  = fold14 qppp plus
encodeFold14 (tri3 neg  neg  neg)  = fold14 qppp minus

decode-encode-fold14 : ∀ t → decodeFold14 (encodeFold14 t) ≡ t
decode-encode-fold14 (tri3 neg  neg  neg)  = refl
decode-encode-fold14 (tri3 neg  neg  zero) = refl
decode-encode-fold14 (tri3 neg  neg  pos)  = refl
decode-encode-fold14 (tri3 neg  zero neg)  = refl
decode-encode-fold14 (tri3 neg  zero zero) = refl
decode-encode-fold14 (tri3 neg  zero pos)  = refl
decode-encode-fold14 (tri3 neg  pos  neg)  = refl
decode-encode-fold14 (tri3 neg  pos  zero) = refl
decode-encode-fold14 (tri3 neg  pos  pos)  = refl
decode-encode-fold14 (tri3 zero neg  neg)  = refl
decode-encode-fold14 (tri3 zero neg  zero) = refl
decode-encode-fold14 (tri3 zero neg  pos)  = refl
decode-encode-fold14 (tri3 zero zero neg)  = refl
decode-encode-fold14 (tri3 zero zero zero) = refl
decode-encode-fold14 (tri3 zero zero pos)  = refl
decode-encode-fold14 (tri3 zero pos  neg)  = refl
decode-encode-fold14 (tri3 zero pos  zero) = refl
decode-encode-fold14 (tri3 zero pos  pos)  = refl
decode-encode-fold14 (tri3 pos  neg  neg)  = refl
decode-encode-fold14 (tri3 pos  neg  zero) = refl
decode-encode-fold14 (tri3 pos  neg  pos)  = refl
decode-encode-fold14 (tri3 pos  zero neg)  = refl
decode-encode-fold14 (tri3 pos  zero zero) = refl
decode-encode-fold14 (tri3 pos  zero pos)  = refl
decode-encode-fold14 (tri3 pos  pos  neg)  = refl
decode-encode-fold14 (tri3 pos  pos  zero) = refl
decode-encode-fold14 (tri3 pos  pos  pos)  = refl
