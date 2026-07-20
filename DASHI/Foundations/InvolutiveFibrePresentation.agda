module DASHI.Foundations.InvolutiveFibrePresentation where

open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- A carrier may admit an exact encoded presentation with a coarser quotient.
-- The carrier involution is transported to the encoded representation while
-- leaving the quotient coordinate fixed. Encoded may be dependent internally;
-- this avoids assigning an arbitrary sign to the zero trit fibre.

record InvolutiveFibrePresentation : Set₁ where
  field
    Carrier : Set
    Encoded : Set
    Quotient : Set

    encode : Carrier → Encoded
    decode : Encoded → Carrier
    carrierInvolution : Carrier → Carrier
    encodedInvolution : Encoded → Encoded
    quotient : Encoded → Quotient

    decodeEncode : ∀ x → decode (encode x) ≡ x
    encodeDecode : ∀ e → encode (decode e) ≡ e
    involutionEquivariant :
      ∀ x → encode (carrierInvolution x) ≡ encodedInvolution (encode x)
    quotientInvariant :
      ∀ x → quotient (encodedInvolution (encode x)) ≡ quotient (encode x)

open InvolutiveFibrePresentation public
