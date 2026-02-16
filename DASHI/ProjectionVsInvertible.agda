module DASHI.ProjectionVsInvertible where

open import DASHI.Prelude
open import DASHI.OperatorTypes

projection+invertible→identity :
  ∀ {S : Set} {K : S → S} →
  Projection K → Invertible K → (∀ x → K x ≡ x)
projection+invertible→identity {S} {K} P I x =
  let open Projection P
      open Invertible I
  in
  -- K is idempotent and invertible ⇒ K = id
  -- Proof: x = inv (K x); apply K both sides, use idempotence and right inverse.
  -- K x ≡ K (inv (K x)) ≡ (by right) K x; then show K (inv y) = inv y via idem.
  -- A clean derivation:
  --   inv (K x) ≡ x                      (left)
  --   K (inv (K x)) ≡ K x                (cong K)
  --   but K (inv (K x)) ≡ inv (K x)      (since K ∘ K = K and right inverse)
  -- so inv (K x) ≡ K x, hence x ≡ K x.
  let
    step1 : K (inv (K x)) ≡ K x
    step1 = cong K (left x)  -- K (inv (K x)) = K x

    step2 : K (inv (K x)) ≡ inv (K x)
    step2 =
      -- Using idempotence on y = inv (K x):
      -- K (K y) = K y; but K y = ? we need K (K (inv (K x))) = K (inv (K x))
      -- and K (K (inv (K x))) = K (inv (K x)) trivially; so this doesn’t help.
      -- Instead: use right inverse with y = K x:
      -- K (inv (K x)) = K x (already step1). We need inv (K x) = K x.
      -- We can get that by applying inv to both sides of idem at x:
      -- idem: K (K x) = K x
      -- apply inv: inv (K (K x)) = inv (K x)
      -- but inv (K (K x)) = K x (by left with argument K x)
      -- so K x = inv (K x).
      let
        a : inv (K (K x)) ≡ inv (K x)
        a = cong inv (Projection.idem P x)

        b : inv (K (K x)) ≡ K x
        b = Invertible.left I (K x)
      in
      trans (sym b) a

    invKx≡Kx : inv (K x) ≡ K x
    invKx≡Kx = sym step2

  in
  -- left x : inv (K x) = x, so x = K x
  trans (sym (Invertible.left I x)) invKx≡Kx
