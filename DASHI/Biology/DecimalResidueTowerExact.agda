module DASHI.Biology.DecimalResidueTowerExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Fernando Q. Gouvea, "p-adic Numbers: An Introduction", 2nd ed.,
-- Springer, 1997. DOI: 10.1007/978-3-642-59058-0.
--
-- DASHI CONTRIBUTION
--
-- Construct the map that Round 7 deliberately did not assume.  A length-r
-- decimal address is identified with a canonical residue representative in
-- Fin (10^r).  Appending a digit is the mixed-radix `combine` operation, and
-- prefix is proved to commute with reduction to the lower modulus.
--
-- Fin (10^r) is used here as the finite SET of canonical representatives of
-- Z/(10^r)Z.  Ring operations are not inferred merely from this equivalence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP
import DASHI.Biology.IndexedJStratifiedMultiresolutionExact as J

------------------------------------------------------------------------
-- Decimal digits are exactly Fin 10.
------------------------------------------------------------------------

encodeDigit : J.DecimalDigit → Fin.Fin 10
encodeDigit J.d0 = Fin.zero
encodeDigit J.d1 = Fin.suc Fin.zero
encodeDigit J.d2 = Fin.suc (Fin.suc Fin.zero)
encodeDigit J.d3 = Fin.suc (Fin.suc (Fin.suc Fin.zero))
encodeDigit J.d4 = Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
encodeDigit J.d5 = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
encodeDigit J.d6 = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
encodeDigit J.d7 = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
encodeDigit J.d8 = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))
encodeDigit J.d9 = Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))

decodeDigit : Fin.Fin 10 → J.DecimalDigit
decodeDigit Fin.zero = J.d0
decodeDigit (Fin.suc Fin.zero) = J.d1
decodeDigit (Fin.suc (Fin.suc Fin.zero)) = J.d2
decodeDigit (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = J.d3
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = J.d4
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = J.d5
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = J.d6
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) = J.d7
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) = J.d8
decodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))) = J.d9

decodeEncodeDigit : (digit : J.DecimalDigit) →
  decodeDigit (encodeDigit digit) ≡ digit
decodeEncodeDigit J.d0 = refl
decodeEncodeDigit J.d1 = refl
decodeEncodeDigit J.d2 = refl
decodeEncodeDigit J.d3 = refl
decodeEncodeDigit J.d4 = refl
decodeEncodeDigit J.d5 = refl
decodeEncodeDigit J.d6 = refl
decodeEncodeDigit J.d7 = refl
decodeEncodeDigit J.d8 = refl
decodeEncodeDigit J.d9 = refl

encodeDecodeDigit : (digit : Fin.Fin 10) →
  encodeDigit (decodeDigit digit) ≡ digit
encodeDecodeDigit Fin.zero = refl
encodeDecodeDigit (Fin.suc Fin.zero) = refl
encodeDecodeDigit (Fin.suc (Fin.suc Fin.zero)) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc Fin.zero))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))) = refl
encodeDecodeDigit (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))) = refl

------------------------------------------------------------------------
-- Exact address <-> residue-representative equivalence at every finite level.
--
-- The newest digit is the quotient coordinate in
--   Fin (10 * 10^r) <-> Fin 10 x Fin (10^r),
-- so removing it is exactly remainder modulo 10^r.
------------------------------------------------------------------------

Residue10 : Nat → Set
Residue10 r = Fin.Fin (10 ^ r)

encodeResidue : ∀ {r} → J.DecimalAddress r → Residue10 r
encodeResidue {zero} J.root = Fin.zero
encodeResidue {suc r} (J.extend address digit) =
  Fin.combine (encodeDigit digit) (encodeResidue address)

decodeResidue : ∀ {r} → Residue10 r → J.DecimalAddress r
decodeResidue {zero} Fin.zero = J.root
decodeResidue {suc r} residue with Fin.remQuot (10 ^ r) residue
... | digit , lower = J.extend (decodeResidue lower) (decodeDigit digit)

decodeEncodeResidue :
  ∀ {r} (address : J.DecimalAddress r) →
  decodeResidue (encodeResidue address) ≡ address
decodeEncodeResidue J.root = refl
decodeEncodeResidue {suc r} (J.extend address digit)
  rewrite FinP.remQuot-combine (encodeDigit digit) (encodeResidue address)
        | decodeEncodeResidue address
        | decodeEncodeDigit digit = refl

encodeDecodeResidue :
  ∀ {r} (residue : Residue10 r) →
  encodeResidue (decodeResidue residue) ≡ residue
encodeDecodeResidue {zero} Fin.zero = refl
encodeDecodeResidue {suc r} residue with Fin.remQuot (10 ^ r) residue in eq
... | digit , lower =
  trans
    (cong₂ Fin.combine
      (encodeDecodeDigit digit)
      (encodeDecodeResidue lower))
    (trans
      (cong
        (λ pair → Fin.combine (proj₁ pair) (proj₂ pair))
        (sym eq))
      (FinP.combine-remQuot (10 ^ r) residue))

reduceResidue : ∀ {r} → Residue10 (suc r) → Residue10 r
reduceResidue {r} = Fin.remainder (10 ^ r)

encodePrefixCompatible :
  ∀ {r} (fine : J.DecimalAddress (suc r)) →
  encodeResidue (J.prefix fine) ≡ reduceResidue (encodeResidue fine)
encodePrefixCompatible {r} (J.extend address digit) =
  sym
    (cong proj₂
      (FinP.remQuot-combine
        (encodeDigit digit)
        (encodeResidue address)))

record DecimalResidueEquivalence (r : Nat) : Set where
  constructor decimalResidueEquivalence
  field
    forward : J.DecimalAddress r → Residue10 r
    backward : Residue10 r → J.DecimalAddress r
    backwardForward : (x : J.DecimalAddress r) → backward (forward x) ≡ x
    forwardBackward : (x : Residue10 r) → forward (backward x) ≡ x

canonicalDecimalResidueEquivalence :
  (r : Nat) → DecimalResidueEquivalence r
canonicalDecimalResidueEquivalence r =
  decimalResidueEquivalence
    encodeResidue
    decodeResidue
    decodeEncodeResidue
    encodeDecodeResidue

record DecimalResidueClaimScope : Set where
  constructor decimalResidueClaimScope
  field
    finiteSetEquivalenceConstructed : Bool
    finiteSetEquivalenceConstructedIsTrue :
      finiteSetEquivalenceConstructed ≡ true

    truncationReductionCompatibilityConstructed : Bool
    truncationReductionCompatibilityConstructedIsTrue :
      truncationReductionCompatibilityConstructed ≡ true

    ringIsomorphismInferredFromCardinalityAlone : Bool
    ringIsomorphismInferredFromCardinalityAloneIsFalse :
      ringIsomorphismInferredFromCardinalityAlone ≡ false

canonicalDecimalResidueClaimScope : DecimalResidueClaimScope
canonicalDecimalResidueClaimScope =
  decimalResidueClaimScope true refl true refl false refl
