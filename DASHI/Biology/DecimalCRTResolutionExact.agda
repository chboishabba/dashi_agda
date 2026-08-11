module DASHI.Biology.DecimalCRTResolutionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Fernando Q. Gouvea, "p-adic Numbers: An Introduction", 2nd ed.,
-- Springer, 1997. DOI: 10.1007/978-3-642-59058-0.
--
-- DASHI CONTRIBUTION
--
-- Separate three statements that are easy to conflate:
--   1. 10^r = 2^r * 5^r (cardinality arithmetic);
--   2. a finite-set bijection Fin(10^r) <-> Fin(2^r) x Fin(5^r);
--   3. the stronger arithmetic Chinese-remainder equivalence, coherent with
--      the residue-reduction maps.
--
-- (1) and (2) are constructed below.  For (3), the actual forward arithmetic
-- residue map x |-> (x mod 2^r, x mod 5^r) is constructed explicitly, and a
-- CoherentCRTSystem must provide its inverse plus the reduction-coherence laws.
-- This is intentionally stronger than a same-cardinality bijection.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Nat.Properties as NatP
import Data.Fin.Base as Fin
import Data.Fin.Properties as FinP

------------------------------------------------------------------------
-- Residue representative carriers and reduction maps.
------------------------------------------------------------------------

Residue : Nat → Nat → Set
Residue base r = Fin.Fin (base ^ r)

reduceResidue :
  (base : Nat) {r : Nat} → Residue base (suc r) → Residue base r
reduceResidue base {r} = Fin.remainder (base ^ r)

Residue10 Residue2 Residue5 : Nat → Set
Residue10 = Residue 10
Residue2 = Residue 2
Residue5 = Residue 5

ProductResidue25 : Nat → Set
ProductResidue25 r = Residue2 r × Residue5 r

reduceProduct25 :
  ∀ {r} → ProductResidue25 (suc r) → ProductResidue25 r
reduceProduct25 (two , five) =
  reduceResidue 2 two , reduceResidue 5 five

------------------------------------------------------------------------
-- Exact cardinal factorization at every finite level.
------------------------------------------------------------------------

tenPowerFactor : (r : Nat) → 10 ^ r ≡ 2 ^ r * 5 ^ r
tenPowerFactor r = NatP.^-distribʳ-* r 2 5

tenPowerFactorSwapped : (r : Nat) → 10 ^ r ≡ 5 ^ r * 2 ^ r
tenPowerFactorSwapped r =
  trans (tenPowerFactor r) (NatP.*-comm (2 ^ r) (5 ^ r))

cardinalFactorForward :
  (r : Nat) → Residue10 r → ProductResidue25 r
cardinalFactorForward r residue =
  Fin.remQuot (5 ^ r) (Fin.cast (tenPowerFactor r) residue)

cardinalFactorBackward :
  (r : Nat) → ProductResidue25 r → Residue10 r
cardinalFactorBackward r (two , five) =
  Fin.cast (sym (tenPowerFactor r)) (Fin.combine two five)

cardinalFactorBackwardForward :
  (r : Nat) (x : Residue10 r) →
  cardinalFactorBackward r (cardinalFactorForward r x) ≡ x
cardinalFactorBackwardForward r x =
  trans
    (cong
      (Fin.cast (sym (tenPowerFactor r)))
      (FinP.combine-remQuot
        (5 ^ r)
        (Fin.cast (tenPowerFactor r) x)))
    (FinP.cast-involutive
      (sym (tenPowerFactor r))
      (tenPowerFactor r)
      x)

cardinalFactorForwardBackward :
  (r : Nat) (pair : ProductResidue25 r) →
  cardinalFactorForward r (cardinalFactorBackward r pair) ≡ pair
cardinalFactorForwardBackward r (two , five) =
  trans
    (cong
      (Fin.remQuot (5 ^ r))
      (FinP.cast-involutive
        (tenPowerFactor r)
        (sym (tenPowerFactor r))
        (Fin.combine two five)))
    (FinP.remQuot-combine two five)

record FiniteCardinalFactorization (r : Nat) : Set where
  constructor finiteCardinalFactorization
  field
    forward : Residue10 r → ProductResidue25 r
    backward : ProductResidue25 r → Residue10 r
    backwardForward : (x : Residue10 r) → backward (forward x) ≡ x
    forwardBackward : (x : ProductResidue25 r) → forward (backward x) ≡ x

canonicalFiniteCardinalFactorization :
  (r : Nat) → FiniteCardinalFactorization r
canonicalFiniteCardinalFactorization r =
  finiteCardinalFactorization
    (cardinalFactorForward r)
    (cardinalFactorBackward r)
    (cardinalFactorBackwardForward r)
    (cardinalFactorForwardBackward r)

------------------------------------------------------------------------
-- Canonical arithmetic residue projections.
--
-- These maps really are the two remainder coordinates: the casts expose
-- 10^r as a multiple of the target modulus and `Fin.remainder` performs the
-- canonical finite remainder map.
------------------------------------------------------------------------

canonicalResidue2 :
  (r : Nat) → Residue10 r → Residue2 r
canonicalResidue2 r x =
  Fin.remainder (2 ^ r) (Fin.cast (tenPowerFactorSwapped r) x)

canonicalResidue5 :
  (r : Nat) → Residue10 r → Residue5 r
canonicalResidue5 r x =
  Fin.remainder (5 ^ r) (Fin.cast (tenPowerFactor r) x)

canonicalCRTForward :
  (r : Nat) → Residue10 r → ProductResidue25 r
canonicalCRTForward r x =
  canonicalResidue2 r x , canonicalResidue5 r x

------------------------------------------------------------------------
-- Arithmetic CRT data is deliberately a stronger type.
--
-- A genuine stage must use the canonical arithmetic residue map, provide an
-- inverse to it, and a coherent system must additionally commute with the
-- canonical residue reductions.  Therefore an arbitrary mixed-radix cardinal
-- bijection cannot inhabit this type unless it is proved equal to the actual
-- residue-pair map.
------------------------------------------------------------------------

record CRTStage (r : Nat) : Set where
  constructor crtStage
  field
    crtForward : Residue10 r → ProductResidue25 r
    crtForwardIsCanonicalResidues :
      (x : Residue10 r) → crtForward x ≡ canonicalCRTForward r x

    crtBackward : ProductResidue25 r → Residue10 r
    crtBackwardForward :
      (x : Residue10 r) → crtBackward (crtForward x) ≡ x
    crtForwardBackward :
      (x : ProductResidue25 r) → crtForward (crtBackward x) ≡ x

open CRTStage public

record CoherentCRTSystem : Set₁ where
  constructor coherentCRTSystem
  field
    stage : (r : Nat) → CRTStage r

    forwardReductionCommutes :
      ∀ {r} (x : Residue10 (suc r)) →
      crtForward (stage r) (reduceResidue 10 x)
      ≡ reduceProduct25 (crtForward (stage (suc r)) x)

    backwardReductionCommutes :
      ∀ {r} (x : ProductResidue25 (suc r)) →
      crtBackward (stage r) (reduceProduct25 x)
      ≡ reduceResidue 10 (crtBackward (stage (suc r)) x)

open CoherentCRTSystem public

record DecimalCRTClaimScope : Set where
  constructor decimalCRTClaimScope
  field
    tenPowerCardinalityFactorizationConstructed : Bool
    tenPowerCardinalityFactorizationConstructedIsTrue :
      tenPowerCardinalityFactorizationConstructed ≡ true

    finiteSetBijectionConstructed : Bool
    finiteSetBijectionConstructedIsTrue :
      finiteSetBijectionConstructed ≡ true

    canonicalArithmeticForwardResiduesConstructed : Bool
    canonicalArithmeticForwardResiduesConstructedIsTrue :
      canonicalArithmeticForwardResiduesConstructed ≡ true

    arbitraryCardinalBijectionCalledArithmeticCRT : Bool
    arbitraryCardinalBijectionCalledArithmeticCRTIsFalse :
      arbitraryCardinalBijectionCalledArithmeticCRT ≡ false

    coherentArithmeticCRTRequiresExplicitInverseAndLaws : Bool
    coherentArithmeticCRTRequiresExplicitInverseAndLawsIsTrue :
      coherentArithmeticCRTRequiresExplicitInverseAndLaws ≡ true

canonicalDecimalCRTClaimScope : DecimalCRTClaimScope
canonicalDecimalCRTClaimScope =
  decimalCRTClaimScope
    true refl
    true refl
    true refl
    false refl
    true refl
