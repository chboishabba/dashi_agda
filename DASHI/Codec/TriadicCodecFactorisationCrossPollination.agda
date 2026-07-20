module DASHI.Codec.TriadicCodecFactorisationCrossPollination where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Sigma using (_,_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos; inv)
import DASHI.Algebra.TritSupportSignFactor as Canonical
import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.Codec.TriadicPAdicCodec as PAdic

------------------------------------------------------------------------
-- Canonicalise the three finite support/sign presentations already present
-- in the repository.
--
-- DASHI.Algebra.TritSupportSignFactor is the theorem owner.  The codec-local
-- presentations remain useful APIs, but are connected here by exact
-- isomorphisms rather than treated as independent ternary semantics.
------------------------------------------------------------------------

pAdic→canonical : PAdic.FoldedTrit → Canonical.SupportSign
pAdic→canonical PAdic.zeroFold = Canonical.inactive , Canonical.tt
pAdic→canonical (PAdic.signed PAdic.minus) =
  Canonical.active , Canonical.negative
pAdic→canonical (PAdic.signed PAdic.plus) =
  Canonical.active , Canonical.positive

canonical→pAdic : Canonical.SupportSign → PAdic.FoldedTrit
canonical→pAdic (Canonical.inactive , Canonical.tt) = PAdic.zeroFold
canonical→pAdic (Canonical.active , Canonical.negative) =
  PAdic.signed PAdic.minus
canonical→pAdic (Canonical.active , Canonical.positive) =
  PAdic.signed PAdic.plus

pAdic-canonical-roundtrip :
  (x : PAdic.FoldedTrit) →
  canonical→pAdic (pAdic→canonical x) ≡ x
pAdic-canonical-roundtrip PAdic.zeroFold = refl
pAdic-canonical-roundtrip (PAdic.signed PAdic.minus) = refl
pAdic-canonical-roundtrip (PAdic.signed PAdic.plus) = refl

canonical-pAdic-roundtrip :
  (x : Canonical.SupportSign) →
  pAdic→canonical (canonical→pAdic x) ≡ x
canonical-pAdic-roundtrip (Canonical.inactive , Canonical.tt) = refl
canonical-pAdic-roundtrip (Canonical.active , Canonical.negative) = refl
canonical-pAdic-roundtrip (Canonical.active , Canonical.positive) = refl

pAdic-fold-is-canonical :
  (t : Trit) →
  pAdic→canonical (PAdic.foldTrit t) ≡ Canonical.encode t
pAdic-fold-is-canonical neg = refl
pAdic-fold-is-canonical zer = refl
pAdic-fold-is-canonical pos = refl

maskSign→canonical : MaskSign.FactorizedTrit → Canonical.SupportSign
maskSign→canonical MaskSign.inactive = Canonical.inactive , Canonical.tt
maskSign→canonical (MaskSign.active MaskSign.negative) =
  Canonical.active , Canonical.negative
maskSign→canonical (MaskSign.active MaskSign.positive) =
  Canonical.active , Canonical.positive

canonical→maskSign : Canonical.SupportSign → MaskSign.FactorizedTrit
canonical→maskSign (Canonical.inactive , Canonical.tt) = MaskSign.inactive
canonical→maskSign (Canonical.active , Canonical.negative) =
  MaskSign.active MaskSign.negative
canonical→maskSign (Canonical.active , Canonical.positive) =
  MaskSign.active MaskSign.positive

maskSign-canonical-roundtrip :
  (x : MaskSign.FactorizedTrit) →
  canonical→maskSign (maskSign→canonical x) ≡ x
maskSign-canonical-roundtrip MaskSign.inactive = refl
maskSign-canonical-roundtrip (MaskSign.active MaskSign.negative) = refl
maskSign-canonical-roundtrip (MaskSign.active MaskSign.positive) = refl

canonical-maskSign-roundtrip :
  (x : Canonical.SupportSign) →
  maskSign→canonical (canonical→maskSign x) ≡ x
canonical-maskSign-roundtrip (Canonical.inactive , Canonical.tt) = refl
canonical-maskSign-roundtrip (Canonical.active , Canonical.negative) = refl
canonical-maskSign-roundtrip (Canonical.active , Canonical.positive) = refl

maskSign-encode-is-canonical :
  (t : Trit) →
  maskSign→canonical (MaskSign.encodeTrit t) ≡ Canonical.encode t
maskSign-encode-is-canonical neg = refl
maskSign-encode-is-canonical zer = refl
maskSign-encode-is-canonical pos = refl

------------------------------------------------------------------------
-- Support is the involution quotient; sign is the odd fibre.
------------------------------------------------------------------------

support-inversion-invariant :
  (t : Trit) →
  PAdic.support (inv t) ≡ PAdic.support t
support-inversion-invariant neg = refl
support-inversion-invariant zer = refl
support-inversion-invariant pos = refl

------------------------------------------------------------------------
-- Exact raw support/sign payload accounting for ordered trit triples.
--
-- Every position contributes one support bit.  Every active position contributes
-- one gated sign bit.  Thus a triple with k active trits costs 3 + k raw bits.
-- This is a finite representation theorem, not an entropy or rANS rate theorem.
------------------------------------------------------------------------

three : Nat
three = suc (suc (suc zero))

rawSupportSignBits : MaskSign.Triple Trit → Nat
rawSupportSignBits u = three + MaskSign.activeCount (MaskSign.encodeTriple u)

allZeroRawBits :
  rawSupportSignBits (MaskSign.triple zer zer zer) ≡ 3
allZeroRawBits = refl

sparseRawBits :
  rawSupportSignBits (MaskSign.triple neg zer pos) ≡ 5
sparseRawBits = refl

allActiveRawBits :
  rawSupportSignBits (MaskSign.triple neg pos neg) ≡ 6
allActiveRawBits = refl

------------------------------------------------------------------------
-- Integration and claim boundary.
------------------------------------------------------------------------

record FactorisationCrossPollinationBoundary : Set where
  constructor boundary
  field
    canonicalOwnerReused : Bool
    pAdicPresentationExactlyEquivalent : Bool
    maskSignPresentationExactlyEquivalent : Bool
    supportIsInvolutionInvariant : Bool
    rawNPlusKLawCheckedForTriples : Bool
    entropyOptimalityProvedHere : Bool
    rANSMachineCorrectnessProvedHere : Bool
    empiricalCodecSuperiorityProvedHere : Bool

canonicalFactorisationCrossPollinationBoundary :
  FactorisationCrossPollinationBoundary
canonicalFactorisationCrossPollinationBoundary =
  boundary true true true true true false false false
