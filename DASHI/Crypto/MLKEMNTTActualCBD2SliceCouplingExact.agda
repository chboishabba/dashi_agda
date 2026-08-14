module DASHI.Crypto.MLKEMNTTActualCBD2SliceCouplingExact where

------------------------------------------------------------------------
-- SOURCE-FAITHFUL TWO-COEFFICIENT CBD2 SLICE OF THE FIPS-203 NTT PRIOR
--
-- Primary source:
-- National Institute of Standards and Technology,
-- "Module-Lattice-Based Key-Encapsulation Mechanism Standard", FIPS 203,
-- 2024. DOI: 10.6028/NIST.FIPS.203.
--
-- FIPS 203 fixes q=3329 and zeta=17, with zeta^128 = -1.  In the quadratic
-- factor formula, residue i=0 uses gamma0=zeta=17.  For i=1,
-- BitRev7(1)=64, so gamma1=zeta^129=-zeta=3312 mod 3329.
--
-- Restrict one CBD2 polynomial to two even source coefficients and fix all
-- others to zero.  Writing centered digits x,y in {-2,-1,0,1,2}, the constant
-- parts of these first two quadratic residues are
--
--   u = x + 17 y,
--   v = x - 17 y              (over the centered integer lift; no wrap occurs).
--
-- After harmless translations into Nat, we use
--   U = xd + 17 yd,
--   V = xd + 17 (4-yd),
-- where xd,yd are the centered digits shifted into {0,1,2,3,4}.
--
-- U=0 is locally reachable and V=0 is locally reachable, but the crossed local
-- pair (U,V)=(0,0) is not in the joint image.  Thus an actual FIPS-constant
-- NTT slice already witnesses non-Cartesian transported CBD support.
--
-- This is a support-geometry theorem, not an ML-KEM attack or an independence
-- theorem for the full 256-coordinate distribution.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; subst)

q : Nat
q = 3329

zeta : Nat
zeta = 17

gamma0 : Nat
gamma0 = 17

gamma1 : Nat
gamma1 = 3312

gamma1IsMinusZetaModQ : gamma1 + zeta ≡ q
gamma1IsMinusZetaModQ = refl

data CBD2Digit : Set where
  d0 d1 d2 d3 d4 : CBD2Digit

digit : CBD2Digit → Nat
digit d0 = 0
digit d1 = 1
digit d2 = 2
digit d3 = 3
digit d4 = 4

reverseDigit : CBD2Digit → CBD2Digit
reverseDigit d0 = d4
reverseDigit d1 = d3
reverseDigit d2 = d2
reverseDigit d3 = d1
reverseDigit d4 = d0

record SourceSlice : Set where
  constructor sourceSlice
  field
    x y : CBD2Digit
open SourceSlice public

encodeU : SourceSlice → Nat
encodeU source = digit (x source) + 17 * digit (y source)

encodeV : SourceSlice → Nat
encodeV source = digit (x source) + 17 * digit (reverseDigit (y source))

s00 : SourceSlice
s00 = sourceSlice d0 d0

s04 : SourceSlice
s04 = sourceSlice d0 d4

uZeroReachable : encodeU s00 ≡ 0
uZeroReachable = refl

vZeroReachable : encodeV s04 ≡ 0
vZeroReachable = refl

------------------------------------------------------------------------
-- U=0 uniquely identifies the source slice d0,d0 inside this 5x5 support.
------------------------------------------------------------------------

uZeroOnlyS00 : ∀ source → encodeU source ≡ 0 → source ≡ s00
uZeroOnlyS00 (sourceSlice d0 d0) refl = refl
uZeroOnlyS00 (sourceSlice d1 d0) ()
uZeroOnlyS00 (sourceSlice d2 d0) ()
uZeroOnlyS00 (sourceSlice d3 d0) ()
uZeroOnlyS00 (sourceSlice d4 d0) ()
uZeroOnlyS00 (sourceSlice d0 d1) ()
uZeroOnlyS00 (sourceSlice d1 d1) ()
uZeroOnlyS00 (sourceSlice d2 d1) ()
uZeroOnlyS00 (sourceSlice d3 d1) ()
uZeroOnlyS00 (sourceSlice d4 d1) ()
uZeroOnlyS00 (sourceSlice d0 d2) ()
uZeroOnlyS00 (sourceSlice d1 d2) ()
uZeroOnlyS00 (sourceSlice d2 d2) ()
uZeroOnlyS00 (sourceSlice d3 d2) ()
uZeroOnlyS00 (sourceSlice d4 d2) ()
uZeroOnlyS00 (sourceSlice d0 d3) ()
uZeroOnlyS00 (sourceSlice d1 d3) ()
uZeroOnlyS00 (sourceSlice d2 d3) ()
uZeroOnlyS00 (sourceSlice d3 d3) ()
uZeroOnlyS00 (sourceSlice d4 d3) ()
uZeroOnlyS00 (sourceSlice d0 d4) ()
uZeroOnlyS00 (sourceSlice d1 d4) ()
uZeroOnlyS00 (sourceSlice d2 d4) ()
uZeroOnlyS00 (sourceSlice d3 d4) ()
uZeroOnlyS00 (sourceSlice d4 d4) ()

record TargetSlice : Set where
  constructor targetSlice
  field
    U V : Nat
open TargetSlice public

jointEncode : SourceSlice → TargetSlice
jointEncode source = targetSlice (encodeU source) (encodeV source)

crossedMarginalPair : TargetSlice
crossedMarginalPair = targetSlice 0 0

sixtyEightNotZero : 68 ≡ 0 → ⊥
sixtyEightNotZero ()

crossedMarginalsNotJointlyReachable :
  ∀ source → jointEncode source ≡ crossedMarginalPair → ⊥
crossedMarginalsNotJointlyReachable source equality =
  sixtyEightNotZero vImpossible
  where
  uEquality : encodeU source ≡ 0
  uEquality = cong U equality

  sourceIs00 : source ≡ s00
  sourceIs00 = uZeroOnlyS00 source uEquality

  vEquality : encodeV source ≡ 0
  vEquality = cong V equality

  vImpossible : encodeV s00 ≡ 0
  vImpossible = subst (λ selected → encodeV selected ≡ 0) sourceIs00 vEquality

------------------------------------------------------------------------
-- The two local marginal values exist independently, while their product point
-- does not belong to the transported joint support.
------------------------------------------------------------------------

record NonCartesianSupportWitness : Set where
  constructor nonCartesianSupportWitness
  field
    localUReachable : Set
    localVReachable : Set
    crossedPairImpossible : Set

nonCartesianCBD2NTTSlice : NonCartesianSupportWitness
nonCartesianCBD2NTTSlice =
  nonCartesianSupportWitness
    (encodeU s00 ≡ 0)
    (encodeV s04 ≡ 0)
    ((source : SourceSlice) → jointEncode source ≡ crossedMarginalPair → ⊥)
