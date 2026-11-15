module DASHI.Physics.YangMills.YMClaySUNFinitePairedFiberCodecExact where

------------------------------------------------------------------------
-- P0.E finite COORDINATE source: exact SU(N) paired-link fiber codec.
--
-- Native group multiplication W=U*V has a GLOBAL inverse fiber
-- description (U,W) -> (U, U^-1*W). Unlike the proposed
-- sqrt(W)*exp(+-xi) local chart, this is EXACT and uses no Lie-group
-- logarithm, Faddeev-Popov determinant or Jacobian approximation.
--
-- Proved for every finite number n of independent *coordinate pairs*
-- on the original CertifiedSUNMatrixTheory (including n=64).
-- This is a bijection of finite link VECTORS, not yet the 1024-bond
-- original geometry permutation and not an interacting Gibbs estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; trans; sym)
import DASHI.Physics.YangMills.CompactLieGroupCore as Group
import DASHI.Physics.YangMills.SUNMatrixCarrier as SUN

module _
    {Matrix Complex : Set} {N : Nat}
    (theory : SUN.CertifiedSUNMatrixTheory N Matrix Complex)
  where

  Link : Set
  Link = SUN.SUNMatrixElement theory

  PairVector : Nat → Set
  PairVector n = Vec (Link × Link) n

  product : Link → Link → Link
  product = SUN.sunMultiply theory

  inverse : Link → Link
  inverse = SUN.sunInverse theory

  originalSUNGroup : Group.Group Link
  originalSUNGroup = SUN.sunMatrixGroup theory

  nativeInverseLeftCancellation :
    (U V : Link) → product (inverse U) (product U V) ≡ V
  nativeInverseLeftCancellation U V =
    trans
      (sym (Group.multiplyAssociative originalSUNGroup (inverse U) U V))
      (trans
        (cong (λ X → product X V)
          (Group.inverseLeft originalSUNGroup U))
        (Group.identityLeft originalSUNGroup V))

  nativeInverseRightCancellation :
    (U W : Link) → product U (product (inverse U) W) ≡ W
  nativeInverseRightCancellation U W =
    trans
      (sym (Group.multiplyAssociative originalSUNGroup U (inverse U) W))
      (trans
        (cong (λ X → product X W)
          (Group.inverseRight originalSUNGroup U))
        (Group.identityLeft originalSUNGroup W))

  nativeBlockedProducts : ∀ {n} → PairVector n → Vec Link n
  nativeBlockedProducts [] = []
  nativeBlockedProducts ((U , V) ∷ rest) =
    product U V ∷ nativeBlockedProducts rest

  nativeFiberCoordinates : ∀ {n} → PairVector n → Vec Link n
  nativeFiberCoordinates [] = []
  nativeFiberCoordinates ((U , V) ∷ rest) =
    U ∷ nativeFiberCoordinates rest

  nativeReconstructFinePairs :
    ∀ {n} → Vec Link n → Vec Link n → PairVector n
  nativeReconstructFinePairs [] [] = []
  nativeReconstructFinePairs (U ∷ fiber) (W ∷ coarse) =
    (U , product (inverse U) W) ∷
      nativeReconstructFinePairs fiber coarse

  originalFiniteFiberCodecBlockedRoundTrip :
    ∀ {n} (fiber coarse : Vec Link n) →
    nativeBlockedProducts (nativeReconstructFinePairs fiber coarse)
    ≡ coarse
  originalFiniteFiberCodecBlockedRoundTrip [] [] = refl
  originalFiniteFiberCodecBlockedRoundTrip
      (U ∷ fiber) (W ∷ coarse) =
    cong₂ _∷_
      (nativeInverseRightCancellation U W)
      (originalFiniteFiberCodecBlockedRoundTrip fiber coarse)

  originalFiniteFiberCodecFineRoundTrip :
    ∀ {n} (fine : PairVector n) →
    nativeReconstructFinePairs
      (nativeFiberCoordinates fine)
      (nativeBlockedProducts fine)
    ≡ fine
  originalFiniteFiberCodecFineRoundTrip [] = refl
  originalFiniteFiberCodecFineRoundTrip ((U , V) ∷ rest) =
    cong₂ (λ recovered tail → (U , recovered) ∷ tail)
      (nativeInverseLeftCancellation U V)
      (originalFiniteFiberCodecFineRoundTrip rest)

  -- These TWO genuine round trips pay the global finite-pair
  -- coordinate Jacobian replacement exactly: native Haar invariance
  -- (proved separately) then supplies the measure transformation.
  originalR445Candidate64PairBlockedRoundTrip :
    (fiber coarse : Vec Link 64) →
    nativeBlockedProducts (nativeReconstructFinePairs fiber coarse)
    ≡ coarse
  originalR445Candidate64PairBlockedRoundTrip =
    originalFiniteFiberCodecBlockedRoundTrip

  originalR445Candidate64PairFineRoundTrip :
    (fine : PairVector 64) →
    nativeReconstructFinePairs
      (nativeFiberCoordinates fine)
      (nativeBlockedProducts fine)
    ≡ fine
  originalR445Candidate64PairFineRoundTrip =
    originalFiniteFiberCodecFineRoundTrip
