module DASHI.Biology.Physical.C3DirectGroupConvolutionExact where

------------------------------------------------------------------------
-- Direct group-sum convolution on C3 and its exact cyclotomic DFT theorem.
-- This closes the non-spectral-definition case in one dimension and supplies
-- the recursive product convolution used by the C3^3 lane.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Rational.Tactic.RingSolver using (solve-∀)

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as F

infixl 6 _+T_
infixl 7 _*T_

_+T_ : F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3
_+T_ = F.zipTriple F._+C_

_*T_ : F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3
_*T_ = F.zipTriple F._*C_

cyclicConvolution1 :
  F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3
cyclicConvolution1
  (F.triple a0 a1 a2)
  (F.triple b0 b1 b2) =
  F.triple
    (a0 F.*C b0 F.+C a1 F.*C b2 F.+C a2 F.*C b1)
    (a0 F.*C b1 F.+C a1 F.*C b0 F.+C a2 F.*C b2)
    (a0 F.*C b2 F.+C a1 F.*C b1 F.+C a2 F.*C b0)

forward1Additive : (f g : F.Triple F.Cyclotomic3) →
  F.forward1 (f +T g) ≡ F.forward1 f +T F.forward1 g
forward1Additive
  (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1))
  (F.triple (F.cyc d0 d1) (F.cyc e0 e1) (F.cyc f0 f1)) =
  F.triple-ext
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)

c3DirectConvolutionTheorem : (f g : F.Triple F.Cyclotomic3) →
  F.forward1 (cyclicConvolution1 f g)
  ≡ F.zipTriple F._*C_ (F.forward1 f) (F.forward1 g)
c3DirectConvolutionTheorem
  (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1))
  (F.triple (F.cyc d0 d1) (F.cyc e0 e1) (F.cyc f0 f1)) =
  F.triple-ext
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)

------------------------------------------------------------------------
-- Delta identity for the direct group convolution.
------------------------------------------------------------------------

delta0 : F.Triple F.Cyclotomic3
delta0 = F.triple F.oneC F.zeroC F.zeroC

convolutionDeltaLeftIdentity : (f : F.Triple F.Cyclotomic3) →
  cyclicConvolution1 delta0 f ≡ f
convolutionDeltaLeftIdentity
  (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1)) =
  F.triple-ext
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)

convolutionDeltaRightIdentity : (f : F.Triple F.Cyclotomic3) →
  cyclicConvolution1 f delta0 ≡ f
convolutionDeltaRightIdentity
  (F.triple (F.cyc a0 a1) (F.cyc b0 b1) (F.cyc c0 c1)) =
  F.triple-ext
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)
    (F.cyc-ext solve-∀ solve-∀)
