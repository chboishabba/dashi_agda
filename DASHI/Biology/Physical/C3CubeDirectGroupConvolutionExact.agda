module DASHI.Biology.Physical.C3CubeDirectGroupConvolutionExact where

------------------------------------------------------------------------
-- Ordinary product-group convolution on C3^3 and exact Fourier
-- diagonalisation.  The proof is tensorial: the one-dimensional direct
-- convolution theorem is transported successively across z, y and x axes.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as F
import DASHI.Biology.Physical.C3DirectGroupConvolutionExact as C1

------------------------------------------------------------------------
-- Generic three-cycle convolution over an arbitrary additive/multiplicative
-- coefficient carrier.
------------------------------------------------------------------------

cyclicWith : ∀ {A : Set} →
  (A → A → A) → (A → A → A) → F.Triple A → F.Triple A → F.Triple A
cyclicWith add mul (F.triple a0 a1 a2) (F.triple b0 b1 b2) =
  F.triple
    (add (add (mul a0 b0) (mul a1 b2)) (mul a2 b1))
    (add (add (mul a0 b1) (mul a1 b0)) (mul a2 b2))
    (add (add (mul a0 b2) (mul a1 b1)) (mul a2 b0))

mapCyclicHom : ∀ {A B : Set}
  (addA mulA : A → A → A)
  (addB mulB : B → B → B)
  (h : A → B) →
  ((x y : A) → h (addA x y) ≡ addB (h x) (h y)) →
  ((x y : A) → h (mulA x y) ≡ mulB (h x) (h y)) →
  (left right : F.Triple A) →
  F.mapTriple h (cyclicWith addA mulA left right)
  ≡ cyclicWith addB mulB (F.mapTriple h left) (F.mapTriple h right)
mapCyclicHom addA mulA addB mulB h hAdd hMul
  (F.triple a0 a1 a2) (F.triple b0 b1 b2)
  rewrite hAdd (addA (mulA a0 b0) (mulA a1 b2)) (mulA a2 b1)
        | hAdd (mulA a0 b0) (mulA a1 b2)
        | hMul a0 b0 | hMul a1 b2 | hMul a2 b1
        | hAdd (addA (mulA a0 b1) (mulA a1 b0)) (mulA a2 b2)
        | hAdd (mulA a0 b1) (mulA a1 b0)
        | hMul a0 b1 | hMul a1 b0 | hMul a2 b2
        | hAdd (addA (mulA a0 b2) (mulA a1 b1)) (mulA a2 b0)
        | hAdd (mulA a0 b2) (mulA a1 b1)
        | hMul a0 b2 | hMul a1 b1 | hMul a2 b0 = refl

------------------------------------------------------------------------
-- Pointwise coefficient algebras.
------------------------------------------------------------------------

add1 : F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3
add1 = F.zipTriple F._+C_

pointwise1 : F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3 → F.Triple F.Cyclotomic3
pointwise1 = F.zipTriple F._*C_

add2 : F.Triple (F.Triple F.Cyclotomic3) →
       F.Triple (F.Triple F.Cyclotomic3) →
       F.Triple (F.Triple F.Cyclotomic3)
add2 = F.zipTriple add1

pointwise2 : F.Triple (F.Triple F.Cyclotomic3) →
             F.Triple (F.Triple F.Cyclotomic3) →
             F.Triple (F.Triple F.Cyclotomic3)
pointwise2 = F.zipTriple pointwise1

pointwise3 : F.CubeSignal → F.CubeSignal → F.CubeSignal
pointwise3 = F.zipTriple pointwise2

------------------------------------------------------------------------
-- Direct C3^2 and C3^3 group convolution, recursively using group-product
-- convolution rather than the Fourier transform.
------------------------------------------------------------------------

convolution2 :
  F.Triple (F.Triple F.Cyclotomic3) →
  F.Triple (F.Triple F.Cyclotomic3) →
  F.Triple (F.Triple F.Cyclotomic3)
convolution2 = cyclicWith add1 C1.cyclicConvolution1

convolution3 : F.CubeSignal → F.CubeSignal → F.CubeSignal
convolution3 = cyclicWith add2 convolution2

------------------------------------------------------------------------
-- z transform maps coefficient convolution to pointwise multiplication.
------------------------------------------------------------------------

zMapsConvolution2 : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.mapTriple F.forward1 (convolution2 f g)
  ≡ cyclicWith add1 pointwise1
      (F.mapTriple F.forward1 f)
      (F.mapTriple F.forward1 g)
zMapsConvolution2 =
  mapCyclicHom add1 C1.cyclicConvolution1 add1 pointwise1
    F.forward1 C1.forward1Additive C1.c3DirectConvolutionTheorem

------------------------------------------------------------------------
-- y transform diagonalizes an outer cyclic convolution whose coefficients
-- already multiply pointwise in z.
------------------------------------------------------------------------

transposeCyclicPointwise :
  (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.transpose2 (cyclicWith add1 pointwise1 f g)
  ≡ F.zipTriple C1.cyclicConvolution1 (F.transpose2 f) (F.transpose2 g)
transposeCyclicPointwise
  (F.triple (F.triple a00 a01 a02) (F.triple a10 a11 a12) (F.triple a20 a21 a22))
  (F.triple (F.triple b00 b01 b02) (F.triple b10 b11 b12) (F.triple b20 b21 b22)) = refl

mapForwardOverConvolutionColumns :
  (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.mapTriple F.forward1 (F.zipTriple C1.cyclicConvolution1 f g)
  ≡ F.zipTriple pointwise1 (F.mapTriple F.forward1 f) (F.mapTriple F.forward1 g)
mapForwardOverConvolutionColumns (F.triple a b c) (F.triple d e g)
  rewrite C1.c3DirectConvolutionTheorem a d
        | C1.c3DirectConvolutionTheorem b e
        | C1.c3DirectConvolutionTheorem c g = refl

transposePointwiseProduct :
  (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.transpose2 (F.zipTriple pointwise1 f g)
  ≡ pointwise2 (F.transpose2 f) (F.transpose2 g)
transposePointwiseProduct
  (F.triple (F.triple a00 a01 a02) (F.triple a10 a11 a12) (F.triple a20 a21 a22))
  (F.triple (F.triple b00 b01 b02) (F.triple b10 b11 b12) (F.triple b20 b21 b22)) = refl

transformMatrixYConvolution :
  (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.transformMatrixY (cyclicWith add1 pointwise1 f g)
  ≡ pointwise2 (F.transformMatrixY f) (F.transformMatrixY g)
transformMatrixYConvolution f g
  rewrite transposeCyclicPointwise f g
        | mapForwardOverConvolutionColumns (F.transpose2 f) (F.transpose2 g)
        | transposePointwiseProduct
            (F.mapTriple F.forward1 (F.transpose2 f))
            (F.mapTriple F.forward1 (F.transpose2 g)) = refl

------------------------------------------------------------------------
-- Full C3^2 transform and convolution theorem.
------------------------------------------------------------------------

fourier2 :
  F.Triple (F.Triple F.Cyclotomic3) → F.Triple (F.Triple F.Cyclotomic3)
fourier2 m = F.transformMatrixY (F.mapTriple F.forward1 m)

fourier2Convolution : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  fourier2 (convolution2 f g) ≡ pointwise2 (fourier2 f) (fourier2 g)
fourier2Convolution f g
  rewrite zMapsConvolution2 f g
        | transformMatrixYConvolution
            (F.mapTriple F.forward1 f)
            (F.mapTriple F.forward1 g) = refl

------------------------------------------------------------------------
-- Additivity is needed to lift convolution through the final x-axis.
------------------------------------------------------------------------

mapForwardAddRows : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.mapTriple F.forward1 (F.zipTriple add1 f g)
  ≡ F.zipTriple add1 (F.mapTriple F.forward1 f) (F.mapTriple F.forward1 g)
mapForwardAddRows (F.triple a b c) (F.triple d e g)
  rewrite C1.forward1Additive a d
        | C1.forward1Additive b e
        | C1.forward1Additive c g = refl

transposePointwiseAdd : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.transpose2 (F.zipTriple add1 f g)
  ≡ F.zipTriple add1 (F.transpose2 f) (F.transpose2 g)
transposePointwiseAdd
  (F.triple (F.triple a00 a01 a02) (F.triple a10 a11 a12) (F.triple a20 a21 a22))
  (F.triple (F.triple b00 b01 b02) (F.triple b10 b11 b12) (F.triple b20 b21 b22)) = refl

transformMatrixYAdditive : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  F.transformMatrixY (F.zipTriple add1 f g)
  ≡ F.zipTriple add1 (F.transformMatrixY f) (F.transformMatrixY g)
transformMatrixYAdditive f g
  rewrite transposePointwiseAdd f g
        | mapForwardAddRows (F.transpose2 f) (F.transpose2 g)
        | transposePointwiseAdd
            (F.mapTriple F.forward1 (F.transpose2 f))
            (F.mapTriple F.forward1 (F.transpose2 g)) = refl

fourier2Additive : (f g : F.Triple (F.Triple F.Cyclotomic3)) →
  fourier2 (F.zipTriple add1 f g) ≡ F.zipTriple add1 (fourier2 f) (fourier2 g)
fourier2Additive f g
  rewrite mapForwardAddRows f g
        | transformMatrixYAdditive (F.mapTriple F.forward1 f) (F.mapTriple F.forward1 g) = refl

------------------------------------------------------------------------
-- Applying the C3^2 transform independently to each x coefficient turns the
-- inner product-group convolution into pointwise yz multiplication.
------------------------------------------------------------------------

mapFourier2Convolution3 : (f g : F.CubeSignal) →
  F.mapTriple fourier2 (convolution3 f g)
  ≡ cyclicWith add2 pointwise2 (F.mapTriple fourier2 f) (F.mapTriple fourier2 g)
mapFourier2Convolution3 =
  mapCyclicHom add2 convolution2 add2 pointwise2
    fourier2 fourier2Additive fourier2Convolution

preXYEqualsYZ : (x : F.CubeSignal) →
  F.mapTriple fourier2 x ≡ F.transformY (F.transformZ x)
preXYEqualsYZ (F.triple a b c) = refl

------------------------------------------------------------------------
-- x-axis diagonalization.  swapXY turns an x convolution with pointwise yz
-- coefficients into three independent y-labelled matrix convolutions along
-- the middle (formerly x) coordinate.
------------------------------------------------------------------------

swapOuterConvolution : (f g : F.CubeSignal) →
  F.swapXY (cyclicWith add2 pointwise2 f g)
  ≡ F.zipTriple (cyclicWith add1 pointwise1) (F.swapXY f) (F.swapXY g)
swapOuterConvolution
  (F.triple
    (F.triple (F.triple a000 a001 a002) (F.triple a010 a011 a012) (F.triple a020 a021 a022))
    (F.triple (F.triple a100 a101 a102) (F.triple a110 a111 a112) (F.triple a120 a121 a122))
    (F.triple (F.triple a200 a201 a202) (F.triple a210 a211 a212) (F.triple a220 a221 a222)))
  (F.triple
    (F.triple (F.triple b000 b001 b002) (F.triple b010 b011 b012) (F.triple b020 b021 b022))
    (F.triple (F.triple b100 b101 b102) (F.triple b110 b111 b112) (F.triple b120 b121 b122))
    (F.triple (F.triple b200 b201 b202) (F.triple b210 b211 b212) (F.triple b220 b221 b222))) = refl

transformYOnCyclicMatrices : (f g : F.CubeSignal) →
  F.transformY (F.zipTriple (cyclicWith add1 pointwise1) f g)
  ≡ F.zipTriple pointwise2 (F.transformY f) (F.transformY g)
transformYOnCyclicMatrices (F.triple a b c) (F.triple d e g)
  rewrite transformMatrixYConvolution a d
        | transformMatrixYConvolution b e
        | transformMatrixYConvolution c g = refl

swapPointwiseProduct : (f g : F.CubeSignal) →
  F.swapXY (pointwise3 f g) ≡ pointwise3 (F.swapXY f) (F.swapXY g)
swapPointwiseProduct
  (F.triple
    (F.triple (F.triple a000 a001 a002) (F.triple a010 a011 a012) (F.triple a020 a021 a022))
    (F.triple (F.triple a100 a101 a102) (F.triple a110 a111 a112) (F.triple a120 a121 a122))
    (F.triple (F.triple a200 a201 a202) (F.triple a210 a211 a212) (F.triple a220 a221 a222)))
  (F.triple
    (F.triple (F.triple b000 b001 b002) (F.triple b010 b011 b012) (F.triple b020 b021 b022))
    (F.triple (F.triple b100 b101 b102) (F.triple b110 b111 b112) (F.triple b120 b121 b122))
    (F.triple (F.triple b200 b201 b202) (F.triple b210 b211 b212) (F.triple b220 b221 b222))) = refl

transformXConvolution : (f g : F.CubeSignal) →
  F.transformX (cyclicWith add2 pointwise2 f g)
  ≡ pointwise3 (F.transformX f) (F.transformX g)
transformXConvolution f g
  rewrite swapOuterConvolution f g
        | transformYOnCyclicMatrices (F.swapXY f) (F.swapXY g)
        | swapPointwiseProduct (F.transformY (F.swapXY f)) (F.transformY (F.swapXY g)) = refl

------------------------------------------------------------------------
-- Full ordinary C3^3 convolution theorem.
------------------------------------------------------------------------

c3CubeDirectConvolutionTheorem : (f g : F.CubeSignal) →
  F.fourier27 (convolution3 f g)
  ≡ pointwise3 (F.fourier27 f) (F.fourier27 g)
c3CubeDirectConvolutionTheorem f g
  rewrite sym (preXYEqualsYZ (convolution3 f g))
        | mapFourier2Convolution3 f g
        | transformXConvolution (F.mapTriple fourier2 f) (F.mapTriple fourier2 g)
        | preXYEqualsYZ f
        | preXYEqualsYZ g = refl

------------------------------------------------------------------------
-- Therefore the direct group convolution equals the induced spectral
-- convolution, by injectivity/two-sided inversion of the exact DFT.
------------------------------------------------------------------------

directEqualsSpectralConvolution : (f g : F.CubeSignal) →
  convolution3 f g ≡ F.spectralConvolution f g
directEqualsSpectralConvolution f g =
  sym (trans
    (cong F.inverseFourier27 (c3CubeDirectConvolutionTheorem f g))
    (F.cubeFourierInversion (convolution3 f g)))
