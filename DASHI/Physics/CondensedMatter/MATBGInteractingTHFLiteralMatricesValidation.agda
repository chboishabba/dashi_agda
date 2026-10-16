module DASHI.Physics.CondensedMatter.MATBGInteractingTHFLiteralMatricesValidation where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.CondensedMatter.MATBGInteractingTHFLiteralMatricesExact as THFMatrix

hcKprime-is-valley-flip : THFMatrix.hcKPrime THFMatrix.i0 THFMatrix.i2 ≡ THFMatrix.valleyFlip (THFMatrix.hcK THFMatrix.i0 THFMatrix.i2)
hcKprime-is-valley-flip = refl

hcfKprime-is-valley-flip : THFMatrix.hcfKPrime THFMatrix.i2 THFMatrix.j1 ≡ THFMatrix.valleyFlip (THFMatrix.hcfK THFMatrix.i2 THFMatrix.j1)
hcfKprime-is-valley-flip = refl

literal-matrix-boundary-paid : THFMatrix.literalMatrixShapesPaid THFMatrix.canonicalTHFLiteralMatrixBoundary ≡ true
literal-matrix-boundary-paid = refl
