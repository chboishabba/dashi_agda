module DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.CayleyDicksonRationalOctonionExact as O
import DASHI.Mathematics.Algebra.RationalOctonionSignedBasisAutomorphismExact as G

selected : O.RationalOctonion
selected = O.e1

aHasOrderTwoAtSelected : G.autoA (G.autoA selected) ≡ selected
aHasOrderTwoAtSelected = G.autoASquaredIdentity selected

bHasOrderThreeAtSelected : G.autoB (G.autoB (G.autoB selected)) ≡ selected
bHasOrderThreeAtSelected = G.autoBCubedIdentity selected
