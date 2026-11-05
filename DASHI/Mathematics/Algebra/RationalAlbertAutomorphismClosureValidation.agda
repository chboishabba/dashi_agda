module DASHI.Mathematics.Algebra.RationalAlbertAutomorphismClosureValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertHermitianCubicExact as A
import DASHI.Mathematics.Algebra.RationalAlbertKnownGeneratorFamilyExact as G
import DASHI.Mathematics.Algebra.RationalAlbertAutomorphismClosureExact as C

cycleThenTriality : C.AutomorphismWord
cycleThenTriality =
  C.composeWord
    (C.generatorWord G.coordinateCycle)
    (C.generatorWord G.selectedMoufangTriality)

compiledRoundTrip : (x : A.RationalAlbert) →
  C.AlbertAutomorphism.backward (C.compileWord cycleThenTriality)
    (C.AlbertAutomorphism.forward (C.compileWord cycleThenTriality) x)
  ≡ x
compiledRoundTrip =
  C.AlbertAutomorphism.backwardForward (C.compileWord cycleThenTriality)
