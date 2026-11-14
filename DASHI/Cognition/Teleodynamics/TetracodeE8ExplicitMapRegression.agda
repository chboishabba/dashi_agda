module DASHI.Cognition.Teleodynamics.TetracodeE8ExplicitMapRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Cognition.Teleodynamics.TetracodeE8ExplicitMapExact as T

open T.TetracodeE8ExecutionReceipt
open T.Boundary

shell240 : eisensteinMinimalShellCount T.canonicalTetracodeE8ExecutionReceipt ≡ 240
shell240 = refl

imageEqualsStandardE8 :
  explicitMatrixImageEqualsStandardE8RootSet T.canonicalTetracodeE8ExecutionReceipt ≡ true
imageEqualsStandardE8 = refl

notRelativeT5Recognition :
  explicitMapIdentifiesRelativeT5Carrier T.canonicalBoundary ≡ false
notRelativeT5Recognition = refl
