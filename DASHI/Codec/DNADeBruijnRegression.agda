module DASHI.Codec.DNADeBruijnRegression where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([])

open import DASHI.Codec.DNAProductionConstraints using (initialState)
open import DASHI.Codec.DNAProductionChoices using (branchCount)
open import DASHI.Codec.DNAProductionDeBruijn using
  ( LabelledWalk; done; outDegree; branchCount-is-outDegree )
open import DASHI.Codec.DNADeBruijnWalks using
  ( append; appendWalk )

emptyWalk : LabelledWalk initialState [] initialState
emptyWalk = done

empty-append : append [] [] ≡ []
empty-append = refl

initial-branch-is-out-degree :
  branchCount initialState ≡ outDegree initialState
initial-branch-is-out-degree = branchCount-is-outDegree initialState

empty-walk-composes :
  appendWalk emptyWalk emptyWalk ≡ emptyWalk
empty-walk-composes = refl
