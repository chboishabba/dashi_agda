module DASHI.Cognition.PNF.X369ConcreteLiteralHistorySeparatorExact where

-- Weld exact C3 signed-six action directly into history minimality.
-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- No claim that original learned Torch recurrence satisfies these equations.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Fin using (Fin)
open import Agda.Builtin.List using (List)
open import Data.Empty using (⊥)
import DASHI.Cognition.PNF.X369ConcreteSixVectorExact as Six
import DASHI.Cognition.PNF.X369ConstructiveConsumerSplitExact as Split
import DASHI.Cognition.PNF.X369CommutingHistorySeparatorExact as History

module FixedGuards {Value : Set}
  (flip : Value → Value)
  (involution : (v : Value) → flip (flip v) ≡ v)
  (aGuard bGuard : Fin 3) where

  module Geometry = Six.Carrier flip involution

  step : Split.Literal → Geometry.State → Geometry.State
  step Split.a = Geometry.apply (Geometry.aGuard aGuard)
  step Split.b = Geometry.apply (Geometry.bGuard bGuard)
  step Split.j = Geometry.apply (Geometry.literal Geometry.j1)
  step Split.n = Geometry.apply (Geometry.literal Geometry.n1)

  module Obstruction = History.Witness step
    (Geometry.commuteAction aGuard bGuard)

  sameEndpoint : (suffix : List Split.Literal) (z : Geometry.State) →
    Obstruction.run (Split.a ∷ Split.b ∷ suffix) z ≡
    Obstruction.run (Split.b ∷ Split.a ∷ suffix) z
  sameEndpoint = Obstruction.semanticCollision

  noSemanticOnlyFirstReader :
    (suffix : List Split.Literal) (z : Geometry.State) →
    (read : Geometry.State → Split.Latch) →
    ((word : List Split.Literal) →
      read (Obstruction.run word z) ≡
      Split.runLatch word Split.unset) → ⊥
  noSemanticOnlyFirstReader = Obstruction.cannotFactorFirstThroughEndpoint
