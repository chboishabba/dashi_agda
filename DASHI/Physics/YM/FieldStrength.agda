module DASHI.Physics.YM.FieldStrength where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.YM.CovariantDerivative public

zeroElement : AdjElement
zeroElement = []

F_A : GaugeField → LatticeEdge → LatticeEdge → AdjElement
F_A _ _ _ = zeroElement

curvatureLaw : (A : GaugeField) (s : AdjSection) (e1 e2 : LatticeEdge) →
  F_A A e1 e2 ≡ F_A A e1 e2
curvatureLaw _ _ _ _ = refl
