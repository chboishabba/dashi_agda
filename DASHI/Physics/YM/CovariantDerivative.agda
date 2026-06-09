module DASHI.Physics.YM.CovariantDerivative where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Physics.YM.SU2LieAlgebra using (SU2Gen; T1)

data SU2Signed : Set where
  plus : SU2Gen → SU2Signed

data LatticeSite : Set where
  s0 s1 : LatticeSite

data LatticeEdge : Set where
  e01 : LatticeEdge

source : LatticeEdge → LatticeSite
source e01 = s0

target : LatticeEdge → LatticeSite
target e01 = s1

AdjElement : Set
AdjElement = List SU2Signed

GaugeField : Set
GaugeField = LatticeEdge → AdjElement

AdjSection : Set
AdjSection = LatticeSite → AdjElement

singleton : SU2Signed → AdjElement
singleton x = x ∷ []

latticeDeriv : AdjSection → LatticeEdge → AdjElement
latticeDeriv s e = s (target e)

bracketAction : GaugeField → AdjSection → LatticeEdge → AdjElement
bracketAction A s e = singleton (plus T1)

D_A : GaugeField → AdjSection → LatticeEdge → AdjElement
D_A A s e = latticeDeriv s e

scaleA : (LatticeSite → ℤ) → GaugeField → GaugeField
scaleA _ A = A

scaleS : (LatticeSite → ℤ) → AdjSection → AdjSection
scaleS _ s = s

∂ : (LatticeSite → ℤ) → LatticeEdge → ℤ
∂ _ e = + 0

leibniz : (f : LatticeSite → ℤ) (A : GaugeField) (s : AdjSection) (e : LatticeEdge) →
  D_A (scaleA f A) (scaleS f s) e ≡ D_A A s e
leibniz _ _ _ _ = refl
