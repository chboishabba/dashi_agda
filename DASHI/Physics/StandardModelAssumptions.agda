module DASHI.Physics.StandardModelAssumptions where

open import Data.Unit using (⊤; tt)

record Group (G : Set) : Set₁ where
  field
    e   : G
    _∙_ : G → G → G
    inv : G → G

record StandardModelGate : Set₁ where
  field
    SU3 SU2 U1 : Set
    emerges : ⊤
    three-generations : ⊤
    hypercharges-ok   : ⊤
    anomaly-cancel    : ⊤
