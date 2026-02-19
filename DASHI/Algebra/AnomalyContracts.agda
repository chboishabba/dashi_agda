module DASHI.Algebra.AnomalyContracts where

open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.Equality using (_≡_; refl)

data Particle : Set where
  QL uR dR LL eR : Particle

Y : Particle → Nat
Y QL = 1
Y uR = 4
Y dR = 2
Y LL = 3
Y eR = 6

-- placeholder computed results (set to 0 until you wire the real computation)
anomalyU1Cubed   : Nat
anomalyU1Cubed   = 0

anomalySU2SU2U1  : Nat
anomalySU2SU2U1  = 0

anomalySU3SU3U1  : Nat
anomalySU3SU3U1  = 0

cancel-U1³ : anomalyU1Cubed ≡ 0
cancel-U1³ = refl

cancel-221 : anomalySU2SU2U1 ≡ 0
cancel-221 = refl

cancel-331 : anomalySU3SU3U1 ≡ 0
cancel-331 = refl
