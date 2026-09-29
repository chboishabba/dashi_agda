module DASHI.Physics.CondensedMatter.AltermagnetCoQuarterTaSeTwo where

-- Finite, source-attributed symmetry witness, NOT a derivation of the
-- experimental electronic structure or a claim of room-temperature operation.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record PublishedEvidence : Set where
  constructor evidence
  field
    authors : String
    title : String
    venue : String
    doi : String
    observation : String
    epistemicBoundary : String

sprague2026 : PublishedEvidence
sprague2026 = evidence
  "Milo Sprague; Mazharul Islam Mondal; Anup Pradhan Sakhya; Resham Babu Regmi; Surasree Sadhukhan; Arun K. Kumay; Himanshu Sheokand; Igor I. Mazin; Nirmal J. Ghimire; Madhab Neupane"
  "Observation of Altermagnetic Spin-Splitting in an Intercalated Transition Metal Dichalcogenide"
  "Nature Communications (2026-08-20)"
  "10.1038/s41467-026-76784-x"
  "Co1/4TaSe2: type-A antiferromagnetism, reported TN=178 K; spin-resolved / spin-integrated ARPES and DFT provide evidence of momentum-dependent spin splitting."
  "Source evidence is not a formal proof of a material model, a spin-current device, or a twisted heterostructure."

-- A two-momentum, two-spin abstraction.  The material-specific dispersion,
-- spin-orbit terms, symmetries, and ARPES matrix elements remain unmodelled.
data Spin : Set where
  up down : Spin

data Momentum : Set where
  kA kB : Momentum

reverseSpin : Spin → Spin
reverseSpin up = down
reverseSpin down = up

rotateMomentum : Momentum → Momentum
rotateMomentum kA = kB
rotateMomentum kB = kA

spin-involution : (s : Spin) → reverseSpin (reverseSpin s) ≡ s
spin-involution up = refl
spin-involution down = refl

momentum-involution : (k : Momentum) →
  rotateMomentum (rotateMomentum k) ≡ k
momentum-involution kA = refl
momentum-involution kB = refl

-- Illustrative band energies.  Their values are model choices, not fitted
-- measurements.  Opposite spin labels swap energy under momentum rotation.
energy : Momentum → Spin → Nat
energy kA up = 0
energy kA down = 1
energy kB up = 1
energy kB down = 0

-- Altermagnetic covariance for the illustrative two-point model.
combined-symmetry : (k : Momentum) (s : Spin) →
  energy (rotateMomentum k) (reverseSpin s) ≡ energy k s
combined-symmetry kA up = refl
combined-symmetry kA down = refl
combined-symmetry kB up = refl
combined-symmetry kB down = refl

-- A non-degenerate pair at either modeled momentum.
spin-splitting-A : energy kA up ≡ 0
spin-splitting-A = refl

spin-splitting-B : energy kB up ≡ 1
spin-splitting-B = refl

-- Equal representation of opposite spins in the two-sector carrier.
-- This is a finite counting witness, not a calculated magnetic moment.
up-count : Nat
up-count = suc (suc zero)

down-count : Nat
down-count = suc (suc zero)

compensated-count : up-count ≡ down-count
compensated-count = refl

-- Twistronics boundary: a variable twist requires a real angle-dependent
-- interlayer Hamiltonian; the operation below is ONLY a discrete exchange
-- of two momentum labels, not a physical twist-angle simulation.
