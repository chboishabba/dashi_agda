module DASHI.Physics.Closure.NSTriadKNLuoTriadwiseEnergyCancellationRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- The global Galerkin energy cancellation is reduced to a local six-term
-- identity on one resonant triad.  For p+q+k=0 and transverse amplitudes
-- a,b,c, incompressibility gives
--
--   a.q = -a.k,  b.k = -b.p,  c.p = -c.q.
--
-- The two ordered placements at each output then cancel cyclically.  This
-- file proves that algebra exactly over Q, before any shell grouping or
-- absolute-value majorant is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

zeroQ : ℚ
zeroQ = Int.+ 0 / 1

record ResonantTriadEnergyCoordinates : Set where
  constructor resonant-triad-energy-coordinates
  field
    -- Wave-vector contractions.
    aDotQ aDotK : ℚ
    bDotP bDotK : ℚ
    cDotP cDotQ : ℚ

    -- Symmetric amplitude pairings.
    aDotB aDotC bDotC : ℚ

    -- Resonance plus transversality consequences.
    aDotKIsNegativeADotQ : aDotK ≡ zeroQ - aDotQ
    bDotKIsNegativeBDotP : bDotK ≡ zeroQ - bDotP
    cDotPIsNegativeCDotQ : cDotP ≡ zeroQ - cDotQ

open ResonantTriadEnergyCoordinates public

------------------------------------------------------------------------
-- The six ordered energy-transfer atoms, two at each output mode.
------------------------------------------------------------------------

outputKTransfer : ResonantTriadEnergyCoordinates → ℚ
outputKTransfer C =
  aDotQ C * bDotC C
  + bDotP C * aDotC C

outputPTransfer : ResonantTriadEnergyCoordinates → ℚ
outputPTransfer C =
  bDotK C * aDotC C
  + cDotQ C * aDotB C

outputQTransfer : ResonantTriadEnergyCoordinates → ℚ
outputQTransfer C =
  cDotP C * aDotB C
  + aDotK C * bDotC C

cyclicTriadEnergyTransfer : ResonantTriadEnergyCoordinates → ℚ
cyclicTriadEnergyTransfer C =
  outputKTransfer C
  + outputPTransfer C
  + outputQTransfer C

------------------------------------------------------------------------
-- Pairwise cancellations expose which terms pay for which terms.  This is
-- stronger than proving only the final scalar equality and can be reused by
-- shell-flux and cutoff-boundary arguments.
------------------------------------------------------------------------

aPairCancels :
  (C : ResonantTriadEnergyCoordinates) →
  aDotQ C * bDotC C + aDotK C * bDotC C ≡ zeroQ
aPairCancels C
  rewrite aDotKIsNegativeADotQ C =
  solve (aDotQ C ∷ bDotC C ∷ [])

bPairCancels :
  (C : ResonantTriadEnergyCoordinates) →
  bDotP C * aDotC C + bDotK C * aDotC C ≡ zeroQ
bPairCancels C
  rewrite bDotKIsNegativeBDotP C =
  solve (bDotP C ∷ aDotC C ∷ [])

cPairCancels :
  (C : ResonantTriadEnergyCoordinates) →
  cDotQ C * aDotB C + cDotP C * aDotB C ≡ zeroQ
cPairCancels C
  rewrite cDotPIsNegativeCDotQ C =
  solve (cDotQ C ∷ aDotB C ∷ [])

resonantTriadEnergyExchangeCyclicZero :
  (C : ResonantTriadEnergyCoordinates) →
  cyclicTriadEnergyTransfer C ≡ zeroQ
resonantTriadEnergyExchangeCyclicZero C
  rewrite aDotKIsNegativeADotQ C
        | bDotKIsNegativeBDotP C
        | cDotPIsNegativeCDotQ C =
  solve
    ( aDotQ C ∷ bDotP C ∷ cDotQ C
    ∷ aDotB C ∷ aDotC C ∷ bDotC C ∷ [])

------------------------------------------------------------------------
-- A finite list of complete triads has zero internal energy exchange.  Any
-- nonzero cumulative shell transfer must therefore arise from cutting triads
-- across shell or Galerkin boundaries, not from internal production.
------------------------------------------------------------------------

sumTriadTransfers : List ResonantTriadEnergyCoordinates → ℚ
sumTriadTransfers [] = zeroQ
sumTriadTransfers (C ∷ rest) =
  cyclicTriadEnergyTransfer C + sumTriadTransfers rest

shellInternalTransferCancels :
  (triads : List ResonantTriadEnergyCoordinates) →
  sumTriadTransfers triads ≡ zeroQ
shellInternalTransferCancels [] = solve []
shellInternalTransferCancels (C ∷ rest)
  rewrite resonantTriadEnergyExchangeCyclicZero C
        | shellInternalTransferCancels rest =
  solve []
