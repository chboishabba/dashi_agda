module DASHI.Biology.MoonshineOrbifoldModularSectorActionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Chongying Dong, Haisheng Li and Geoffrey Mason,
-- "Modular-Invariance of Trace Functions in Orbifold Theory and Generalized
-- Moonshine".
-- DOI: 10.1007/s002200000242.
--
-- Charles Dong and Geoffrey Mason,
-- "On Quantum Galois Theory".
-- DOI: 10.1215/S0012-7094-98-09312-6.
--
-- Igor B. Frenkel, James Lepowsky and Arne Meurman,
-- "Vertex Operator Algebras and the Monster".
-- ISBN: 0-12-267065-5.  No DOI asserted here.
--
-- DASHI CONTRIBUTION
--
-- Make the finite modular-sector bookkeeping of a Z/2 orbifold exact.  A
-- twisted-twining trace is indexed by a commuting pair (g,h).  For Z/2 the
-- modular generators act by
--
--   S(g,h) = (h,g),
--   T(g,h) = (g,g+h).
--
-- We prove S^2=1, T^2=1 and (ST)^3=1 on all four sectors.  The vacuum sector
-- (0,0) is fixed, while the three nontrivial sectors form one exact three-cycle
-- under ST.  This is the finite permutation skeleton behind orbifold modular
-- covariance; it does not prove analytic modularity of the corresponding trace
-- functions or construct the twisted module.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Bit : Set where
  zeroBit : Bit
  oneBit : Bit

addBit : Bit → Bit → Bit
addBit zeroBit right = right
addBit oneBit zeroBit = oneBit
addBit oneBit oneBit = zeroBit

addBitSelfZero : (value : Bit) → addBit value value ≡ zeroBit
addBitSelfZero zeroBit = refl
addBitSelfZero oneBit = refl

record OrbifoldSector : Set where
  constructor sector
  field
    spatialTwist : Bit
    temporalInsertion : Bit

open OrbifoldSector public

S : OrbifoldSector → OrbifoldSector
S value = sector (temporalInsertion value) (spatialTwist value)

T : OrbifoldSector → OrbifoldSector
T value =
  sector
    (spatialTwist value)
    (addBit (spatialTwist value) (temporalInsertion value))

ST : OrbifoldSector → OrbifoldSector
ST value = S (T value)

SInvolutive : (value : OrbifoldSector) → S (S value) ≡ value
SInvolutive (sector zeroBit zeroBit) = refl
SInvolutive (sector zeroBit oneBit) = refl
SInvolutive (sector oneBit zeroBit) = refl
SInvolutive (sector oneBit oneBit) = refl

TInvolutive : (value : OrbifoldSector) → T (T value) ≡ value
TInvolutive (sector zeroBit zeroBit) = refl
TInvolutive (sector zeroBit oneBit) = refl
TInvolutive (sector oneBit zeroBit) = refl
TInvolutive (sector oneBit oneBit) = refl

STOrderThree : (value : OrbifoldSector) → ST (ST (ST value)) ≡ value
STOrderThree (sector zeroBit zeroBit) = refl
STOrderThree (sector zeroBit oneBit) = refl
STOrderThree (sector oneBit zeroBit) = refl
STOrderThree (sector oneBit oneBit) = refl

vacuumSector untwistedTwining twistedNoInsertion twistedTwining :
  OrbifoldSector
vacuumSector = sector zeroBit zeroBit
untwistedTwining = sector zeroBit oneBit
twistedNoInsertion = sector oneBit zeroBit
twistedTwining = sector oneBit oneBit

vacuumFixedByST : ST vacuumSector ≡ vacuumSector
vacuumFixedByST = refl

nontrivialCycleFirst : ST untwistedTwining ≡ twistedNoInsertion
nontrivialCycleFirst = refl

nontrivialCycleSecond : ST twistedNoInsertion ≡ twistedTwining
nontrivialCycleSecond = refl

nontrivialCycleThird : ST twistedTwining ≡ untwistedTwining
nontrivialCycleThird = refl

vacuumIsNotTwisted : vacuumSector ≡ twistedNoInsertion → ⊥
vacuumIsNotTwisted ()

record OrbifoldModularityBoundary : Set where
  constructor orbifoldModularityBoundary
  field
    sectorPermutationProvesAnalyticModularity : Set
    sectorPermutationDoesNotProveAnalyticModularity :
      sectorPermutationProvesAnalyticModularity → Set

    sectorPermutationConstructsTwistedModule : Set
    sectorPermutationDoesNotConstructTwistedModule :
      sectorPermutationConstructsTwistedModule → Set

canonicalOrbifoldModularityBoundary : OrbifoldModularityBoundary
canonicalOrbifoldModularityBoundary =
  orbifoldModularityBoundary
    ⊥ (λ impossible → ⊥)
    ⊥ (λ impossible → ⊥)
