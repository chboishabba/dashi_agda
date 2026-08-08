module DASHI.Physics.YangMills.BalabanWilsonBooleanFourCubeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Gian-Carlo Rota,
-- "On the Foundations of Combinatorial Theory I. Theory of Möbius
-- Functions", Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte
-- Gebiete 2 (1964), 340--368.
-- DOI: 10.1007/BF00531932.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Give the four plaquette-factor subset cube a literal finite carrier.  Its
-- sixteen elements are the empty/background placement and the fifteen
-- nonempty Wilson atoms, with exact degree counts 4+6+4+1.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.List.Base using (length)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data BondSlot4 : Set where
  slot0 slot1 slot2 slot3 : BondSlot4

bondSlots4 : List BondSlot4
bondSlots4 = slot0 ∷ slot1 ∷ slot2 ∷ slot3 ∷ []

data Subset4 : Set where
  empty : Subset4
  s0 s1 s2 s3 : Subset4
  s01 s02 s03 s12 s13 s23 : Subset4
  s012 s013 s023 s123 : Subset4
  s0123 : Subset4

allSubsets4 : List Subset4
allSubsets4 =
  empty
  ∷ s0 ∷ s1 ∷ s2 ∷ s3
  ∷ s01 ∷ s02 ∷ s03 ∷ s12 ∷ s13 ∷ s23
  ∷ s012 ∷ s013 ∷ s023 ∷ s123
  ∷ s0123
  ∷ []

nonemptySubsets4 : List Subset4
nonemptySubsets4 =
  s0 ∷ s1 ∷ s2 ∷ s3
  ∷ s01 ∷ s02 ∷ s03 ∷ s12 ∷ s13 ∷ s23
  ∷ s012 ∷ s013 ∷ s023 ∷ s123
  ∷ s0123
  ∷ []

singletonSubsets4 : List Subset4
singletonSubsets4 = s0 ∷ s1 ∷ s2 ∷ s3 ∷ []

pairSubsets4 : List Subset4
pairSubsets4 = s01 ∷ s02 ∷ s03 ∷ s12 ∷ s13 ∷ s23 ∷ []

tripleSubsets4 : List Subset4
tripleSubsets4 = s012 ∷ s013 ∷ s023 ∷ s123 ∷ []

quarticSubsets4 : List Subset4
quarticSubsets4 = s0123 ∷ []

subsetCardinality : Subset4 → Nat
subsetCardinality empty = 0
subsetCardinality s0 = 1
subsetCardinality s1 = 1
subsetCardinality s2 = 1
subsetCardinality s3 = 1
subsetCardinality s01 = 2
subsetCardinality s02 = 2
subsetCardinality s03 = 2
subsetCardinality s12 = 2
subsetCardinality s13 = 2
subsetCardinality s23 = 2
subsetCardinality s012 = 3
subsetCardinality s013 = 3
subsetCardinality s023 = 3
subsetCardinality s123 = 3
subsetCardinality s0123 = 4

contains : BondSlot4 → Subset4 → Bool
contains slot0 empty = false
contains slot1 empty = false
contains slot2 empty = false
contains slot3 empty = false

contains slot0 s0 = true
contains slot1 s0 = false
contains slot2 s0 = false
contains slot3 s0 = false

contains slot0 s1 = false
contains slot1 s1 = true
contains slot2 s1 = false
contains slot3 s1 = false

contains slot0 s2 = false
contains slot1 s2 = false
contains slot2 s2 = true
contains slot3 s2 = false

contains slot0 s3 = false
contains slot1 s3 = false
contains slot2 s3 = false
contains slot3 s3 = true

contains slot0 s01 = true
contains slot1 s01 = true
contains slot2 s01 = false
contains slot3 s01 = false

contains slot0 s02 = true
contains slot1 s02 = false
contains slot2 s02 = true
contains slot3 s02 = false

contains slot0 s03 = true
contains slot1 s03 = false
contains slot2 s03 = false
contains slot3 s03 = true

contains slot0 s12 = false
contains slot1 s12 = true
contains slot2 s12 = true
contains slot3 s12 = false

contains slot0 s13 = false
contains slot1 s13 = true
contains slot2 s13 = false
contains slot3 s13 = true

contains slot0 s23 = false
contains slot1 s23 = false
contains slot2 s23 = true
contains slot3 s23 = true

contains slot0 s012 = true
contains slot1 s012 = true
contains slot2 s012 = true
contains slot3 s012 = false

contains slot0 s013 = true
contains slot1 s013 = true
contains slot2 s013 = false
contains slot3 s013 = true

contains slot0 s023 = true
contains slot1 s023 = false
contains slot2 s023 = true
contains slot3 s023 = true

contains slot0 s123 = false
contains slot1 s123 = true
contains slot2 s123 = true
contains slot3 s123 = true

contains slot0 s0123 = true
contains slot1 s0123 = true
contains slot2 s0123 = true
contains slot3 s0123 = true

complement : Subset4 → Subset4
complement empty = s0123
complement s0 = s123
complement s1 = s023
complement s2 = s013
complement s3 = s012
complement s01 = s23
complement s02 = s13
complement s03 = s12
complement s12 = s03
complement s13 = s02
complement s23 = s01
complement s012 = s3
complement s013 = s2
complement s023 = s1
complement s123 = s0
complement s0123 = empty

complementInvolutive : ∀ subset →
  complement (complement subset) ≡ subset
complementInvolutive empty = refl
complementInvolutive s0 = refl
complementInvolutive s1 = refl
complementInvolutive s2 = refl
complementInvolutive s3 = refl
complementInvolutive s01 = refl
complementInvolutive s02 = refl
complementInvolutive s03 = refl
complementInvolutive s12 = refl
complementInvolutive s13 = refl
complementInvolutive s23 = refl
complementInvolutive s012 = refl
complementInvolutive s013 = refl
complementInvolutive s023 = refl
complementInvolutive s123 = refl
complementInvolutive s0123 = refl

allSubsetCountExact : length allSubsets4 ≡ 16
allSubsetCountExact = refl

nonemptySubsetCountExact : length nonemptySubsets4 ≡ 15
nonemptySubsetCountExact = refl

singletonSubsetCountExact : length singletonSubsets4 ≡ 4
singletonSubsetCountExact = refl

pairSubsetCountExact : length pairSubsets4 ≡ 6
pairSubsetCountExact = refl

tripleSubsetCountExact : length tripleSubsets4 ≡ 4
tripleSubsetCountExact = refl

quarticSubsetCountExact : length quarticSubsets4 ≡ 1
quarticSubsetCountExact = refl

nonemptyDegreePartitionCountExact :
  length singletonSubsets4
  + (length pairSubsets4
  + (length tripleSubsets4
  + length quarticSubsets4))
  ≡ length nonemptySubsets4
nonemptyDegreePartitionCountExact = refl

booleanFourCubeCarrierLevel : ProofLevel
booleanFourCubeCarrierLevel = machineChecked

booleanFourCubeDegreeCountLevel : ProofLevel
booleanFourCubeDegreeCountLevel = machineChecked
