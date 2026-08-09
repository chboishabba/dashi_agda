module DASHI.Foundations.Base369LayeredAttractorAndCoarseFineExact where

------------------------------------------------------------------------
-- The 3/6/9 pattern is cumulative depth:
--   3 = one local ternary horizon,
--   6 = immediate plus medium transport,
--   9 = immediate, medium, and long integration.
--
-- Separately, 11 = 1 + 10 is a coarse/fine carrier.  The coarse coordinate
-- may itself carry nominal/actual fibres, but that semantic two-one split does
-- not replace the structural 1+10 decomposition.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Fin.Base using (Fin)

open import Base369 using (TriTruth)
open import DASHI.Foundations.Base369SignedMembershipExact using
  (NominalActual)

record Horizon3 : Set where
  constructor horizon3
  field
    state : TriTruth
    transport : TriTruth
    result : TriTruth

open Horizon3 public

record Depth6 : Set where
  constructor depth6
  field
    immediate : Horizon3
    medium : Horizon3

open Depth6 public

record Depth9 : Set where
  constructor depth9
  field
    firstSix : Depth6
    long : Horizon3

open Depth9 public

project9To6 : Depth9 → Depth6
project9To6 = firstSix

project6To3 : Depth6 → Horizon3
project6To3 = immediate

project9To3 : Depth9 → Horizon3
project9To3 x = immediate (firstSix x)

record LayeredAttractor (A : Set) : Set where
  constructor layeredAttractor
  field
    immediateAttractor : A
    mediumAttractor : A
    longAttractor : A

open LayeredAttractor public

record HorizonCompatible {A : Set} (target : LayeredAttractor A) : Set where
  constructor horizonCompatible
  field
    immediatePreserved : A
    mediumPreserved : A
    longPreserved : A

------------------------------------------------------------------------
-- A branch may be locally successful and globally adverse.
------------------------------------------------------------------------

record HorizonDrift : Set where
  constructor horizonDrift
  field
    immediateDrift : TriTruth
    mediumDrift : TriTruth
    longDrift : TriTruth

open HorizonDrift public

------------------------------------------------------------------------
-- Structural coarse/fine 11.
------------------------------------------------------------------------

record CoarseFine11 (Coarse Fine : Set) : Set where
  constructor coarseFine11
  field
    coarse1 : Coarse
    fine10 : Fin 10 → Fine

open CoarseFine11 public

record CoarseFineReconstruction
  (Whole Coarse Fine : Set) : Set₁ where
  constructor coarseFineReconstruction
  field
    observe : Whole → CoarseFine11 Coarse Fine
    reconstruct : CoarseFine11 Coarse Fine → Whole
    reconstructAfterObserve :
      (x : Whole) → reconstruct (observe x) ≡ x

open CoarseFineReconstruction public

-- A nominal/actual pair may live inside the single coarse channel.
record CoarseWithNominalActual (A Fine : Set) : Set where
  constructor coarseWithNominalActual
  field
    coarseSemanticPair : NominalActual A
    fineRealisation : Fin 10 → Fine

------------------------------------------------------------------------
-- The address alphabet never restricts the fibre ontology.
------------------------------------------------------------------------

record AddressedFibre
  (Address : Set)
  (Fibre : Address → Set) : Set₁ where
  constructor addressedFibre
  field
    address : Address
    payload : Fibre address

open AddressedFibre public

record ContinuousOrWaveCarrier
  (Address : Set)
  (Field : Set)
  (at : Address → Field) : Set₁ where
  constructor continuousOrWaveCarrier
  field
    exactField : Field
    localAddress : Address
    addressAgrees : at localAddress ≡ exactField

-- Generic n-ary/mixed carriers are admitted simply by choosing another Address.
-- Balanced ternary is the minimal signed local alphabet, not an ontological
-- claim that the payload is finite or discrete.
