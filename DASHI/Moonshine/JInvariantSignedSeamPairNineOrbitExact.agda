module DASHI.Moonshine.JInvariantSignedSeamPairNineOrbitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Moonshine.JInvariantOrderThreeOrbitBalancedTernaryBidiExact as Orbit
import DASHI.Moonshine.Monster369SignedPairNineOrbitExact as Pair

------------------------------------------------------------------------
-- J-INVARIANT SIGNED-SEAM PAIR OBSERVER
--
-- The existing j owner already interprets one signed SSP multiplicity through
-- the canonical balanced trit as converging / identity / diverging seam
-- dynamics.  Pairing two such observations and then applying the existing
-- global inversion quotient retains relative sign geometry while forgetting
-- common orientation.
------------------------------------------------------------------------

seamPairOrbit :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Triadic.NineOrbit
seamPairOrbit = Pair.signedPairOrbit

firstSeamDynamics :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Orbit.SeamDynamics
firstSeamDynamics a b = Orbit.seamDynamicsOfMultiplicity a

secondSeamDynamics :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Orbit.SeamDynamics
secondSeamDynamics a b = Orbit.seamDynamicsOfMultiplicity b

firstGluingDynamics :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Orbit.GluingDynamics
firstGluingDynamics a b = Orbit.gluingDynamicsOfMultiplicity a

secondGluingDynamics :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Orbit.GluingDynamics
secondGluingDynamics a b = Orbit.gluingDynamicsOfMultiplicity b

bothSeamsNeutral :
  seamPairOrbit SSP.zeroMultiplicity SSP.zeroMultiplicity ≡ Triadic.zeroOrbit
bothSeamsNeutral = refl

firstSeamOnly :
  (n : Nat) ->
  seamPairOrbit (SSP.positiveMultiplicity n) SSP.zeroMultiplicity
  ≡ Triadic.firstAxisOrbit
firstSeamOnly n = refl

secondSeamOnly :
  (n : Nat) ->
  seamPairOrbit SSP.zeroMultiplicity (SSP.positiveMultiplicity n)
  ≡ Triadic.secondAxisOrbit
secondSeamOnly n = refl

sameSeamOrientation :
  (m n : Nat) ->
  seamPairOrbit (SSP.negativeMultiplicity m) (SSP.negativeMultiplicity n)
  ≡ Triadic.equalSignOrbit
sameSeamOrientation m n = refl

oppositeSeamOrientation :
  (m n : Nat) ->
  seamPairOrbit (SSP.negativeMultiplicity m) (SSP.positiveMultiplicity n)
  ≡ Triadic.oppositeSignOrbit
oppositeSeamOrientation m n = refl

simultaneousSeamInversionInvisible :
  (a b : SSP.SignedMultiplicity) ->
  seamPairOrbit (SSP.negateMultiplicity a) (SSP.negateMultiplicity b)
  ≡ seamPairOrbit a b
simultaneousSeamInversionInvisible = Pair.signedPairOrbitNegationInvariant

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data PairObserverCreatesSameTauCarrier : Set where
data PairObserverCreatesModularAction : Set where
data PairObserverCreatesMonsterRepresentation : Set where

pairObserverDoesNotCreateSameTauCarrier : PairObserverCreatesSameTauCarrier -> ⊥
pairObserverDoesNotCreateSameTauCarrier ()

pairObserverDoesNotCreateModularAction : PairObserverCreatesModularAction -> ⊥
pairObserverDoesNotCreateModularAction ()

pairObserverDoesNotCreateMonsterRepresentation :
  PairObserverCreatesMonsterRepresentation -> ⊥
pairObserverDoesNotCreateMonsterRepresentation ()

record JSeamPairNineOrbitBoundary : Set where
  constructor j-seam-pair-nine-orbit-boundary
  field
    existingSignedSeamObserverReused : Bool
    signedPairQuotientReused : Bool
    relativeFiveStateGeometryConstructed : Bool
    simultaneousOrientationForgotten : Bool
    sameTauCarrierCreated : Bool
    modularActionCreated : Bool
    monsterRepresentationCreated : Bool
    nextResidual : String
open JSeamPairNineOrbitBoundary public

canonicalJSeamPairNineOrbitBoundary : JSeamPairNineOrbitBoundary
canonicalJSeamPairNineOrbitBoundary =
  j-seam-pair-nine-orbit-boundary
    true true true true
    false false false
    "attach a concrete pair of same-object analytic seam observations only after their individual tau/source fibres are paid; the relative NineOrbit observer itself does not create that same-object attachment"
