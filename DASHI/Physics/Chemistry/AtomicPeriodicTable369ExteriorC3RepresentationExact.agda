module DASHI.Physics.Chemistry.AtomicPeriodicTable369ExteriorC3RepresentationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3

------------------------------------------------------------------------
-- Finite exterior-basis lift of the paid one-particle p-shell C3 action.
--
-- The old AtomicValenceFermionBridgeExact pays swap sign and duplicate-state
-- vanishing for a two-label toy carrier, but explicitly does not complete an
-- exterior algebra.  Here we move one step further on the actual three-state
-- magnetic carrier used by the atomic C3 realization.
--
-- We still do not pretend that a finite basis/sign representation is the full
-- linear exterior algebra over C.  What is paid here is the exact induced C3
-- action on the ordered antisymmetric basis of wedge^2 and wedge^3.
------------------------------------------------------------------------

data WedgeSign : Set where
  positiveWedge : WedgeSign
  negativeWedge : WedgeSign

flipSign : WedgeSign -> WedgeSign
flipSign positiveWedge = negativeWedge
flipSign negativeWedge = positiveWedge

flipTwice : (s : WedgeSign) -> flipSign (flipSign s) ≡ s
flipTwice positiveWedge = refl
flipTwice negativeWedge = refl

data Wedge2Basis : Set where
  wedgeNegZero : Wedge2Basis
  wedgeNegPos : Wedge2Basis
  wedgeZeroPos : Wedge2Basis

record SignedWedge2 : Set where
  constructor signedWedge2
  field
    wedgeSign : WedgeSign
    wedgeBasis : Wedge2Basis

open SignedWedge2 public

negateWedge2 : SignedWedge2 -> SignedWedge2
negateWedge2 (signedWedge2 s b) = signedWedge2 (flipSign s) b

------------------------------------------------------------------------
-- U = chargePositiveStep on one-particle basis:
--
--   e- -> e0 -> e+ -> e-.
--
-- Therefore on wedge^2:
--   e-^e0 ->  e0^e+
--   e-^e+ ->  e0^e- = -(e-^e0)
--   e0^e+ ->  e+^e- = -(e-^e+).
------------------------------------------------------------------------

wedge2PositiveStep : SignedWedge2 -> SignedWedge2
wedge2PositiveStep (signedWedge2 s wedgeNegZero) =
  signedWedge2 s wedgeZeroPos
wedge2PositiveStep (signedWedge2 s wedgeNegPos) =
  signedWedge2 (flipSign s) wedgeNegZero
wedge2PositiveStep (signedWedge2 s wedgeZeroPos) =
  signedWedge2 (flipSign s) wedgeNegPos

wedge2ActionRespectsNegation :
  (x : SignedWedge2) ->
  wedge2PositiveStep (negateWedge2 x)
  ≡ negateWedge2 (wedge2PositiveStep x)
wedge2ActionRespectsNegation (signedWedge2 positiveWedge wedgeNegZero) = refl
wedge2ActionRespectsNegation (signedWedge2 negativeWedge wedgeNegZero) = refl
wedge2ActionRespectsNegation (signedWedge2 positiveWedge wedgeNegPos) = refl
wedge2ActionRespectsNegation (signedWedge2 negativeWedge wedgeNegPos) = refl
wedge2ActionRespectsNegation (signedWedge2 positiveWedge wedgeZeroPos) = refl
wedge2ActionRespectsNegation (signedWedge2 negativeWedge wedgeZeroPos) = refl

wedge2PositiveStepOrderThree :
  (x : SignedWedge2) ->
  wedge2PositiveStep (wedge2PositiveStep (wedge2PositiveStep x)) ≡ x
wedge2PositiveStepOrderThree (signedWedge2 positiveWedge wedgeNegZero) = refl
wedge2PositiveStepOrderThree (signedWedge2 negativeWedge wedgeNegZero) = refl
wedge2PositiveStepOrderThree (signedWedge2 positiveWedge wedgeNegPos) = refl
wedge2PositiveStepOrderThree (signedWedge2 negativeWedge wedgeNegPos) = refl
wedge2PositiveStepOrderThree (signedWedge2 positiveWedge wedgeZeroPos) = refl
wedge2PositiveStepOrderThree (signedWedge2 negativeWedge wedgeZeroPos) = refl

canonicalWedge2NegZero : SignedWedge2
canonicalWedge2NegZero = signedWedge2 positiveWedge wedgeNegZero

canonicalWedge2Orbit :
  wedge2PositiveStep
    (wedge2PositiveStep
      (wedge2PositiveStep canonicalWedge2NegZero))
  ≡ canonicalWedge2NegZero
canonicalWedge2Orbit = refl

------------------------------------------------------------------------
-- wedge^3 of the three-dimensional magnetic carrier is one-dimensional.
-- A three-cycle is an even permutation, hence the oriented volume element is
-- fixed exactly.
------------------------------------------------------------------------

data Wedge3Basis : Set where
  wedgeNegZeroPos : Wedge3Basis

wedge3PositiveStep : Wedge3Basis -> Wedge3Basis
wedge3PositiveStep wedgeNegZeroPos = wedgeNegZeroPos

wedge3PositiveStepInvariant :
  wedge3PositiveStep wedgeNegZeroPos ≡ wedgeNegZeroPos
wedge3PositiveStepInvariant = refl

wedge3PositiveStepOrderThree :
  wedge3PositiveStep
    (wedge3PositiveStep
      (wedge3PositiveStep wedgeNegZeroPos))
  ≡ wedgeNegZeroPos
wedge3PositiveStepOrderThree = refl

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record ExteriorC3RepresentationBoundary : Set where
  constructor exteriorC3RepresentationBoundary
  field
    actualPTripletOneParticleCarrierUsed : Bool
    antisymmetricTwoParticleBasisPaid : Bool
    exchangeSignPaid : Bool
    inducedWedge2C3ActionPaid : Bool
    inducedWedge2OrderThreePaid : Bool
    inducedWedge3ActionPaid : Bool
    closedThreeModeDeterminantInvariantPaid : Bool

    fullLinearExteriorAlgebraOverComplexPaid : Bool
    creationAnnihilationOperatorAlgebraPaid : Bool
    interactingHamiltonianSymmetryPaidHere : Bool
    fullAtom369IdentityPaid : Bool

open ExteriorC3RepresentationBoundary public

canonicalExteriorC3RepresentationBoundary : ExteriorC3RepresentationBoundary
canonicalExteriorC3RepresentationBoundary =
  exteriorC3RepresentationBoundary
    true true true true true true true
    false false false false

interactingHamiltonianSymmetryPaidHereIsFalse :
  interactingHamiltonianSymmetryPaidHere canonicalExteriorC3RepresentationBoundary
  ≡ false
interactingHamiltonianSymmetryPaidHereIsFalse = refl
