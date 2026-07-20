module DASHI.Physics.Closure.ShiftFixedPointPerturbationClassification where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat using (_≤_; _<_)

open import DASHI.Physics.DashiDynamicsShiftInstance as DDSI
open import DASHI.Physics.ShiftPotentialQuadraticEnergy as SPQE
open import DASHI.Physics.Closure.ShiftCollapseChainMDLCompatibility as Chain
open import DASHI.Physics.Closure.ShiftObservableSignaturePressureTestInstance as SPTI

------------------------------------------------------------------------
-- Bounded fixed-point perturbation classification on the live shift carrier.
--
-- This is the finite theorem earned by the current dynamics stack:
--
--   * the held point is fixed;
--   * start and next are transient perturbations with strict potential descent;
--   * the held point is the only marginal/stable class on this carrier;
--   * no relevant/growing class is inhabited;
--   * quadratic energy is non-increasing;
--   * the already-proved collapse/MDL chain remains attached as execution
--     evidence.
--
-- The word "linearized" is intentionally not used for the step below.  The
-- current carrier has no tangent space or derivative, so this module classifies
-- the exact finite step rather than pretending to have a Frechet linearization
-- or a conformal-field-theory theorem.

data PerturbationClass : Set where
  relevant : PerturbationClass
  marginal : PerturbationClass
  irrelevant : PerturbationClass

shiftPerturbationClass :
  SPTI.ShiftPressurePoint →
  PerturbationClass
shiftPerturbationClass SPTI.shiftStartPoint = irrelevant
shiftPerturbationClass SPTI.shiftNextPoint = irrelevant
shiftPerturbationClass SPTI.shiftHeldExitPoint = marginal

shiftPerturbationStep :
  SPTI.ShiftPressurePoint →
  SPTI.ShiftPressurePoint
shiftPerturbationStep = DDSI.shiftPressureAdvance

shiftFixedPoint : SPTI.ShiftPressurePoint
shiftFixedPoint = SPTI.shiftHeldExitPoint

ShiftFixedPointLaw : Set
ShiftFixedPointLaw =
  shiftPerturbationStep shiftFixedPoint ≡ shiftFixedPoint

ShiftIrrelevantStrictDescent : Set
ShiftIrrelevantStrictDescent =
  (s : SPTI.ShiftPressurePoint) →
  shiftPerturbationClass s ≡ irrelevant →
  DDSI.shiftHeldPotential (shiftPerturbationStep s)
    <
  DDSI.shiftHeldPotential s

ShiftMarginalStable : Set
ShiftMarginalStable =
  (s : SPTI.ShiftPressurePoint) →
  shiftPerturbationClass s ≡ marginal →
  shiftPerturbationStep s ≡ s

ShiftNoRelevantClass : Set
ShiftNoRelevantClass =
  (s : SPTI.ShiftPressurePoint) →
  shiftPerturbationClass s ≡ relevant →
  ⊥

ShiftQuadraticEnergyDescent : Set
ShiftQuadraticEnergyDescent =
  (s : SPTI.ShiftPressurePoint) →
  SPQE.shiftQuadraticEnergy (shiftPerturbationStep s)
    ≤
  SPQE.shiftQuadraticEnergy s

shiftFixedPointWitness : ShiftFixedPointLaw
shiftFixedPointWitness = DDSI.shiftHeldFixedPointWitness

shiftIrrelevantStrictDescentWitness :
  ShiftIrrelevantStrictDescent
shiftIrrelevantStrictDescentWitness SPTI.shiftStartPoint _ =
  DDSI.shiftStrictPotentialDescentWitness
    SPTI.shiftStartPoint
    DDSI.atStart
shiftIrrelevantStrictDescentWitness SPTI.shiftNextPoint _ =
  DDSI.shiftStrictPotentialDescentWitness
    SPTI.shiftNextPoint
    DDSI.atNext
shiftIrrelevantStrictDescentWitness SPTI.shiftHeldExitPoint ()

shiftMarginalStableWitness : ShiftMarginalStable
shiftMarginalStableWitness SPTI.shiftStartPoint ()
shiftMarginalStableWitness SPTI.shiftNextPoint ()
shiftMarginalStableWitness SPTI.shiftHeldExitPoint _ = refl

shiftNoRelevantClassWitness : ShiftNoRelevantClass
shiftNoRelevantClassWitness SPTI.shiftStartPoint ()
shiftNoRelevantClassWitness SPTI.shiftNextPoint ()
shiftNoRelevantClassWitness SPTI.shiftHeldExitPoint ()

shiftQuadraticEnergyDescentWitness :
  ShiftQuadraticEnergyDescent
shiftQuadraticEnergyDescentWitness =
  SPQE.shiftQuadraticDescentWitness

record ShiftFixedPointPerturbationClassification : Setω where
  field
    fixedPoint : SPTI.ShiftPressurePoint
    perturbationStep :
      SPTI.ShiftPressurePoint →
      SPTI.ShiftPressurePoint
    classify :
      SPTI.ShiftPressurePoint →
      PerturbationClass

    fixedPointLaw :
      perturbationStep fixedPoint ≡ fixedPoint

    irrelevantStrictDescent :
      (s : SPTI.ShiftPressurePoint) →
      classify s ≡ irrelevant →
      DDSI.shiftHeldPotential (perturbationStep s)
        <
      DDSI.shiftHeldPotential s

    marginalStable :
      (s : SPTI.ShiftPressurePoint) →
      classify s ≡ marginal →
      perturbationStep s ≡ s

    noRelevantClass :
      (s : SPTI.ShiftPressurePoint) →
      classify s ≡ relevant →
      ⊥

    quadraticEnergyDescent :
      (s : SPTI.ShiftPressurePoint) →
      SPQE.shiftQuadraticEnergy (perturbationStep s)
        ≤
      SPQE.shiftQuadraticEnergy s

    collapseMdlChain :
      Chain.ShiftCollapseChainMDLCompatibility

    nonClaimBoundary : List String

open ShiftFixedPointPerturbationClassification public

canonicalShiftFixedPointPerturbationClassification :
  ShiftFixedPointPerturbationClassification
canonicalShiftFixedPointPerturbationClassification =
  record
    { fixedPoint = shiftFixedPoint
    ; perturbationStep = shiftPerturbationStep
    ; classify = shiftPerturbationClass
    ; fixedPointLaw = shiftFixedPointWitness
    ; irrelevantStrictDescent = shiftIrrelevantStrictDescentWitness
    ; marginalStable = shiftMarginalStableWitness
    ; noRelevantClass = shiftNoRelevantClassWitness
    ; quadraticEnergyDescent = shiftQuadraticEnergyDescentWitness
    ; collapseMdlChain =
        Chain.canonicalShiftCollapseChainMDLCompatibility
    ; nonClaimBoundary =
        "ShiftFixedPointPerturbationClassification classifies the exact bounded shift step only"
        ∷ "start and next are irrelevant because the supplied potential decreases strictly"
        ∷ "held is marginal only in the finite fixed-point sense that the exact step leaves it unchanged"
        ∷ "no relevant class is inhabited on the current three-point carrier"
        ∷ "quadraticEnergyDescent reuses the existing finite scalar quadratic-energy package"
        ∷ "collapseMdlChain keeps the pressure-depth, potential, and execution-receipt layers coordinated"
        ∷ "No tangent space, Frechet derivative, scaling dimension, conformal algebra, continuum RG, or CFT theorem is claimed"
        ∷ "No global equality between collapse depth, potential, quadratic energy, and MDL is claimed"
        ∷ []
    }
