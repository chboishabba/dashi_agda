module DASHI.Physics.Closure.NavierStokesWeakSolutionInterface where

open import Agda.Primitive using (Set)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Carrier-level incompressible Navier-Stokes weak-solution interface.
--
-- This module supplies a concrete finite carrier-level interface lane for
-- weak formulation, divergence-free constraint, Leray projection, and the
-- Leray-Hopf energy inequality shape.  The canonical instance is the
-- singleton carrier: it is intentionally finite and definitionally total,
-- so every law below is witnessed by refl/tt rather than by postulates.

data NavierStokesWeakSolutionInterfaceStatus : Set where
  finiteCarrierWeakLerayInterfaceRecordedContinuumOpen :
    NavierStokesWeakSolutionInterfaceStatus

record NavierStokesCarrier : Set₁ where
  field
    Time :
      Set

    DomainPoint :
      Set

    Scalar :
      Set

    Velocity :
      Set

    Pressure :
      Set

    TestVelocity :
      Set

    Force :
      Set

    initialTime :
      Time

    scalarZero :
      Scalar

    scalarAdd :
      Scalar →
      Scalar →
      Scalar

    scalarNeg :
      Scalar →
      Scalar

    scalarLeq :
      Scalar →
      Scalar →
      Set

    scalarLeqRefl :
      (x : Scalar) →
      scalarLeq x x

    viscosity :
      Scalar

    zeroVelocity :
      Velocity

    initialVelocity :
      Velocity

    zeroPressure :
      Pressure

    zeroForce :
      Force

    velocityAdd :
      Velocity →
      Velocity →
      Velocity

    velocityScale :
      Scalar →
      Velocity →
      Velocity

    timeDerivativePairing :
      Velocity →
      TestVelocity →
      Scalar

    viscosityPairing :
      Velocity →
      TestVelocity →
      Scalar

    convectionPairing :
      Velocity →
      Velocity →
      TestVelocity →
      Scalar

    pressureGradientPairing :
      Pressure →
      TestVelocity →
      Scalar

    forcePairing :
      Force →
      TestVelocity →
      Scalar

    divergencePairing :
      Velocity →
      TestVelocity →
      Scalar

    carrierBoundary :
      List String

weakMomentumResidual :
  (carrier : NavierStokesCarrier) →
  NavierStokesCarrier.Velocity carrier →
  NavierStokesCarrier.Pressure carrier →
  NavierStokesCarrier.Force carrier →
  NavierStokesCarrier.TestVelocity carrier →
  NavierStokesCarrier.Scalar carrier
weakMomentumResidual carrier u p f φ =
  NavierStokesCarrier.scalarAdd carrier
    (NavierStokesCarrier.timeDerivativePairing carrier u φ)
    (NavierStokesCarrier.scalarAdd carrier
      (NavierStokesCarrier.viscosityPairing carrier u φ)
      (NavierStokesCarrier.scalarAdd carrier
        (NavierStokesCarrier.convectionPairing carrier u u φ)
        (NavierStokesCarrier.scalarAdd carrier
          (NavierStokesCarrier.pressureGradientPairing carrier p φ)
          (NavierStokesCarrier.scalarNeg carrier
            (NavierStokesCarrier.forcePairing carrier f φ)))))

canonicalFiniteNavierStokesCarrier :
  NavierStokesCarrier
canonicalFiniteNavierStokesCarrier =
  record
    { Time =
        ⊤
    ; DomainPoint =
        ⊤
    ; Scalar =
        ⊤
    ; Velocity =
        ⊤
    ; Pressure =
        ⊤
    ; TestVelocity =
        ⊤
    ; Force =
        ⊤
    ; initialTime =
        tt
    ; scalarZero =
        tt
    ; scalarAdd =
        λ _ _ → tt
    ; scalarNeg =
        λ _ → tt
    ; scalarLeq =
        λ _ _ → ⊤
    ; scalarLeqRefl =
        λ _ → tt
    ; viscosity =
        tt
    ; zeroVelocity =
        tt
    ; initialVelocity =
        tt
    ; zeroPressure =
        tt
    ; zeroForce =
        tt
    ; velocityAdd =
        λ _ _ → tt
    ; velocityScale =
        λ _ _ → tt
    ; timeDerivativePairing =
        λ _ _ → tt
    ; viscosityPairing =
        λ _ _ → tt
    ; convectionPairing =
        λ _ _ _ → tt
    ; pressureGradientPairing =
        λ _ _ → tt
    ; forcePairing =
        λ _ _ → tt
    ; divergencePairing =
        λ _ _ → tt
    ; carrierBoundary =
        "The canonical carrier is the inhabited finite singleton carrier"
        ∷ "All weak-form pairings are total carrier-level operations"
        ∷ "The carrier is a typed interface witness only, not a continuum PDE theorem"
        ∷ []
    }

record NavierStokesDivergenceFreeInterface
  (carrier : NavierStokesCarrier) : Set₁ where
  open NavierStokesCarrier carrier

  field
    divergenceValue :
      Velocity →
      Scalar

    isDivergenceFree :
      Velocity →
      Set

    initialVelocityDivergenceFree :
      isDivergenceFree initialVelocity

    divergenceValueZeroForInitialVelocity :
      divergenceValue initialVelocity ≡ scalarZero

    testVelocityDivergenceFree :
      TestVelocity →
      Set

    canonicalTestVelocity :
      TestVelocity

    canonicalTestVelocityDivergenceFree :
      testVelocityDivergenceFree canonicalTestVelocity

    divergenceFreeImpliesWeakDivergenceZero :
      (u : Velocity) →
      isDivergenceFree u →
      (φ : TestVelocity) →
      divergencePairing u φ ≡ scalarZero

    divergenceFreeBoundary :
      List String

canonicalDivergenceFreeInterface :
  NavierStokesDivergenceFreeInterface canonicalFiniteNavierStokesCarrier
canonicalDivergenceFreeInterface =
  record
    { divergenceValue =
        λ _ → tt
    ; isDivergenceFree =
        λ _ → ⊤
    ; initialVelocityDivergenceFree =
        tt
    ; divergenceValueZeroForInitialVelocity =
        refl
    ; testVelocityDivergenceFree =
        λ _ → ⊤
    ; canonicalTestVelocity =
        tt
    ; canonicalTestVelocityDivergenceFree =
        tt
    ; divergenceFreeImpliesWeakDivergenceZero =
        λ _ _ _ → refl
    ; divergenceFreeBoundary =
        "Divergence-free is an inhabited carrier-level predicate"
        ∷ "The selected initial velocity has zero divergence by definitional equality"
        ∷ "Weak divergence vanishes against every selected test velocity on this finite carrier"
        ∷ []
    }

record NavierStokesDiscreteLerayHodgeDecomposition
  (carrier : NavierStokesCarrier)
  (divergenceFree :
    NavierStokesDivergenceFreeInterface carrier) : Set₁ where
  open NavierStokesCarrier carrier
  open NavierStokesDivergenceFreeInterface divergenceFree

  field
    lerayPotential :
      Velocity →
      Pressure

    gradient :
      Pressure →
      Velocity

    velocitySubtract :
      Velocity →
      Velocity →
      Velocity

    scalarSubtract :
      Scalar →
      Scalar →
      Scalar

    laplacian :
      Pressure →
      Scalar

    divergenceOfGradient :
      Pressure →
      Scalar

    finiteCarrierPointwiseDivergence :
      Velocity →
      DomainPoint →
      Scalar

    finiteCarrierDivergenceAgreesWithValue :
      (u : Velocity) →
      (x : DomainPoint) →
      finiteCarrierPointwiseDivergence u x ≡ divergenceValue u

    poissonEquation :
      (u : Velocity) →
      laplacian (lerayPotential u) ≡ divergenceValue u

    laplacianIsDivergenceOfGradient :
      (φ : Pressure) →
      divergenceOfGradient φ ≡ laplacian φ

    divergenceSubtractGradientLaw :
      (u : Velocity) →
      divergenceValue (velocitySubtract u (gradient (lerayPotential u)))
      ≡
      scalarSubtract
        (divergenceValue u)
        (divergenceOfGradient (lerayPotential u))

    poissonSubtractionCancels :
      (u : Velocity) →
      scalarSubtract
        (divergenceValue u)
        (laplacian (lerayPotential u))
      ≡
      scalarZero

    finiteCarrierLerayDivergenceZero :
      (u : Velocity) →
      (x : DomainPoint) →
      finiteCarrierPointwiseDivergence
        (velocitySubtract u (gradient (lerayPotential u)))
        x
      ≡
      scalarZero

    hodgeDecompositionBoundary :
      List String

canonicalDiscreteLerayHodgeDecomposition :
  NavierStokesDiscreteLerayHodgeDecomposition
    canonicalFiniteNavierStokesCarrier
    canonicalDivergenceFreeInterface
canonicalDiscreteLerayHodgeDecomposition =
  record
    { lerayPotential =
        λ _ → tt
    ; gradient =
        λ _ → tt
    ; velocitySubtract =
        λ _ _ → tt
    ; scalarSubtract =
        λ _ _ → tt
    ; laplacian =
        λ _ → tt
    ; divergenceOfGradient =
        λ _ → tt
    ; finiteCarrierPointwiseDivergence =
        λ _ _ → tt
    ; finiteCarrierDivergenceAgreesWithValue =
        λ _ _ → refl
    ; poissonEquation =
        λ _ → refl
    ; laplacianIsDivergenceOfGradient =
        λ _ → refl
    ; divergenceSubtractGradientLaw =
        λ _ → refl
    ; poissonSubtractionCancels =
        λ _ → refl
    ; finiteCarrierLerayDivergenceZero =
        λ _ _ → refl
    ; hodgeDecompositionBoundary =
        "Discrete Leray potential solves Delta phi = div u on the selected finite carrier"
        ∷ "The selected Laplacian is divergence-of-gradient on this carrier"
        ∷ "The finite-carrier proof checks div (u - grad phi) = 0 pointwise"
        ∷ "This is the finite carrier Hodge/Leray decomposition interface, not a continuum elliptic regularity theorem"
        ∷ []
    }

record NavierStokesLerayProjectionInterface
  (carrier : NavierStokesCarrier)
  (divergenceFree :
    NavierStokesDivergenceFreeInterface carrier) : Set₁ where
  open NavierStokesCarrier carrier
  open NavierStokesDivergenceFreeInterface divergenceFree

  field
    discreteHodgeDecomposition :
      NavierStokesDiscreteLerayHodgeDecomposition carrier divergenceFree

    projectVelocity :
      Velocity →
      Velocity

    pressureProjection :
      Velocity →
      Pressure

    projectVelocityIsVelocityMinusGradientPotential :
      (u : Velocity) →
      projectVelocity u
      ≡
      NavierStokesDiscreteLerayHodgeDecomposition.velocitySubtract
        discreteHodgeDecomposition
        u
        (NavierStokesDiscreteLerayHodgeDecomposition.gradient
          discreteHodgeDecomposition
          (NavierStokesDiscreteLerayHodgeDecomposition.lerayPotential
            discreteHodgeDecomposition
            u))

    pressureProjectionIsLerayPotential :
      (u : Velocity) →
      pressureProjection u
      ≡
      NavierStokesDiscreteLerayHodgeDecomposition.lerayPotential
        discreteHodgeDecomposition
        u

    pressureProjectionSolvesPoisson :
      (u : Velocity) →
      NavierStokesDiscreteLerayHodgeDecomposition.laplacian
        discreteHodgeDecomposition
        (pressureProjection u)
      ≡
      divergenceValue u

    projectedDivergenceValueZero :
      (u : Velocity) →
      divergenceValue (projectVelocity u) ≡ scalarZero

    projectedPointwiseDivergenceZero :
      (u : Velocity) →
      (x : DomainPoint) →
      NavierStokesDiscreteLerayHodgeDecomposition.finiteCarrierPointwiseDivergence
        discreteHodgeDecomposition
        (projectVelocity u)
        x
      ≡
      scalarZero

    projectedVelocityDivergenceFree :
      (u : Velocity) →
      isDivergenceFree (projectVelocity u)

    projectionIdempotent :
      (u : Velocity) →
      projectVelocity (projectVelocity u) ≡ projectVelocity u

    projectionFixesDivergenceFreeVelocity :
      (u : Velocity) →
      isDivergenceFree u →
      projectVelocity u ≡ u

    projectionFixesInitialVelocity :
      projectVelocity initialVelocity ≡ initialVelocity

    pressureGradientVanishesOnDivergenceFreeTests :
      (u : Velocity) →
      (φ : TestVelocity) →
      testVelocityDivergenceFree φ →
      pressureGradientPairing (pressureProjection u) φ ≡ scalarZero

    lerayBoundary :
      List String

canonicalLerayProjectionInterface :
  NavierStokesLerayProjectionInterface
    canonicalFiniteNavierStokesCarrier
    canonicalDivergenceFreeInterface
canonicalLerayProjectionInterface =
  record
    { discreteHodgeDecomposition =
        canonicalDiscreteLerayHodgeDecomposition
    ; projectVelocity =
        λ _ → tt
    ; pressureProjection =
        λ _ → tt
    ; projectVelocityIsVelocityMinusGradientPotential =
        λ _ → refl
    ; pressureProjectionIsLerayPotential =
        λ _ → refl
    ; pressureProjectionSolvesPoisson =
        λ _ → refl
    ; projectedDivergenceValueZero =
        λ _ → refl
    ; projectedPointwiseDivergenceZero =
        λ _ _ → refl
    ; projectedVelocityDivergenceFree =
        λ _ → tt
    ; projectionIdempotent =
        λ _ → refl
    ; projectionFixesDivergenceFreeVelocity =
        λ _ _ → refl
    ; projectionFixesInitialVelocity =
        refl
    ; pressureGradientVanishesOnDivergenceFreeTests =
        λ _ _ _ → refl
    ; lerayBoundary =
        "The Leray projection is the concrete finite-carrier map P_sigma u = u - grad phi"
        ∷ "The pressure projection is the Leray potential phi solving Delta phi = div u"
        ∷ "Projected velocities have zero divergence explicitly at every point of the finite carrier"
        ∷ "Pressure gradients vanish on selected divergence-free tests"
        ∷ []
    }

record NavierStokesWeakFormulationInterface
  (carrier : NavierStokesCarrier)
  (divergenceFree :
    NavierStokesDivergenceFreeInterface carrier)
  (leray :
    NavierStokesLerayProjectionInterface carrier divergenceFree) : Set₁ where
  open NavierStokesCarrier carrier
  open NavierStokesDivergenceFreeInterface divergenceFree
  open NavierStokesLerayProjectionInterface leray

  field
    velocityTrajectory :
      Time →
      Velocity

    pressureTrajectory :
      Time →
      Pressure

    forceTrajectory :
      Time →
      Force

    trajectoryDivergenceFree :
      (t : Time) →
      isDivergenceFree (velocityTrajectory t)

    weakMomentumBalance :
      (t : Time) →
      (φ : TestVelocity) →
      testVelocityDivergenceFree φ →
      weakMomentumResidual
        carrier
        (velocityTrajectory t)
        (pressureTrajectory t)
        (forceTrajectory t)
        φ
      ≡
      scalarZero

    weakInitialCondition :
      velocityTrajectory initialTime ≡ initialVelocity

    lerayProjectionCompatibility :
      (t : Time) →
      projectVelocity (velocityTrajectory t) ≡ velocityTrajectory t

    weakFormulationBoundary :
      List String

canonicalWeakFormulationInterface :
  NavierStokesWeakFormulationInterface
    canonicalFiniteNavierStokesCarrier
    canonicalDivergenceFreeInterface
    canonicalLerayProjectionInterface
canonicalWeakFormulationInterface =
  record
    { velocityTrajectory =
        λ _ → tt
    ; pressureTrajectory =
        λ _ → tt
    ; forceTrajectory =
        λ _ → tt
    ; trajectoryDivergenceFree =
        λ _ → tt
    ; weakMomentumBalance =
        λ _ _ _ → refl
    ; weakInitialCondition =
        refl
    ; lerayProjectionCompatibility =
        λ _ → refl
    ; weakFormulationBoundary =
        "The weak momentum equation is a carrier-level residual identity"
        ∷ "The selected velocity trajectory is divergence-free at every finite carrier time"
        ∷ "The selected velocity trajectory is fixed by the concrete Leray projection"
        ∷ []
    }

record NavierStokesLerayHopfWeakSolutionInterface
  (carrier : NavierStokesCarrier)
  (divergenceFree :
    NavierStokesDivergenceFreeInterface carrier)
  (leray :
    NavierStokesLerayProjectionInterface carrier divergenceFree)
  (weakFormulation :
    NavierStokesWeakFormulationInterface
      carrier
      divergenceFree
      leray) : Set₁ where
  open NavierStokesCarrier carrier
  open NavierStokesDivergenceFreeInterface divergenceFree
  open NavierStokesWeakFormulationInterface weakFormulation

  field
    energy :
      Time →
      Scalar

    enstrophy :
      Time →
      Scalar

    dissipation :
      Time →
      Scalar

    energyInequality :
      (s t : Time) →
      scalarLeq (energy t) (scalarAdd (energy s) (dissipation s))

    lerayHopfDivergenceFree :
      (t : Time) →
      isDivergenceFree (velocityTrajectory t)

    lerayHopfWeakMomentumBalance :
      (t : Time) →
      (φ : TestVelocity) →
      testVelocityDivergenceFree φ →
      weakMomentumResidual
        carrier
        (velocityTrajectory t)
        (pressureTrajectory t)
        (forceTrajectory t)
        φ
      ≡
      scalarZero

    lerayHopfBoundary :
      List String

canonicalLerayHopfWeakSolutionInterface :
  NavierStokesLerayHopfWeakSolutionInterface
    canonicalFiniteNavierStokesCarrier
    canonicalDivergenceFreeInterface
    canonicalLerayProjectionInterface
    canonicalWeakFormulationInterface
canonicalLerayHopfWeakSolutionInterface =
  record
    { energy =
        λ _ → tt
    ; enstrophy =
        λ _ → tt
    ; dissipation =
        λ _ → tt
    ; energyInequality =
        λ _ _ → tt
    ; lerayHopfDivergenceFree =
        λ _ → tt
    ; lerayHopfWeakMomentumBalance =
        λ _ _ _ → refl
    ; lerayHopfBoundary =
        "The Leray-Hopf lane records a concrete weak solution interface on the finite singleton carrier"
        ∷ "Energy, enstrophy, and dissipation are total carrier-level observables"
        ∷ "The energy inequality is inhabited on the selected carrier order"
        ∷ []
    }

record NavierStokesWeakSolutionInterfaceReceipt : Set₁ where
  field
    status :
      NavierStokesWeakSolutionInterfaceStatus

    carrier :
      NavierStokesCarrier

    carrierIsCanonical :
      carrier ≡ canonicalFiniteNavierStokesCarrier

    divergenceFreeInterface :
      NavierStokesDivergenceFreeInterface canonicalFiniteNavierStokesCarrier

    divergenceFreeInterfaceIsCanonical :
      divergenceFreeInterface ≡ canonicalDivergenceFreeInterface

    lerayProjectionInterface :
      NavierStokesLerayProjectionInterface
        canonicalFiniteNavierStokesCarrier
        canonicalDivergenceFreeInterface

    lerayProjectionInterfaceIsCanonical :
      lerayProjectionInterface ≡ canonicalLerayProjectionInterface

    weakFormulationInterface :
      NavierStokesWeakFormulationInterface
        canonicalFiniteNavierStokesCarrier
        canonicalDivergenceFreeInterface
        canonicalLerayProjectionInterface

    weakFormulationInterfaceIsCanonical :
      weakFormulationInterface ≡ canonicalWeakFormulationInterface

    lerayHopfWeakSolutionInterface :
      NavierStokesLerayHopfWeakSolutionInterface
        canonicalFiniteNavierStokesCarrier
        canonicalDivergenceFreeInterface
        canonicalLerayProjectionInterface
        canonicalWeakFormulationInterface

    lerayHopfWeakSolutionInterfaceIsCanonical :
      lerayHopfWeakSolutionInterface
      ≡
      canonicalLerayHopfWeakSolutionInterface

    carrierWeakFormulationRecorded :
      Bool

    carrierWeakFormulationRecordedIsTrue :
      carrierWeakFormulationRecorded ≡ true

    continuumRegularityPromoted :
      Bool

    continuumRegularityPromotedIsFalse :
      continuumRegularityPromoted ≡ false

    receiptBoundary :
      List String

canonicalNavierStokesWeakSolutionInterfaceReceipt :
  NavierStokesWeakSolutionInterfaceReceipt
canonicalNavierStokesWeakSolutionInterfaceReceipt =
  record
    { status =
        finiteCarrierWeakLerayInterfaceRecordedContinuumOpen
    ; carrier =
        canonicalFiniteNavierStokesCarrier
    ; carrierIsCanonical =
        refl
    ; divergenceFreeInterface =
        canonicalDivergenceFreeInterface
    ; divergenceFreeInterfaceIsCanonical =
        refl
    ; lerayProjectionInterface =
        canonicalLerayProjectionInterface
    ; lerayProjectionInterfaceIsCanonical =
        refl
    ; weakFormulationInterface =
        canonicalWeakFormulationInterface
    ; weakFormulationInterfaceIsCanonical =
        refl
    ; lerayHopfWeakSolutionInterface =
        canonicalLerayHopfWeakSolutionInterface
    ; lerayHopfWeakSolutionInterfaceIsCanonical =
        refl
    ; carrierWeakFormulationRecorded =
        true
    ; carrierWeakFormulationRecordedIsTrue =
        refl
    ; continuumRegularityPromoted =
        false
    ; continuumRegularityPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Concrete finite carrier-level Navier-Stokes weak formulation is recorded"
        ∷ "Concrete divergence-free and Leray projection interfaces are recorded"
        ∷ "Concrete Leray-Hopf energy inequality shape is recorded"
        ∷ "This receipt does not promote finite carrier evidence to continuum regularity"
        ∷ []
    }

canonicalWeakMomentumBalanceAtInitialTime :
  NavierStokesWeakFormulationInterface.weakMomentumBalance
    canonicalWeakFormulationInterface
    tt
    tt
    tt
  ≡
  refl
canonicalWeakMomentumBalanceAtInitialTime =
  refl

canonicalLerayHopfEnergyInequalityAtInitialTime :
  NavierStokesLerayHopfWeakSolutionInterface.energyInequality
    canonicalLerayHopfWeakSolutionInterface
    tt
    tt
  ≡
  tt
canonicalLerayHopfEnergyInequalityAtInitialTime =
  refl

canonicalLerayProjectionIsVelocityMinusGradientPotential :
  NavierStokesLerayProjectionInterface.projectVelocityIsVelocityMinusGradientPotential
    canonicalLerayProjectionInterface
    tt
  ≡
  refl
canonicalLerayProjectionIsVelocityMinusGradientPotential =
  refl

canonicalLerayPressureProjectionSolvesPoisson :
  NavierStokesLerayProjectionInterface.pressureProjectionSolvesPoisson
    canonicalLerayProjectionInterface
    tt
  ≡
  refl
canonicalLerayPressureProjectionSolvesPoisson =
  refl

canonicalLerayProjectedDivergenceValueZero :
  NavierStokesLerayProjectionInterface.projectedDivergenceValueZero
    canonicalLerayProjectionInterface
    tt
  ≡
  refl
canonicalLerayProjectedDivergenceValueZero =
  refl

canonicalLerayProjectedPointwiseDivergenceZero :
  NavierStokesLerayProjectionInterface.projectedPointwiseDivergenceZero
    canonicalLerayProjectionInterface
    tt
    tt
  ≡
  refl
canonicalLerayProjectedPointwiseDivergenceZero =
  refl
