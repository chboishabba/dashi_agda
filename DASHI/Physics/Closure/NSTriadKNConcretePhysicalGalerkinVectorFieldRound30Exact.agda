module DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact where

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
-- Connect the concrete viscous-plus-exhaustive-quadratic coefficient fold to
-- the Round-30 dependent vector-field interface.  A state-indexed builder may
-- choose the finite cutoff/system data, but it must prove that the integer
-- embedding is the fixed embedding of the dependent carrier.  The output list
-- is then constructed mode by mode from the literal formula, transported only
-- across that embedding equality, and accompanied by a witness recovering the
-- exact source mode and exact coefficient value.
--
-- Consequently `concretePhysicalGalerkinVectorField` is not a raw supplied
-- field: every returned coefficient is definitionally traced to
--
--   -nu |k|^2 u(k) + sum_{p+q=k} -i P_k[(u(p) dot q)u(q)].
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using
  (cong; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinVectorFieldRound30Exact as Field

record StateIndexedPhysicalGalerkinSystem
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    physicalSystemAt :
      State.ReconstructedPhysicalState F E →
      Coefficient.PhysicalFiniteComplex3GalerkinSystem F

    embeddingExact : ∀ state →
      Audit.integerEmbedding
        (Coefficient.finiteSystem (physicalSystemAt state))
      ≡ E

open StateIndexedPhysicalGalerkinSystem public

transportCoefficient :
  ∀ {r} {F : C3.RealField r}
    {left right : C3.IntegerEmbedding F} →
  left ≡ right →
  Phase.TransverseModeCoefficient F left →
  Phase.TransverseModeCoefficient F right
transportCoefficient equality coefficient =
  subst (Phase.TransverseModeCoefficient _) equality coefficient

transportCoefficientMode :
  ∀ {r} {F : C3.RealField r}
    {left right : C3.IntegerEmbedding F}
    (equality : left ≡ right)
    (coefficient : Phase.TransverseModeCoefficient F left) →
  Phase.coefficientMode (transportCoefficient equality coefficient)
  ≡ Phase.coefficientMode coefficient
transportCoefficientMode refl coefficient = refl

transportCoefficientValue :
  ∀ {r} {F : C3.RealField r}
    {left right : C3.IntegerEmbedding F}
    (equality : left ≡ right)
    (coefficient : Phase.TransverseModeCoefficient F left) →
  Phase.coefficientValue (transportCoefficient equality coefficient)
  ≡ Phase.coefficientValue coefficient
transportCoefficientValue refl coefficient = refl

mapConcreteCoefficients :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (builder : StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (source : List Z3.FourierMode) →
  (∀ mode → mode Cube.∈ source →
    mode Cube.∈ Audit.modes
      (Coefficient.finiteSystem (physicalSystemAt builder state))) →
  List (Phase.TransverseModeCoefficient F E)
mapConcreteCoefficients builder state [] sourceIncluded = []
mapConcreteCoefficients builder state (mode ∷ rest) sourceIncluded =
  transportCoefficient (embeddingExact builder state)
    (Coefficient.literalTransverseCoefficient
      (physicalSystemAt builder state) mode
      (sourceIncluded mode (Cube.here refl)))
  ∷ mapConcreteCoefficients builder state rest
      (λ selected member → sourceIncluded selected (Cube.there member))

concreteOutputCoefficients :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  StateIndexedPhysicalGalerkinSystem F E →
  State.ReconstructedPhysicalState F E →
  List (Phase.TransverseModeCoefficient F E)
concreteOutputCoefficients builder state =
  mapConcreteCoefficients builder state
    (Audit.modes
      (Coefficient.finiteSystem (physicalSystemAt builder state)))
    (λ mode member → member)

record LiteralCoefficientWitness
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (builder : StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (coefficient : Phase.TransverseModeCoefficient F E) : Set r where
  field
    sourceMode : Z3.FourierMode
    sourceMembership :
      sourceMode Cube.∈ Audit.modes
        (Coefficient.finiteSystem (physicalSystemAt builder state))
    modeExact : Phase.coefficientMode coefficient ≡ sourceMode
    valueExact :
      Phase.coefficientValue coefficient
      ≡ Coefficient.literalViscousQuadraticCoefficient
          (physicalSystemAt builder state) sourceMode

open LiteralCoefficientWitness public

mappedConcreteCoefficientWitness :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (builder : StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    (source : List Z3.FourierMode)
    (sourceIncluded : ∀ mode → mode Cube.∈ source →
      mode Cube.∈ Audit.modes
        (Coefficient.finiteSystem (physicalSystemAt builder state)))
    coefficient →
  State._∈_ coefficient
    (mapConcreteCoefficients builder state source sourceIncluded) →
  LiteralCoefficientWitness builder state coefficient
mappedConcreteCoefficientWitness builder state [] sourceIncluded coefficient ()
mappedConcreteCoefficientWitness builder state (mode ∷ rest)
    sourceIncluded coefficient (State.here coefficientExact) = record
  { sourceMode = mode
  ; sourceMembership = sourceIncluded mode (Cube.here refl)
  ; modeExact = trans
      (cong Phase.coefficientMode coefficientExact)
      (transportCoefficientMode (embeddingExact builder state)
        (Coefficient.literalTransverseCoefficient
          (physicalSystemAt builder state) mode
          (sourceIncluded mode (Cube.here refl))))
  ; valueExact = trans
      (cong Phase.coefficientValue coefficientExact)
      (transportCoefficientValue (embeddingExact builder state)
        (Coefficient.literalTransverseCoefficient
          (physicalSystemAt builder state) mode
          (sourceIncluded mode (Cube.here refl))))
  }
mappedConcreteCoefficientWitness builder state (mode ∷ rest)
    sourceIncluded coefficient (State.there member) =
  mappedConcreteCoefficientWitness builder state rest
    (λ selected selectedMember →
      sourceIncluded selected (Cube.there selectedMember))
    coefficient member

concreteOutputCoefficientWitness :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (builder : StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient (concreteOutputCoefficients builder state) →
  LiteralCoefficientWitness builder state coefficient
concreteOutputCoefficientWitness builder state =
  mappedConcreteCoefficientWitness builder state
    (Audit.modes
      (Coefficient.finiteSystem (physicalSystemAt builder state)))
    (λ mode member → member)

concreteOutputModesNonzero :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    (builder : StateIndexedPhysicalGalerkinSystem F E)
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  State._∈_ coefficient (concreteOutputCoefficients builder state) →
  Z3.NonZeroMode (Phase.coefficientMode coefficient)
concreteOutputModesNonzero builder state coefficient member =
  let
    witness = concreteOutputCoefficientWitness
      builder state coefficient member
    sourceNonzero = Coefficient.retainedModeNonzero
      (physicalSystemAt builder state)
      (sourceMode witness)
      (sourceMembership witness)
  in
  subst Z3.NonZeroMode (sym (modeExact witness)) sourceNonzero

concreteLiteralPhysicalGalerkinProducer :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  StateIndexedPhysicalGalerkinSystem F E →
  Field.LiteralPhysicalGalerkinProducer F E
concreteLiteralPhysicalGalerkinProducer builder = record
  { Field.LiteralPhysicalGalerkinProducer.outputCoefficients =
      concreteOutputCoefficients builder
  ; Field.LiteralPhysicalGalerkinProducer.outputModesNonzero =
      concreteOutputModesNonzero builder
  ; Field.LiteralPhysicalGalerkinProducer.LiteralRawCoefficient =
      LiteralCoefficientWitness builder
  ; Field.LiteralPhysicalGalerkinProducer.outputIsLiteralViscousPlusQuadratic =
      concreteOutputCoefficientWitness builder
  }

concretePhysicalGalerkinVectorField :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F} →
  StateIndexedPhysicalGalerkinSystem F E →
  State.ReconstructedPhysicalState F E →
  State.ReconstructedPhysicalState F E
concretePhysicalGalerkinVectorField builder =
  Field.physicalGalerkinVectorField
    (concreteLiteralPhysicalGalerkinProducer builder)

concretePhysicalGalerkinVectorFieldClosed : Bool
concretePhysicalGalerkinVectorFieldClosed = true

concretePhysicalGalerkinVectorFieldClosedIsTrue :
  concretePhysicalGalerkinVectorFieldClosed ≡ true
concretePhysicalGalerkinVectorFieldClosedIsTrue = refl
