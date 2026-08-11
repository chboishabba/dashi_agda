module DASHI.Physics.Closure.NSTriadKNFixedCutoffSupportInvariantRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Turn the remaining Round-34 F1 support obligation into an invariance
-- theorem.  A reconstructed physical state stores one coefficient per chosen
-- positive reality representative; the negative sheet is reconstructed by
-- conjugation.  The older generic concrete vector field mapped over the full
-- retained mode list, which is too coarse for proving that this representative
-- carrier itself is invariant.
--
-- Here we map the literal viscous-plus-quadratic coefficient only over the
-- state's existing positive representatives.  Every output coefficient is the
-- exact Round-30 Galerkin right-hand side at the same Fourier label and is
-- transverse by construction.  We prove that the complete reconstructed
-- positive/negative mode list is exactly unchanged.  Therefore a state whose
-- reconstructed support is the literal nonzero cutoff cube has a derivative
-- in that same fixed-cutoff support fibre.
--
-- This closes support tangency, zero-mode exclusion, and transverse/reality
-- typing.  It does not yet prove that the derivative preserves Round-33
-- positive/negative overlap compatibility; that remaining statement is the
-- literal Fourier reality law for the nonlinear coefficient.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; subst; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteCutoffCubeCarrier as Cube
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNConcretePhysicalGalerkinVectorFieldRound30Exact as Concrete
import DASHI.Physics.Closure.NSTriadKNSameCarrierSameObjectRound31Exact as Same
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Cutoff

positiveModeInOrbitModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {coefficients : List (Phase.TransverseModeCoefficient F E)}
    {coefficient} →
  coefficient State.∈ coefficients →
  Phase.coefficientMode coefficient Cube.∈ Cutoff.orbitModes coefficients
positiveModeInOrbitModes {coefficients = []} ()
positiveModeInOrbitModes {coefficients = head ∷ rest}
    {coefficient} (State.here equality) =
  Cube.here (cong Phase.coefficientMode equality)
positiveModeInOrbitModes {coefficients = head ∷ rest}
    {coefficient} (State.there member) =
  Cube.there (Cube.there (positiveModeInOrbitModes member))

positiveModeInReconstructedModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E)
    coefficient →
  coefficient State.∈ State.positiveOrbitCoefficients state →
  Phase.coefficientMode coefficient Cube.∈ Same.reconstructedStateModes state
positiveModeInReconstructedModes state coefficient member =
  subst
    (λ modes → Phase.coefficientMode coefficient Cube.∈ modes)
    (sym (Cutoff.reconstructedStateModesExact state))
    (positiveModeInOrbitModes member)

mapPositiveLiteralCoefficients :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  (datum : Cutoff.CutoffSameObjectDatum F E state) →
  (source : List (Phase.TransverseModeCoefficient F E)) →
  (∀ coefficient → coefficient State.∈ source →
    coefficient State.∈ State.positiveOrbitCoefficients state) →
  List (Phase.TransverseModeCoefficient F E)
mapPositiveLiteralCoefficients datum [] include = []
mapPositiveLiteralCoefficients {state = state}
    datum (coefficient ∷ rest) include =
  Concrete.transportCoefficient
    (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
    (Coefficient.literalTransverseCoefficient
      (Cutoff.canonicalPhysicalFiniteSystem datum)
      (Phase.coefficientMode coefficient)
      (positiveModeInReconstructedModes
        state coefficient (include coefficient (State.here refl))))
  ∷ mapPositiveLiteralCoefficients datum rest
      (λ selected member → include selected (State.there member))

positiveLiteralOutputCoefficients :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  Cutoff.CutoffSameObjectDatum F E state →
  List (Phase.TransverseModeCoefficient F E)
positiveLiteralOutputCoefficients {state = state} datum =
  mapPositiveLiteralCoefficients datum
    (State.positiveOrbitCoefficients state)
    (λ coefficient member → member)

record PositiveLiteralCoefficientWitness
    {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state)
    (output : Phase.TransverseModeCoefficient F E) : Set r where
  field
    source : Phase.TransverseModeCoefficient F E
    sourceMember : source State.∈ State.positiveOrbitCoefficients state
    modeExact :
      Phase.coefficientMode output ≡ Phase.coefficientMode source
    valueExact :
      Phase.coefficientValue output
      ≡ Coefficient.literalViscousQuadraticCoefficient
          (Cutoff.canonicalPhysicalFiniteSystem datum)
          (Phase.coefficientMode source)

open PositiveLiteralCoefficientWitness public

mappedPositiveLiteralWitness :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state)
    (sourceList : List (Phase.TransverseModeCoefficient F E))
    (include : ∀ coefficient → coefficient State.∈ sourceList →
      coefficient State.∈ State.positiveOrbitCoefficients state)
    output →
  output State.∈ mapPositiveLiteralCoefficients datum sourceList include →
  PositiveLiteralCoefficientWitness datum output
mappedPositiveLiteralWitness datum [] include output ()
mappedPositiveLiteralWitness {state = state}
    datum (sourceHead ∷ rest) include output
    (State.here outputExact) = record
  { source = sourceHead
  ; sourceMember = include sourceHead (State.here refl)
  ; modeExact = trans
      (cong Phase.coefficientMode outputExact)
      (Concrete.transportCoefficientMode
        (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
        literalHead)
  ; valueExact = trans
      (cong Phase.coefficientValue outputExact)
      (Concrete.transportCoefficientValue
        (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
        literalHead)
  }
  where
  literalHead =
    Coefficient.literalTransverseCoefficient
      (Cutoff.canonicalPhysicalFiniteSystem datum)
      (Phase.coefficientMode sourceHead)
      (positiveModeInReconstructedModes
        state sourceHead (include sourceHead (State.here refl)))
mappedPositiveLiteralWitness datum (sourceHead ∷ rest) include output
    (State.there member) =
  mappedPositiveLiteralWitness datum rest
    (λ selected selectedMember →
      include selected (State.there selectedMember))
    output member

positiveLiteralOutputWitness :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state)
    output →
  output State.∈ positiveLiteralOutputCoefficients datum →
  PositiveLiteralCoefficientWitness datum output
positiveLiteralOutputWitness {state = state} datum =
  mappedPositiveLiteralWitness datum
    (State.positiveOrbitCoefficients state)
    (λ coefficient member → member)

positiveLiteralOutputModesNonzero :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state)
    output →
  output State.∈ positiveLiteralOutputCoefficients datum →
  Z3.NonZeroMode (Phase.coefficientMode output)
positiveLiteralOutputModesNonzero {state = state} datum output member =
  let
    witness = positiveLiteralOutputWitness datum output member
    sourceNonzero =
      State.positiveModesNonzero state
        (source witness) (sourceMember witness)
  in
  subst Z3.NonZeroMode
    (sym (modeExact witness))
    sourceNonzero

fixedSupportPhysicalDerivative :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E} →
  Cutoff.CutoffSameObjectDatum F E state →
  State.ReconstructedPhysicalState F E
fixedSupportPhysicalDerivative datum =
  State.reconstructed-physical-state
    (positiveLiteralOutputCoefficients datum)
    (positiveLiteralOutputModesNonzero datum)

mappedPositiveOrbitModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state)
    (sourceList : List (Phase.TransverseModeCoefficient F E))
    (include : ∀ coefficient → coefficient State.∈ sourceList →
      coefficient State.∈ State.positiveOrbitCoefficients state) →
  Cutoff.orbitModes
    (mapPositiveLiteralCoefficients datum sourceList include)
  ≡ Cutoff.orbitModes sourceList
mappedPositiveOrbitModesExact datum [] include = refl
mappedPositiveOrbitModesExact {state = state}
    datum (sourceHead ∷ rest) include =
  cong₂ _∷_ positiveModeExact
    (cong₂ _∷_ negativeModeExact
      (mappedPositiveOrbitModesExact datum rest
        (λ selected selectedMember →
          include selected (State.there selectedMember))))
  where
  literalHead =
    Coefficient.literalTransverseCoefficient
      (Cutoff.canonicalPhysicalFiniteSystem datum)
      (Phase.coefficientMode sourceHead)
      (positiveModeInReconstructedModes
        state sourceHead (include sourceHead (State.here refl)))

  positiveModeExact :
    Phase.coefficientMode
      (Concrete.transportCoefficient
        (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
        literalHead)
    ≡ Phase.coefficientMode sourceHead
  positiveModeExact =
    Concrete.transportCoefficientMode
      (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
      literalHead

  negativeModeExact :
    Phase.reconstructedNegativeMode
      (Concrete.transportCoefficient
        (Cutoff.canonicalFiniteSystemEmbeddingExact datum)
        literalHead)
    ≡ Phase.reconstructedNegativeMode sourceHead
  negativeModeExact = cong Z3.negateMode positiveModeExact

fixedSupportDerivativeModesExact :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Same.reconstructedStateModes (fixedSupportPhysicalDerivative datum)
  ≡ Same.reconstructedStateModes state
fixedSupportDerivativeModesExact {state = state} datum =
  trans
    (Cutoff.reconstructedStateModesExact
      (fixedSupportPhysicalDerivative datum))
    (trans
      (mappedPositiveOrbitModesExact datum
        (State.positiveOrbitCoefficients state)
        (λ coefficient member → member))
      (sym (Cutoff.reconstructedStateModesExact state)))

fixedSupportDerivativeRetainsLiteralCutoff :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Same.reconstructedStateModes (fixedSupportPhysicalDerivative datum)
  ≡ Cutoff.nonzeroCutoffModes (Cutoff.cutoff datum)
fixedSupportDerivativeRetainsLiteralCutoff datum =
  trans
    (fixedSupportDerivativeModesExact datum)
    (Cutoff.retainedModesAreLiteralNonzeroCutoff datum)

record FixedCutoffSupportFibre
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F)
    (cutoff : Nat) : Set (lsuc r) where
  constructor fixed-cutoff-support-fibre
  field
    state : State.ReconstructedPhysicalState F E
    supportExact :
      Same.reconstructedStateModes state
      ≡ Cutoff.nonzeroCutoffModes cutoff

open FixedCutoffSupportFibre public

derivativeInSameCutoffSupportFibre :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  FixedCutoffSupportFibre F E (Cutoff.cutoff datum)
derivativeInSameCutoffSupportFibre datum =
  fixed-cutoff-support-fibre
    (fixedSupportPhysicalDerivative datum)
    (fixedSupportDerivativeRetainsLiteralCutoff datum)

fixedCutoffSupportTangencyClosed : Bool
fixedCutoffSupportTangencyClosed = true

fixedCutoffSameObjectCompatibilityInvariantConstructed : Bool
fixedCutoffSameObjectCompatibilityInvariantConstructed = false

fixedCutoffSupportTangencyClosedIsTrue :
  fixedCutoffSupportTangencyClosed ≡ true
fixedCutoffSupportTangencyClosedIsTrue = refl

fixedCutoffSameObjectCompatibilityInvariantConstructedIsFalse :
  fixedCutoffSameObjectCompatibilityInvariantConstructed ≡ false
fixedCutoffSameObjectCompatibilityInvariantConstructedIsFalse = refl
