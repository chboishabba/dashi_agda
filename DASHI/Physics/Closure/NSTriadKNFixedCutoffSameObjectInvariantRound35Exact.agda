module DASHI.Physics.Closure.NSTriadKNFixedCutoffSameObjectInvariantRound35Exact where

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
-- Close the Round-35 F1 invariance leaf.  Previous modules now provide:
--
--   * fixed-cutoff support tangency of the literal derivative;
--   * global Fourier reality of the canonical same-object velocity;
--   * local ordered nonlinear reality;
--   * exact conjugation permutation of the output fibres;
--   * summed projected-nonlinearity reality;
--   * viscous reality and hence full RHS reality.
--
-- Using those producer theorems, this module proves the new positive
-- representative list produced by `fixedSupportPhysicalDerivative` is itself
-- `SameObjectCompatibleState`:
--
--   equal output modes have equal RHS values;
--   a positive output overlapping the negative sheet has the conjugate RHS
--   value forced by Fourier reality.
--
-- The derivative therefore inhabits a fresh `CutoffSameObjectDatum` with the
-- *same* cutoff, inverse-square geometry and viscosity.  This is literal
-- tangency of the complete strengthened same-object cutoff carrier.  No ODE
-- existence theorem is used: F1 is an invariant vector-field carrier, while
-- F2/F3 still construct and integrate that vector field on Bishop reals.
------------------------------------------------------------------------

open import Agda.Primitive using (lsuc)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Coefficient
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Cutoff
import DASHI.Physics.Closure.NSTriadKNFixedCutoffSupportInvariantRound35Exact as Fixed
import DASHI.Physics.Closure.NSTriadKNCanonicalVelocityRealityRound35Exact as VelocityReality
import DASHI.Physics.Closure.NSTriadKNSummedProjectedNonlinearityRealityRound35Exact as SummedReality
import DASHI.Physics.Closure.NSTriadKNViscousRealityRound35Exact as ViscousReality

canonicalSystemVelocityReality :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Reality.RealityCondition
    (Audit.velocity
      (Coefficient.finiteSystem (Cutoff.canonicalPhysicalFiniteSystem datum)))
canonicalSystemVelocityReality datum =
  VelocityReality.literalVelocityReality (Cutoff.compatibility datum)

canonicalSystemSummedNonlinearityReality :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  ViscousReality.SummedProjectedNonlinearityReality
    (Coefficient.finiteSystem (Cutoff.canonicalPhysicalFiniteSystem datum))
canonicalSystemSummedNonlinearityReality datum =
  SummedReality.canonicalSummedProjectedNonlinearityReality
    (Coefficient.finiteSystem (Cutoff.canonicalPhysicalFiniteSystem datum))
    (canonicalSystemVelocityReality datum)

canonicalLiteralRHSReality :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Reality.RealityCondition
    (Coefficient.literalViscousQuadraticCoefficient
      (Cutoff.canonicalPhysicalFiniteSystem datum))
canonicalLiteralRHSReality datum =
  ViscousReality.literalViscousQuadraticCoefficientReality
    (Cutoff.canonicalPhysicalFiniteSystem datum)
    (canonicalSystemVelocityReality datum)
    (canonicalSystemSummedNonlinearityReality datum)

outputPositiveFunctional :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Lookup.PositiveModeFunctional
    (State.positiveOrbitCoefficients
      (Fixed.fixedSupportPhysicalDerivative datum))
outputPositiveFunctional datum
    left right leftMember rightMember sameOutputMode =
  let
    leftWitness = Fixed.positiveLiteralOutputWitness datum left leftMember
    rightWitness = Fixed.positiveLiteralOutputWitness datum right rightMember

    sourceModeEqual :
      Phase.coefficientMode (Fixed.source leftWitness)
      ≡ Phase.coefficientMode (Fixed.source rightWitness)
    sourceModeEqual =
      trans
        (sym (Fixed.modeExact leftWitness))
        (trans sameOutputMode (Fixed.modeExact rightWitness))
  in
  trans
    (Fixed.valueExact leftWitness)
    (trans
      (cong
        (Coefficient.literalViscousQuadraticCoefficient
          (Cutoff.canonicalPhysicalFiniteSystem datum))
        sourceModeEqual)
      (sym (Fixed.valueExact rightWitness)))

outputPositiveNegativeCompatibility :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Lookup.PositiveNegativeCompatible
    (State.positiveOrbitCoefficients
      (Fixed.fixedSupportPhysicalDerivative datum))
outputPositiveNegativeCompatibility datum
    positive source positiveMember sourceMember samePhysicalMode =
  let
    positiveWitness =
      Fixed.positiveLiteralOutputWitness datum positive positiveMember
    sourceWitness =
      Fixed.positiveLiteralOutputWitness datum source sourceMember

    positiveSourceMode : Z3.FourierMode
    positiveSourceMode = Phase.coefficientMode (Fixed.source positiveWitness)

    negativeSourceMode : Z3.FourierMode
    negativeSourceMode = Phase.coefficientMode (Fixed.source sourceWitness)

    sourceModesOpposite :
      positiveSourceMode ≡ Z3.negateMode negativeSourceMode
    sourceModesOpposite =
      trans
        (sym (Fixed.modeExact positiveWitness))
        (trans
          samePhysicalMode
          (cong Z3.negateMode (Fixed.modeExact sourceWitness)))

    rhsReality = canonicalLiteralRHSReality datum
  in
  trans
    (Fixed.valueExact positiveWitness)
    (trans
      (cong
        (Coefficient.literalViscousQuadraticCoefficient
          (Cutoff.canonicalPhysicalFiniteSystem datum))
        sourceModesOpposite)
      (trans
        (rhsReality negativeSourceMode)
        (cong C3.complex3Conjugate
          (sym (Fixed.valueExact sourceWitness)))))

fixedSupportDerivativeCompatibleState :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Lookup.SameObjectCompatibleState F E
    (Fixed.fixedSupportPhysicalDerivative datum)
fixedSupportDerivativeCompatibleState datum =
  Lookup.same-object-compatible-state
    (outputPositiveFunctional datum)
    (outputPositiveNegativeCompatibility datum)

derivativeCutoffSameObjectDatum :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  Cutoff.CutoffSameObjectDatum F E
    (Fixed.fixedSupportPhysicalDerivative datum)
derivativeCutoffSameObjectDatum datum =
  Cutoff.cutoff-same-object-datum
    (fixedSupportDerivativeCompatibleState datum)
    (Cutoff.cutoff datum)
    (Cutoff.inverseSquare datum)
    (Cutoff.viscosity datum)
    (Fixed.fixedSupportDerivativeRetainsLiteralCutoff datum)

record FixedCutoffSameObjectVectorFieldInvariant
    {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F)
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) : Set (lsuc r) where
  field
    derivativeState : State.ReconstructedPhysicalState F E
    derivativeExact :
      derivativeState ≡ Fixed.fixedSupportPhysicalDerivative datum
    derivativeDatum :
      Cutoff.CutoffSameObjectDatum F E derivativeState
    sameCutoff :
      Cutoff.cutoff derivativeDatum ≡ Cutoff.cutoff datum

open FixedCutoffSameObjectVectorFieldInvariant public

canonicalFixedCutoffSameObjectVectorFieldInvariant :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (datum : Cutoff.CutoffSameObjectDatum F E state) →
  FixedCutoffSameObjectVectorFieldInvariant F E datum
canonicalFixedCutoffSameObjectVectorFieldInvariant datum = record
  { derivativeState = Fixed.fixedSupportPhysicalDerivative datum
  ; derivativeExact = refl
  ; derivativeDatum = derivativeCutoffSameObjectDatum datum
  ; sameCutoff = refl
  }

fixedCutoffSameObjectVectorFieldInvariantClosed : Bool
fixedCutoffSameObjectVectorFieldInvariantClosed = true

fixedCutoffSameObjectVectorFieldInvariantClosedIsTrue :
  fixedCutoffSameObjectVectorFieldInvariantClosed ≡ true
fixedCutoffSameObjectVectorFieldInvariantClosedIsTrue = refl
