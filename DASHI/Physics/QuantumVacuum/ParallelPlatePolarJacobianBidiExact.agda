module DASHI.Physics.QuantumVacuum.ParallelPlatePolarJacobianBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.PolarJacobianDeterminantAlgebraExact as Polar
import DASHI.Analysis.OrdinaryTranscendentalRealization as Trig
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseRadialReductionBidiExact as Radial

------------------------------------------------------------------------
-- POLAR JACOBIAN BIDI SPLIT
--
-- OWNED theorem shape:
--   det [[c,-rs],[s,rc]] = r(c^2+s^2), hence r under c^2+s^2=1.
--
-- Existing constructed-trig owner:
--   sin^2(theta)+cos^2(theta)=1.
--
-- LIVE application weld:
--   prove the matrix entries are literally the derivatives of
--   (r cos theta, r sin theta) on the selected constructive-real carrier and
--   feed |det|=r into the actual measure change-of-variables theorem.
------------------------------------------------------------------------

record ConstructedPolarDerivativeReceipt : Set₁ where
  field
    Scalar : Set
    radius theta : Scalar
    sine cosine : Scalar → Scalar
    multiply negate : Scalar → Scalar → Scalar

    dxDr dxDtheta dyDr dyDtheta : Scalar

    dxDrIsCosine : Set
    dxDthetaIsMinusRadiusSine : Set
    dyDrIsSine : Set
    dyDthetaIsRadiusCosine : Set
    sameDerivativeSemantics : Set
    reading : String

open ConstructedPolarDerivativeReceipt public

record PolarJacobianSameObjectWeld : Set₁ where
  field
    derivativeReceipt : ConstructedPolarDerivativeReceipt
    rationalAlgebraShape : Set
    constructedTrigPythagoreanUsed : Set
    sameMatrixEntryOrdering : Set
    sameDeterminantConvention : Set
    determinantEqualsRadius : Set
    reading : String

open PolarJacobianSameObjectWeld public

record PolarMeasureCompletion : Set₁ where
  field
    jacobianWeld : PolarJacobianSameObjectWeld
    radialReduction : Set
    absoluteJacobianEqualsRadius : Set
    angularDomainIsFullCircle : Set
    changeOfVariablesHypotheses : Set
    measureTransport : Set
    sameCasimirTransverseIntegrand : Set
    reading : String

open PolarMeasureCompletion public

data AlgebraicDeterminantAutomaticallyIsMeasureTheorem : Set where

data PythagoreanIdentityAutomaticallyProvesTrigDerivatives : Set where

algebraDoesNotAutoGiveMeasureTransport :
  AlgebraicDeterminantAutomaticallyIsMeasureTheorem → ⊥
algebraDoesNotAutoGiveMeasureTransport ()

pythagoreanDoesNotAutoGiveDerivativeEntries :
  PythagoreanIdentityAutomaticallyProvesTrigDerivatives → ⊥
pythagoreanDoesNotAutoGiveDerivativeEntries ()

record Status : Set where
  field
    polarDeterminantAlgebraOwned : Bool
    constructedTrigPythagoreanOwned : Bool
    polarDerivativeEntriesClosed : Bool
    measureChangeOfVariablesClosed : Bool

    polarDeterminantAlgebraOwnedIsTrue : polarDeterminantAlgebraOwned ≡ true
    constructedTrigPythagoreanOwnedIsTrue : constructedTrigPythagoreanOwned ≡ true
    polarDerivativeEntriesClosedIsFalse : polarDerivativeEntriesClosed ≡ false
    measureChangeOfVariablesClosedIsFalse : measureChangeOfVariablesClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { polarDeterminantAlgebraOwned = true
  ; constructedTrigPythagoreanOwned = true
  ; polarDerivativeEntriesClosed = false
  ; measureChangeOfVariablesClosed = false
  ; polarDeterminantAlgebraOwnedIsTrue = refl
  ; constructedTrigPythagoreanOwnedIsTrue = refl
  ; polarDerivativeEntriesClosedIsFalse = refl
  ; measureChangeOfVariablesClosedIsFalse = refl
  }
