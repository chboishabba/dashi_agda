module DASHI.Algebra.Quantum.ShorFiniteSyntaxCyclicPhaseQFTExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat)
open import Data.Fin.Base using (Fin)
open import Data.List.Base using (List; []; _∷_; allFin)

import DASHI.Foundations.Base369Nat as B369
import DASHI.Algebra.Quantum.FiniteQuantumRegister as Finite
import DASHI.Algebra.Quantum.QuantumFourierTransformFinite as QFT
import DASHI.Algebra.Quantum.ShorScalarAmplitudeCarrierExact as Scalar
import DASHI.Algebra.Quantum.ShorFiniteIndependentTargetAmplitudeOracleExact as Target
import DASHI.Algebra.Quantum.ShorCyclicExponentBasisExact as Cyclic
import DASHI.Algebra.Quantum.ShorCyclicPhaseAmplitudeQFTExact as Phase

------------------------------------------------------------------------
-- SAME-REGISTER CYCLIC PHASE ACTION ON THE CONSTRUCTIVE SYNTAX CARRIER
--
-- `ShorFiniteIndependentTargetAmplitudeOracleExact` already gives a finite
-- exponent x finite-target formal-amplitude register and a constructive
-- reversible lift of the exact RSA.powMod graph action.  This file puts the
-- literal cyclic character expansion on THAT SAME register.
--
-- A basis atom |x,y> is sent to
--
--   sum_{k in Fin Q} normalisation * phase(k,x) |k,y>.
--
-- The target coordinate is retained by `Target.relabelFiniteExponent`; only
-- the exponent is changed.  Scaling and addition are mapped structurally.
-- The inverse uses `inversePhase` in the same way.
--
-- Because the state is raw formal syntax rather than a quotient by module
-- identities, Fourier inversion is intentionally NOT asserted definitionally.
-- `SyntaxCyclicPhaseInversionAuthority` is the exact remaining algebraic seam:
-- an inhabitant must justify cancellation/normalisation for these literal
-- expansions (or provide a canonical normal-form theorem).  No funext or trust
-- escape is introduced.
------------------------------------------------------------------------

cyclicBasis :
  ∀ {Q} →
  B369.NonZero Q →
  Finite.FiniteBasis
cyclicBasis {Q} qNonZero =
  Cyclic.cyclicExponentBasis Q qNonZero

phaseCoefficient :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → Fin Q → Coefficient
phaseCoefficient A k x =
  Phase.multiplyCoefficient A
    (Phase.normalisation A)
    (Phase.phase A k x)

inversePhaseCoefficient :
  ∀ {Coefficient Q}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Fin Q → Fin Q → Coefficient
inversePhaseCoefficient A x k =
  Phase.multiplyCoefficient A
    (Phase.normalisation A)
    (Phase.inversePhase A x k)

sumExpression :
  ∀ {Coefficient BasisState} →
  Scalar.ScalarAmplitudeExpression Coefficient BasisState →
  (Fin 0 → Scalar.ScalarAmplitudeExpression Coefficient BasisState) →
  List (Fin 0) →
  Scalar.ScalarAmplitudeExpression Coefficient BasisState
sumExpression seed term [] = seed
sumExpression seed term (x ∷ xs) =
  Scalar.scalarAdd (term x) (sumExpression seed term xs)

foldExpressions :
  ∀ {Coefficient BasisState Q} →
  (Fin Q → Scalar.ScalarAmplitudeExpression Coefficient BasisState) →
  List (Fin Q) →
  Scalar.ScalarAmplitudeExpression Coefficient BasisState
foldExpressions term [] = Scalar.scalarZero
foldExpressions term (x ∷ xs) =
  Scalar.scalarAdd (term x) (foldExpressions term xs)

forwardBasisExpansion :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Target.FiniteIndependentTargetState
    (cyclicBasis qNonZero) base N nNonZero →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero)
forwardBasisExpansion {Q = Q} A basisState =
  foldExpressions
    (λ k →
      Scalar.scalarScale
        (phaseCoefficient A k
          (Target.finiteIndependentExponent basisState))
        (Scalar.scalarBasis
          (Target.relabelFiniteExponent k basisState)))
    (allFin Q)

inverseBasisExpansion :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Target.FiniteIndependentTargetState
    (cyclicBasis qNonZero) base N nNonZero →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero)
inverseBasisExpansion {Q = Q} A basisState =
  foldExpressions
    (λ x →
      Scalar.scalarScale
        (inversePhaseCoefficient A x
          (Target.finiteIndependentExponent basisState))
        (Scalar.scalarBasis
          (Target.relabelFiniteExponent x basisState)))
    (allFin Q)

forwardExpression :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero) →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero)
forwardExpression A Scalar.scalarZero = Scalar.scalarZero
forwardExpression A (Scalar.scalarBasis basisState) =
  forwardBasisExpansion A basisState
forwardExpression A (Scalar.scalarScale coefficient ψ) =
  Scalar.scalarScale coefficient (forwardExpression A ψ)
forwardExpression A (Scalar.scalarAdd ψ φ) =
  Scalar.scalarAdd (forwardExpression A ψ) (forwardExpression A φ)

inverseExpression :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero) →
  Scalar.ScalarAmplitudeExpression Coefficient
    (Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero)
inverseExpression A Scalar.scalarZero = Scalar.scalarZero
inverseExpression A (Scalar.scalarBasis basisState) =
  inverseBasisExpansion A basisState
inverseExpression A (Scalar.scalarScale coefficient ψ) =
  Scalar.scalarScale coefficient (inverseExpression A ψ)
inverseExpression A (Scalar.scalarAdd ψ φ) =
  Scalar.scalarAdd (inverseExpression A ψ) (inverseExpression A φ)

syntaxCyclicPhaseForward :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Finite.State
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient (cyclicBasis qNonZero) base N nNonZero) →
  Finite.State
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient (cyclicBasis qNonZero) base N nNonZero)
syntaxCyclicPhaseForward A
  (Target.finiteIndependentTargetAmplitudeState tag expression) =
  Target.finiteIndependentTargetAmplitudeState tag
    (forwardExpression A expression)

syntaxCyclicPhaseInverse :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  Finite.State
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient (cyclicBasis qNonZero) base N nNonZero) →
  Finite.State
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient (cyclicBasis qNonZero) base N nNonZero)
syntaxCyclicPhaseInverse A
  (Target.finiteIndependentTargetAmplitudeState tag expression) =
  Target.finiteIndependentTargetAmplitudeState tag
    (inverseExpression A expression)

record SyntaxCyclicPhaseInversionAuthority
    {Coefficient Q N}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) : Set₁ where
  constructor syntaxCyclicPhaseInversionAuthority
  field
    inverseAfterForward :
      ∀ {base} ψ →
      syntaxCyclicPhaseInverse
        {qNonZero = qNonZero} {nNonZero = nNonZero} A
        (syntaxCyclicPhaseForward
          {base = base} {qNonZero = qNonZero} {nNonZero = nNonZero} A ψ)
      ≡ ψ

    forwardAfterInverse :
      ∀ {base} ψ →
      syntaxCyclicPhaseForward
        {qNonZero = qNonZero} {nNonZero = nNonZero} A
        (syntaxCyclicPhaseInverse
          {base = base} {qNonZero = qNonZero} {nNonZero = nNonZero} A ψ)
      ≡ ψ

open SyntaxCyclicPhaseInversionAuthority public

syntaxCyclicPhaseFiniteFourierTransform :
  ∀ {Q N Coefficient base}
    (qNonZero : B369.NonZero Q)
    (nNonZero : B369.NonZero N)
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
  SyntaxCyclicPhaseInversionAuthority qNonZero nNonZero A →
  QFT.FiniteFourierTransform
    (Target.finiteIndependentTargetAmplitudeRegister
      Coefficient (cyclicBasis qNonZero) base N nNonZero)
syntaxCyclicPhaseFiniteFourierTransform qNonZero nNonZero A I = record
  { fourier = syntaxCyclicPhaseForward A
  ; inverseFourier = syntaxCyclicPhaseInverse A
  ; inverseAfterFourier = inverseAfterForward I
  ; fourierAfterInverse = forwardAfterInverse I
  }

basisForwardIsLiteralCharacterExpansion :
  ∀ {Coefficient Q N base}
    {qNonZero : B369.NonZero Q}
    {nNonZero : B369.NonZero N}
    (A : Phase.CyclicPhaseCoefficientAuthority Coefficient Q) →
    (basisState : Target.FiniteIndependentTargetState
      (cyclicBasis qNonZero) base N nNonZero) →
  forwardExpression A (Scalar.scalarBasis basisState)
  ≡ forwardBasisExpansion A basisState
basisForwardIsLiteralCharacterExpansion A basisState = refl

record ShorFiniteSyntaxCyclicPhaseQFTBoundary : Set where
  constructor shorFiniteSyntaxCyclicPhaseQFTBoundary
  field
    sameRegisterAsPowModOracle : Bool
    basisActionLiteralCharacterExpansion : Bool
    finiteExponentEnumerationUsed : Bool
    targetRetainedByRelabelling : Bool
    funextUsed : Bool
    coefficientNormalFormConstructed : Bool
    inversionAuthorityInhabitedHere : Bool
    bornMeasurementConstructed : Bool

canonicalShorFiniteSyntaxCyclicPhaseQFTBoundary :
  ShorFiniteSyntaxCyclicPhaseQFTBoundary
canonicalShorFiniteSyntaxCyclicPhaseQFTBoundary =
  shorFiniteSyntaxCyclicPhaseQFTBoundary
    true true true true false false false false
