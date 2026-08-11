module DASHI.Mathematics.NumberTheory.RiemannXiSymmetryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Bernhard Riemann,
-- "Ueber die Anzahl der Primzahlen unter einer gegebenen Grösse" (1859).
-- No DOI was assigned to the original publication.
--
-- Enrico Bombieri,
-- "Problems of the Millennium: The Riemann Hypothesis",
-- Clay Mathematics Institute problem description.  No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Implement the exact finite geometry of the completed-zeta symmetries on a
-- rational coordinate plane.  Conjugation, the functional-equation involution
-- s |-> 1-s, and reflection across Re(s)=1/2 are distinct maps.  Their
-- involutivity, commutation and fixed-line characterization are proved by exact
-- rational algebra.
--
-- The module also packages nontrivial-zero, zero-counting, explicit-formula,
-- Weil-positivity and Hilbert--Pólya obligation surfaces.  It does not construct
-- analytic continuation, Gamma factors, the actual completed zeta function,
-- a prime/zero explicit formula, a self-adjoint operator, or a proof of RH.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.Product using (_×_; _,_)
open import Data.Rational as R using (_/_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_; -_; _<_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

half : ℚ
half = (+ 1) R./ 2

record ComplexCoordinate : Set where
  constructor complexCoordinate
  field
    realPart imaginaryPart : ℚ

open ComplexCoordinate public

complexCoordinateExt : ∀ {left right} →
  realPart left ≡ realPart right →
  imaginaryPart left ≡ imaginaryPart right →
  left ≡ right
complexCoordinateExt {complexCoordinate _ _} {complexCoordinate _ _}
  refl refl = refl

conjugateCoordinate : ComplexCoordinate → ComplexCoordinate
conjugateCoordinate (complexCoordinate sigma tau) =
  complexCoordinate sigma (- tau)

functionalReflection : ComplexCoordinate → ComplexCoordinate
functionalReflection (complexCoordinate sigma tau) =
  complexCoordinate (1ℚ - sigma) (- tau)

criticalReflection : ComplexCoordinate → ComplexCoordinate
criticalReflection (complexCoordinate sigma tau) =
  complexCoordinate (1ℚ - sigma) tau

conjugationInvolutive : ∀ point →
  conjugateCoordinate (conjugateCoordinate point) ≡ point
conjugationInvolutive (complexCoordinate sigma tau) =
  complexCoordinateExt (solve (sigma ∷ [])) (solve (tau ∷ []))

functionalReflectionInvolutive : ∀ point →
  functionalReflection (functionalReflection point) ≡ point
functionalReflectionInvolutive (complexCoordinate sigma tau) =
  complexCoordinateExt (solve (sigma ∷ [])) (solve (tau ∷ []))

criticalReflectionInvolutive : ∀ point →
  criticalReflection (criticalReflection point) ≡ point
criticalReflectionInvolutive (complexCoordinate sigma tau) =
  complexCoordinateExt (solve (sigma ∷ [])) refl

functionalThenConjugateIsCritical : ∀ point →
  conjugateCoordinate (functionalReflection point)
  ≡ criticalReflection point
functionalThenConjugateIsCritical (complexCoordinate sigma tau) =
  complexCoordinateExt refl (solve (tau ∷ []))

conjugateThenFunctionalIsCritical : ∀ point →
  functionalReflection (conjugateCoordinate point)
  ≡ criticalReflection point
conjugateThenFunctionalIsCritical (complexCoordinate sigma tau) =
  complexCoordinateExt refl (solve (tau ∷ []))

conjugationCommutesWithFunctionalReflection : ∀ point →
  conjugateCoordinate (functionalReflection point)
  ≡ functionalReflection (conjugateCoordinate point)
conjugationCommutesWithFunctionalReflection point =
  trans
    (functionalThenConjugateIsCritical point)
    (sym (conjugateThenFunctionalIsCritical point))

CriticalLine : ComplexCoordinate → Set
CriticalLine point = realPart point ≡ half

CriticalStrip : ComplexCoordinate → Set
CriticalStrip point =
  (0ℚ < realPart point) × (realPart point < 1ℚ)

criticalLineFixedByReflection : ∀ point →
  CriticalLine point → criticalReflection point ≡ point
criticalLineFixedByReflection
    (complexCoordinate sigma tau) sigmaIsHalf =
  complexCoordinateExt
    (trans
      (cong (λ value → 1ℚ - value) sigmaIsHalf)
      (trans
        (solve [])
        (sym sigmaIsHalf)))
    refl

reflectionFixedImpliesCriticalLine : ∀ point →
  criticalReflection point ≡ point → CriticalLine point
reflectionFixedImpliesCriticalLine
    (complexCoordinate sigma tau) reflectionFixed =
  let
    realFixed : 1ℚ - sigma ≡ sigma
    realFixed = cong realPart reflectionFixed

    oneEqualsDouble : 1ℚ ≡ sigma + sigma
    oneEqualsDouble =
      trans
        (solve (sigma ∷ []))
        (cong (λ value → value + sigma) realFixed)
  in
  trans
    (solve (sigma ∷ []))
    (trans
      (cong (λ value → half * value) (sym oneEqualsDouble))
      (solve []))

record XiZeroSymmetry : Set₁ where
  field
    isXiZero : ComplexCoordinate → Set
    functionalEquationPreservesZero : ∀ point →
      isXiZero point → isXiZero (functionalReflection point)
    conjugationPreservesZero : ∀ point →
      isXiZero point → isXiZero (conjugateCoordinate point)

open XiZeroSymmetry public

zeroQuartet : ∀ symmetry point →
  isXiZero symmetry point →
  isXiZero symmetry (conjugateCoordinate point)
  × isXiZero symmetry (functionalReflection point)
  × isXiZero symmetry (criticalReflection point)
zeroQuartet symmetry point zeroAtPoint =
  conjugationPreservesZero symmetry point zeroAtPoint
  , functionalEquationPreservesZero symmetry point zeroAtPoint
  , transZero
  where
    transZero : isXiZero symmetry (criticalReflection point)
    transZero =
      let
        functionalZero =
          functionalEquationPreservesZero symmetry point zeroAtPoint
        conjugatedFunctionalZero =
          conjugationPreservesZero symmetry
            (functionalReflection point) functionalZero
      in
      transportZero
        (functionalThenConjugateIsCritical point)
        conjugatedFunctionalZero

    transportZero : ∀ {left right} →
      left ≡ right → isXiZero symmetry left → isXiZero symmetry right
    transportZero refl proof = proof

record NontrivialXiZero (symmetry : XiZeroSymmetry) : Set where
  field
    zeroCoordinate : ComplexCoordinate
    zeroWitness : isXiZero symmetry zeroCoordinate
    criticalStripWitness : CriticalStrip zeroCoordinate

record ZeroCountingData (symmetry : XiZeroSymmetry) : Set₁ where
  field
    Height : Set
    boundedByHeight : ComplexCoordinate → Height → Set
    zeroCount : Height → Nat
    finiteCountCorrect : ∀ height → Set
    monotoneCount : Set

record PrimeZeroExplicitFormula : Set₁ where
  field
    PrimeDatum ZeroDatum TestFunction Scalar : Set
    primeSide : TestFunction → PrimeDatum → Scalar
    zeroSide : TestFunction → ZeroDatum → Scalar
    archimedeanSide : TestFunction → Scalar
    explicitFormulaIdentity : Set

record WeilPositivityCriterion : Set₁ where
  field
    TestFunction WeilQuadraticForm : Set
    admissible : TestFunction → Set
    quadraticForm : TestFunction → WeilQuadraticForm
    nonnegative : WeilQuadraticForm → Set
    positivityForAllAdmissible : Set
    positivityEquivalentToRH : Set

record HilbertPolyaCandidate : Set₁ where
  field
    Eigenvector : Set
    eigenvalue : Eigenvector → ℚ
    selfAdjointRealSpectrum : Set
    associatedZero : Eigenvector → ComplexCoordinate
    zeroCoordinateLaw : ∀ eigenvector →
      associatedZero eigenvector
      ≡ complexCoordinate half (eigenvalue eigenvector)

open HilbertPolyaCandidate public

hilbertPolyaCandidateZerosLieOnCriticalLine :
  ∀ candidate eigenvector →
  CriticalLine (associatedZero candidate eigenvector)
hilbertPolyaCandidateZerosLieOnCriticalLine candidate eigenvector =
  trans
    (cong realPart (zeroCoordinateLaw candidate eigenvector))
    refl

data RiemannProofStage : Set where
  zetaDirichletSeries
  meromorphicContinuation
  completedXiFunctionalEquation
  nontrivialZeroSymmetry
  explicitPrimeZeroFormula
  zeroCountingAsymptotics
  weilPositivity
  hilbertPolyaOperator
  allNontrivialZerosCritical

stageDistinct :
  hilbertPolyaOperator ≡ allNontrivialZerosCritical → ⊥
stageDistinct ()
