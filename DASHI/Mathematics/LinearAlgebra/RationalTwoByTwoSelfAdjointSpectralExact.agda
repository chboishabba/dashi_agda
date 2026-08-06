module DASHI.Mathematics.LinearAlgebra.RationalTwoByTwoSelfAdjointSpectralExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Tosio Kato,
-- "Perturbation Theory for Linear Operators", second edition.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- DASHI CONTRIBUTION
--
-- Construct an exact rational 2-by-2 self-adjoint spectral model.  The
-- diagonal operator diag(2,5) has certified eigenpairs e1/e2, characteristic
-- polynomial (2-lambda)(5-lambda), spectral separation 3, and zero residuals.
-- A generic residual identity proves that an exact eigenpair is an
-- approximate eigenpair of radius zero.
--
-- This is the shared finite spectral seed for Hodge Laplacians, Maaß
-- enclosures, Hilbert--Pólya approximants and finite-volume transfer
-- Hamiltonians.  It does not prove convergence to any continuum spectrum.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record Vector2 : Set where
  constructor vector2
  field
    xCoordinate yCoordinate : ℚ

open Vector2 public

vectorExtensionality : ∀ {left right} →
  xCoordinate left ≡ xCoordinate right →
  yCoordinate left ≡ yCoordinate right →
  left ≡ right
vectorExtensionality {vector2 _ _} {vector2 _ _} refl refl = refl

zeroVector : Vector2
zeroVector = vector2 0ℚ 0ℚ

addVector : Vector2 → Vector2 → Vector2
addVector (vector2 x y) (vector2 x' y') = vector2 (x + x') (y + y')

scaleVector : ℚ → Vector2 → Vector2
scaleVector scalar (vector2 x y) = vector2 (scalar * x) (scalar * y)

subtractVector : Vector2 → Vector2 → Vector2
subtractVector (vector2 x y) (vector2 x' y') = vector2 (x - x') (y - y')

dot : Vector2 → Vector2 → ℚ
dot (vector2 x y) (vector2 x' y') = x * x' + y * y'

normSquared : Vector2 → ℚ
normSquared vector = dot vector vector

record Matrix2 : Set where
  constructor matrix2
  field
    entry11 entry12 entry21 entry22 : ℚ

open Matrix2 public

applyMatrix : Matrix2 → Vector2 → Vector2
applyMatrix (matrix2 a b c d) (vector2 x y) =
  vector2 (a * x + b * y) (c * x + d * y)

transpose : Matrix2 → Matrix2
transpose (matrix2 a b c d) = matrix2 a c b d

SelfAdjoint : Matrix2 → Set
SelfAdjoint matrix = transpose matrix ≡ matrix

matrixExtensionality : ∀ {left right} →
  entry11 left ≡ entry11 right →
  entry12 left ≡ entry12 right →
  entry21 left ≡ entry21 right →
  entry22 left ≡ entry22 right →
  left ≡ right
matrixExtensionality {matrix2 _ _ _ _} {matrix2 _ _ _ _}
  refl refl refl refl = refl

selfAdjointPairingLaw : ∀ matrix → SelfAdjoint matrix →
  ∀ left right →
  dot (applyMatrix matrix left) right
  ≡ dot left (applyMatrix matrix right)
selfAdjointPairingLaw (matrix2 a b c d) selfAdjoint
    (vector2 x y) (vector2 u v)
    with selfAdjoint
... | refl = solve (a ∷ b ∷ d ∷ x ∷ y ∷ u ∷ v ∷ [])

record ExactEigenpair (matrix : Matrix2) : Set where
  constructor exactEigenpair
  field
    eigenvalue : ℚ
    eigenvector : Vector2
    eigenvectorNonzero : eigenvector ≡ zeroVector → ⊥
    eigenEquation :
      applyMatrix matrix eigenvector
      ≡ scaleVector eigenvalue eigenvector

open ExactEigenpair public

residual : Matrix2 → ℚ → Vector2 → Vector2
residual matrix lambda vector =
  subtractVector
    (applyMatrix matrix vector)
    (scaleVector lambda vector)

exactEigenpairHasZeroResidual : ∀ {matrix} (pair : ExactEigenpair matrix) →
  residual matrix (eigenvalue pair) (eigenvector pair) ≡ zeroVector
exactEigenpairHasZeroResidual
    (exactEigenpair lambda vector nonzero equation)
    with equation
... | refl with vector
... | vector2 x y =
  vectorExtensionality (solve (lambda ∷ x ∷ [])) (solve (lambda ∷ y ∷ []))

record ApproximateEigenpair (matrix : Matrix2) : Set where
  field
    approximateEigenvalue : ℚ
    approximateEigenvector : Vector2
    residualVector : Vector2
    residualEquation :
      residual matrix approximateEigenvalue approximateEigenvector
      ≡ residualVector
    residualNormSquared : ℚ
    residualNormEquation :
      residualNormSquared ≡ normSquared residualVector

open ApproximateEigenpair public

exactToZeroResidualApproximate :
  ∀ {matrix} → ExactEigenpair matrix → ApproximateEigenpair matrix
exactToZeroResidualApproximate pair = record
  { approximateEigenvalue = eigenvalue pair
  ; approximateEigenvector = eigenvector pair
  ; residualVector = zeroVector
  ; residualEquation = exactEigenpairHasZeroResidual pair
  ; residualNormSquared = 0ℚ
  ; residualNormEquation = refl
  }

------------------------------------------------------------------------
-- Concrete diag(2,5) model.
------------------------------------------------------------------------

two five three nine : ℚ
two = 1ℚ + 1ℚ
five = two + two + 1ℚ
three = two + 1ℚ
nine = three * three

diagonalTwoFive : Matrix2
diagonalTwoFive = matrix2 two 0ℚ 0ℚ five

diagonalTwoFiveSelfAdjoint : SelfAdjoint diagonalTwoFive
diagonalTwoFiveSelfAdjoint = refl

basisOne basisTwo : Vector2
basisOne = vector2 1ℚ 0ℚ
basisTwo = vector2 0ℚ 1ℚ

basisOneNonzero : basisOne ≡ zeroVector → ⊥
basisOneNonzero ()

basisTwoNonzero : basisTwo ≡ zeroVector → ⊥
basisTwoNonzero ()

eigenpairTwo : ExactEigenpair diagonalTwoFive
eigenpairTwo = exactEigenpair two basisOne basisOneNonzero
  (vectorExtensionality (solve []) (solve []))

eigenpairFive : ExactEigenpair diagonalTwoFive
eigenpairFive = exactEigenpair five basisTwo basisTwoNonzero
  (vectorExtensionality (solve []) (solve []))

characteristicPolynomial : Matrix2 → ℚ → ℚ
characteristicPolynomial (matrix2 a b c d) lambda =
  (a - lambda) * (d - lambda) - b * c

diagonalCharacteristicFactors : ∀ lambda →
  characteristicPolynomial diagonalTwoFive lambda
  ≡ (two - lambda) * (five - lambda)
diagonalCharacteristicFactors lambda = solve (lambda ∷ [])

twoIsCharacteristicRoot :
  characteristicPolynomial diagonalTwoFive two ≡ 0ℚ
twoIsCharacteristicRoot = solve []

fiveIsCharacteristicRoot :
  characteristicPolynomial diagonalTwoFive five ≡ 0ℚ
fiveIsCharacteristicRoot = solve []

spectralDifference : five - two ≡ three
spectralDifference = solve []

spectralSeparationSquared : (five - two) * (five - two) ≡ nine
spectralSeparationSquared = solve []

basisOrthogonal : dot basisOne basisTwo ≡ 0ℚ
basisOrthogonal = solve []

basisNormalized :
  normSquared basisOne ≡ 1ℚ × normSquared basisTwo ≡ 1ℚ
basisNormalized = solve [] , solve []

record TwoPointSpectralCertificate : Set where
  field
    operatorSelfAdjoint : SelfAdjoint diagonalTwoFive
    firstEigenpair : ExactEigenpair diagonalTwoFive
    secondEigenpair : ExactEigenpair diagonalTwoFive
    firstRoot : characteristicPolynomial diagonalTwoFive two ≡ 0ℚ
    secondRoot : characteristicPolynomial diagonalTwoFive five ≡ 0ℚ
    separatedSquared : (five - two) * (five - two) ≡ nine
    orthogonalEigenvectors : dot basisOne basisTwo ≡ 0ℚ

canonicalTwoPointSpectralCertificate : TwoPointSpectralCertificate
canonicalTwoPointSpectralCertificate = record
  { operatorSelfAdjoint = diagonalTwoFiveSelfAdjoint
  ; firstEigenpair = eigenpairTwo
  ; secondEigenpair = eigenpairFive
  ; firstRoot = twoIsCharacteristicRoot
  ; secondRoot = fiveIsCharacteristicRoot
  ; separatedSquared = spectralSeparationSquared
  ; orthogonalEigenvectors = basisOrthogonal
  }
