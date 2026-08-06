module DASHI.Moonshine.RankOneHeisenbergFockWindowExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Victor G. Kac,
-- "Vertex Algebras for Beginners", second edition,
-- University Lecture Series 10, American Mathematical Society, 1998.
-- No DOI is asserted for the cited AMS book edition.
--
-- DASHI CONTRIBUTION
--
-- Give an exact finite-window representation of the rank-one Heisenberg
-- relation.  On rational polynomials of degree at most four, creation is
-- multiplication by x followed by truncation and annihilation is formal
-- differentiation.  For inputs of degree at most three,
--
--   D(Xf) - X(Df) = f.
--
-- The number operator XD has eigenvalues 0,1,2,3 on the first four monomials.
-- This is the finite oscillator algebra beneath the Fock grading.  The full
-- infinite Weyl algebra, completed Fock space, normal ordering and VOA Jacobi
-- identity remain separate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)

record PolynomialDegreeFour : Set where
  constructor polynomial5
  field
    coefficient0 coefficient1 coefficient2 coefficient3 coefficient4 : ℚ

open PolynomialDegreeFour public

polynomialExtensionality : ∀ {left right} →
  coefficient0 left ≡ coefficient0 right →
  coefficient1 left ≡ coefficient1 right →
  coefficient2 left ≡ coefficient2 right →
  coefficient3 left ≡ coefficient3 right →
  coefficient4 left ≡ coefficient4 right →
  left ≡ right
polynomialExtensionality
    {polynomial5 _ _ _ _ _} {polynomial5 _ _ _ _ _}
    refl refl refl refl refl = refl

zeroPolynomial : PolynomialDegreeFour
zeroPolynomial = polynomial5 0ℚ 0ℚ 0ℚ 0ℚ 0ℚ

subtractPolynomial :
  PolynomialDegreeFour → PolynomialDegreeFour → PolynomialDegreeFour
subtractPolynomial
    (polynomial5 a0 a1 a2 a3 a4)
    (polynomial5 b0 b1 b2 b3 b4) =
  polynomial5
    (a0 - b0) (a1 - b1) (a2 - b2) (a3 - b3) (a4 - b4)

scalePolynomial : ℚ → PolynomialDegreeFour → PolynomialDegreeFour
scalePolynomial scalar (polynomial5 a0 a1 a2 a3 a4) =
  polynomial5
    (scalar * a0) (scalar * a1) (scalar * a2)
    (scalar * a3) (scalar * a4)

creation : PolynomialDegreeFour → PolynomialDegreeFour
creation (polynomial5 a0 a1 a2 a3 a4) =
  polynomial5 0ℚ a0 a1 a2 a3

annihilation : PolynomialDegreeFour → PolynomialDegreeFour
annihilation (polynomial5 a0 a1 a2 a3 a4) =
  polynomial5
    a1
    ((1ℚ + 1ℚ) * a2)
    ((1ℚ + 1ℚ + 1ℚ) * a3)
    ((1ℚ + 1ℚ + 1ℚ + 1ℚ) * a4)
    0ℚ

record DegreeAtMostThree (polynomial : PolynomialDegreeFour) : Set where
  constructor degreeAtMostThree
  field
    topCoefficientZero : coefficient4 polynomial ≡ 0ℚ

open DegreeAtMostThree public

heisenbergCommutator : PolynomialDegreeFour → PolynomialDegreeFour
heisenbergCommutator polynomial =
  subtractPolynomial
    (annihilation (creation polynomial))
    (creation (annihilation polynomial))

heisenbergRelationOnFiniteWindow : ∀ polynomial →
  DegreeAtMostThree polynomial →
  heisenbergCommutator polynomial ≡ polynomial
heisenbergRelationOnFiniteWindow
    (polynomial5 a0 a1 a2 a3 a4)
    (degreeAtMostThree topZero)
    with topZero
... | refl =
  polynomialExtensionality
    (solve (a0 ∷ []))
    (solve (a1 ∷ []))
    (solve (a2 ∷ []))
    (solve (a3 ∷ []))
    refl

numberOperator : PolynomialDegreeFour → PolynomialDegreeFour
numberOperator polynomial = creation (annihilation polynomial)

basis0 basis1 basis2 basis3 : PolynomialDegreeFour
basis0 = polynomial5 1ℚ 0ℚ 0ℚ 0ℚ 0ℚ
basis1 = polynomial5 0ℚ 1ℚ 0ℚ 0ℚ 0ℚ
basis2 = polynomial5 0ℚ 0ℚ 1ℚ 0ℚ 0ℚ
basis3 = polynomial5 0ℚ 0ℚ 0ℚ 1ℚ 0ℚ

basis0LowDegree : DegreeAtMostThree basis0
basis0LowDegree = degreeAtMostThree refl

basis1LowDegree : DegreeAtMostThree basis1
basis1LowDegree = degreeAtMostThree refl

basis2LowDegree : DegreeAtMostThree basis2
basis2LowDegree = degreeAtMostThree refl

basis3LowDegree : DegreeAtMostThree basis3
basis3LowDegree = degreeAtMostThree refl

numberEigenvalue0 : numberOperator basis0 ≡ scalePolynomial 0ℚ basis0
numberEigenvalue0 =
  polynomialExtensionality (solve []) (solve []) (solve []) (solve []) (solve [])

numberEigenvalue1 : numberOperator basis1 ≡ scalePolynomial 1ℚ basis1
numberEigenvalue1 =
  polynomialExtensionality (solve []) (solve []) (solve []) (solve []) (solve [])

numberEigenvalue2 :
  numberOperator basis2 ≡ scalePolynomial (1ℚ + 1ℚ) basis2
numberEigenvalue2 =
  polynomialExtensionality (solve []) (solve []) (solve []) (solve []) (solve [])

numberEigenvalue3 :
  numberOperator basis3 ≡ scalePolynomial (1ℚ + 1ℚ + 1ℚ) basis3
numberEigenvalue3 =
  polynomialExtensionality (solve []) (solve []) (solve []) (solve []) (solve [])

vacuumAnnihilated : annihilation basis0 ≡ zeroPolynomial
vacuumAnnihilated = refl

creationBuildsFirstModes :
  creation basis0 ≡ basis1
  × creation basis1 ≡ basis2
  × creation basis2 ≡ basis3
creationBuildsFirstModes = refl , refl , refl

record FiniteHeisenbergCertificate : Set where
  field
    commutatorIdentity : ∀ polynomial →
      DegreeAtMostThree polynomial →
      heisenbergCommutator polynomial ≡ polynomial
    vacuumKilled : annihilation basis0 ≡ zeroPolynomial
    numberZero : numberOperator basis0 ≡ scalePolynomial 0ℚ basis0
    numberOne : numberOperator basis1 ≡ scalePolynomial 1ℚ basis1
    numberTwo :
      numberOperator basis2 ≡ scalePolynomial (1ℚ + 1ℚ) basis2
    numberThree :
      numberOperator basis3
      ≡ scalePolynomial (1ℚ + 1ℚ + 1ℚ) basis3

canonicalFiniteHeisenbergCertificate : FiniteHeisenbergCertificate
canonicalFiniteHeisenbergCertificate = record
  { commutatorIdentity = heisenbergRelationOnFiniteWindow
  ; vacuumKilled = vacuumAnnihilated
  ; numberZero = numberEigenvalue0
  ; numberOne = numberEigenvalue1
  ; numberTwo = numberEigenvalue2
  ; numberThree = numberEigenvalue3
  }

record InfiniteHeisenbergFockBoundary : Set₁ where
  field
    allIntegerModes : Set
    centralExtension : Set
    fullCommutator : Set
    completedFockSpace : Set
    normalOrdering : Set
    conformalVector : Set
    centralChargeOne : Set
    vertexJacobiIdentity : Set
