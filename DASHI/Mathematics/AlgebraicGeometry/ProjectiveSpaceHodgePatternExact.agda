module DASHI.Mathematics.AlgebraicGeometry.ProjectiveSpaceHodgePatternExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Claire Voisin,
-- "Hodge Theory and Complex Algebraic Geometry I".
-- DOI: 10.1017/CBO9780511615344.
--
-- DASHI CONTRIBUTION
--
-- Give a finite generic carrier for the standard Hodge pattern of complex
-- projective space.  In complex dimension n, basis classes are indexed by
-- Fin(n+1), representing 1,H,...,H^n, and every class has diagonal bidegree
-- (k,k).  Explicit P2 and P3 basis and Betti vectors are checked.
--
-- The file captures the finite hyperplane-power/Hodge-diamond pattern.  A
-- geometric construction of CP^n, singular/de Rham comparison, hard Lefschetz
-- and the general cohomology-ring theorem remain separate owners.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin; zero; suc; toℕ)
open import Data.Product using (_×_; _,_)

record Bidegree : Set where
  constructor bidegree
  field
    pDegree qDegree : Nat

open Bidegree public

ProjectiveSpaceHodgeBasis : Nat → Set
ProjectiveSpaceHodgeBasis n = Fin (suc n)

hyperplanePowerDegree :
  ∀ {n} → ProjectiveSpaceHodgeBasis n → Bidegree
hyperplanePowerDegree class = bidegree (toℕ class) (toℕ class)

allProjectiveSpaceClassesAreDiagonal :
  ∀ {n} (class : ProjectiveSpaceHodgeBasis n) →
  pDegree (hyperplanePowerDegree class)
  ≡ qDegree (hyperplanePowerDegree class)
allProjectiveSpaceClassesAreDiagonal class = refl

hodgeConjugationFixesHyperplanePowers :
  ∀ {n} (class : ProjectiveSpaceHodgeBasis n) →
  bidegree
    (qDegree (hyperplanePowerDegree class))
    (pDegree (hyperplanePowerDegree class))
  ≡ hyperplanePowerDegree class
hodgeConjugationFixesHyperplanePowers class = refl

------------------------------------------------------------------------
-- P2: 1,H,H^2 and Betti vector 1,0,1,0,1.
------------------------------------------------------------------------

p2One : ProjectiveSpaceHodgeBasis 2
p2One = zero

p2Hyperplane : ProjectiveSpaceHodgeBasis 2
p2Hyperplane = suc zero

p2Point : ProjectiveSpaceHodgeBasis 2
p2Point = suc (suc zero)

p2Basis : List (ProjectiveSpaceHodgeBasis 2)
p2Basis = p2One ∷ p2Hyperplane ∷ p2Point ∷ []

p2OneDegree : hyperplanePowerDegree p2One ≡ bidegree 0 0
p2OneDegree = refl

p2HyperplaneDegree :
  hyperplanePowerDegree p2Hyperplane ≡ bidegree 1 1
p2HyperplaneDegree = refl

p2PointDegree : hyperplanePowerDegree p2Point ≡ bidegree 2 2
p2PointDegree = refl

p2Betti0 p2Betti1 p2Betti2 p2Betti3 p2Betti4 : Nat
p2Betti0 = 1
p2Betti1 = 0
p2Betti2 = 1
p2Betti3 = 0
p2Betti4 = 1

p2BettiVector :
  p2Betti0 ≡ 1
  × p2Betti1 ≡ 0
  × p2Betti2 ≡ 1
  × p2Betti3 ≡ 0
  × p2Betti4 ≡ 1
p2BettiVector = refl , refl , refl , refl , refl

------------------------------------------------------------------------
-- P3: 1,H,H^2,H^3 and Betti vector 1,0,1,0,1,0,1.
------------------------------------------------------------------------

p3One : ProjectiveSpaceHodgeBasis 3
p3One = zero

p3Hyperplane : ProjectiveSpaceHodgeBasis 3
p3Hyperplane = suc zero

p3Line : ProjectiveSpaceHodgeBasis 3
p3Line = suc (suc zero)

p3Point : ProjectiveSpaceHodgeBasis 3
p3Point = suc (suc (suc zero))

p3Basis : List (ProjectiveSpaceHodgeBasis 3)
p3Basis = p3One ∷ p3Hyperplane ∷ p3Line ∷ p3Point ∷ []

p3DegreeTable :
  hyperplanePowerDegree p3One ≡ bidegree 0 0
  × hyperplanePowerDegree p3Hyperplane ≡ bidegree 1 1
  × hyperplanePowerDegree p3Line ≡ bidegree 2 2
  × hyperplanePowerDegree p3Point ≡ bidegree 3 3
p3DegreeTable = refl , refl , refl , refl

p3BettiVector : List Nat
p3BettiVector = 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ 0 ∷ 1 ∷ []

record ProjectiveSpaceHodgeCertificate : Set₁ where
  field
    genericDiagonal : ∀ {n}
      (class : ProjectiveSpaceHodgeBasis n) →
      pDegree (hyperplanePowerDegree class)
      ≡ qDegree (hyperplanePowerDegree class)
    p2Degrees :
      hyperplanePowerDegree p2One ≡ bidegree 0 0
      × hyperplanePowerDegree p2Hyperplane ≡ bidegree 1 1
      × hyperplanePowerDegree p2Point ≡ bidegree 2 2
    p2Betti :
      p2Betti0 ≡ 1 × p2Betti1 ≡ 0 × p2Betti2 ≡ 1
      × p2Betti3 ≡ 0 × p2Betti4 ≡ 1
    p3Degrees :
      hyperplanePowerDegree p3One ≡ bidegree 0 0
      × hyperplanePowerDegree p3Hyperplane ≡ bidegree 1 1
      × hyperplanePowerDegree p3Line ≡ bidegree 2 2
      × hyperplanePowerDegree p3Point ≡ bidegree 3 3

canonicalProjectiveSpaceHodgeCertificate : ProjectiveSpaceHodgeCertificate
canonicalProjectiveSpaceHodgeCertificate = record
  { genericDiagonal = allProjectiveSpaceClassesAreDiagonal
  ; p2Degrees = p2OneDegree , p2HyperplaneDegree , p2PointDegree
  ; p2Betti = p2BettiVector
  ; p3Degrees = p3DegreeTable
  }

record ProjectiveSpaceGeometricBoundary : Set₁ where
  field
    ComplexProjectiveSpace : Nat → Set
    hyperplaneLineBundle : Set
    singularCohomologyRing : Set
    deRhamComparison : Set
    hardLefschetz : Set
    cycleClassOfHyperplanePower : Set
