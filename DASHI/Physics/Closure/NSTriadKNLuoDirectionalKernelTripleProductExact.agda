module DASHI.Physics.Closure.NSTriadKNLuoDirectionalKernelTripleProductExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Peter Constantin and Charles Fefferman,
-- "Direction of Vorticity and the Problem of Global Regularity for the
-- Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Zoran Grujic,
-- "A Geometric Measure-Type Regularity Criterion for Solutions to the
-- 3D Navier-Stokes Equations".
-- DOI: 10.1088/0951-7715/26/1/289.
--
-- DASHI CONTRIBUTION
--
-- The geometric kernel factor is represented by the scalar triple product
--
--   r . (omega_x cross omega_y),
--
-- where r is a unit radial direction.  Exact finite Cauchy--Schwarz gives
--
--   triple^2 <= |omega_x cross omega_y|^2.
--
-- Combining this with the already checked physical directional-defect identity
-- yields
--
--   triple^2
--     <= a^2 b^2 Theta(xi,eta).
--
-- Thus the unsquared estimate carries sqrt(Theta), while the radical-free
-- squared estimate carries Theta.  The two forms are not silently conflated.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical

scalarTriple : Gram.Vec3 → Gram.Vec3 → Gram.Vec3 → ℚ
scalarTriple radial left right =
  Gram.dot radial (Gram.cross left right)

scalarTripleSquaredBound :
  ∀ radial left right →
  L2.square (scalarTriple radial left right)
  ≤ Gram.normSquared radial * Gram.crossNormSquared left right
scalarTripleSquaredBound radial left right =
  let
    crossVector = Gram.cross left right
    product =
      Gram.normSquared radial * Gram.normSquared crossVector
    tripleSquare =
      L2.square (Gram.dot radial crossVector)
    defect = product - tripleSquare

    defectNonnegative : 0ℚ ≤ defect
    defectNonnegative =
      Gram.gramDefectNonnegative radial crossVector

    shifted :
      tripleSquare + 0ℚ
      ≤ tripleSquare + defect
    shifted =
      ℚₚ.+-monoʳ-≤ tripleSquare defectNonnegative

    leftClosed : tripleSquare + 0ℚ ≡ tripleSquare
    leftClosed = solve (tripleSquare ∷ [])

    rightClosed : tripleSquare + defect ≡ product
    rightClosed = solve (product ∷ tripleSquare ∷ [])

    normalizedLeft : tripleSquare ≤ tripleSquare + defect
    normalizedLeft =
      subst
        (λ leftValue → leftValue ≤ tripleSquare + defect)
        leftClosed
        shifted
  in
  subst
    (λ rightValue → tripleSquare ≤ rightValue)
    rightClosed
    normalizedLeft

record UnitRadialPhysicalPair : Set where
  constructor unitRadialPhysicalPair
  field
    radial : Gram.Vec3
    radialUnit : Gram.normSquared radial ≡ 1ℚ
    vorticityPair : Physical.PhysicalVorticityPair

open UnitRadialPhysicalPair public

physicalTriple : UnitRadialPhysicalPair → ℚ
physicalTriple cell =
  scalarTriple
    (radial cell)
    (Physical.leftVorticity (vorticityPair cell))
    (Physical.rightVorticity (vorticityPair cell))

unitRadialTripleBound :
  ∀ cell →
  L2.square (physicalTriple cell)
  ≤
  Gram.crossNormSquared
    (Physical.leftVorticity (vorticityPair cell))
    (Physical.rightVorticity (vorticityPair cell))
unitRadialTripleBound cell =
  let
    base =
      scalarTripleSquaredBound
        (radial cell)
        (Physical.leftVorticity (vorticityPair cell))
        (Physical.rightVorticity (vorticityPair cell))

    rightMeaning :
      Gram.normSquared (radial cell)
      * Gram.crossNormSquared
          (Physical.leftVorticity (vorticityPair cell))
          (Physical.rightVorticity (vorticityPair cell))
      ≡
      Gram.crossNormSquared
        (Physical.leftVorticity (vorticityPair cell))
        (Physical.rightVorticity (vorticityPair cell))
    rightMeaning
      rewrite radialUnit cell =
      solve
        ( Gram.crossNormSquared
            (Physical.leftVorticity (vorticityPair cell))
            (Physical.rightVorticity (vorticityPair cell))
        ∷ [])
  in
  subst
    (λ rightValue →
      L2.square (physicalTriple cell) ≤ rightValue)
    rightMeaning
    base

physicalDirectionalTripleBound :
  ∀ cell →
  L2.square (physicalTriple cell)
  ≤
  L2.square
    (Physical.leftAmplitude (vorticityPair cell))
  * L2.square
    (Physical.rightAmplitude (vorticityPair cell))
  * Gram.directionalDefect
    (Physical.directions (vorticityPair cell))
physicalDirectionalTripleBound cell =
  let
    base = unitRadialTripleBound cell
    identity =
      Physical.physicalDirectionalDefectIdentity
        (vorticityPair cell)
  in
  subst
    (λ rightValue →
      L2.square (physicalTriple cell) ≤ rightValue)
    identity
    base

record DirectionalFactorBoundary : Set where
  constructor directionalFactorBoundary
  field
    squaredThetaFactorProved : Set
    unsquaredSquareRootFactorAutomaticallyIdentified : Set
    principalValueKernelEstimateProved : Set

canonicalDirectionalFactorBoundary : DirectionalFactorBoundary
canonicalDirectionalFactorBoundary =
  directionalFactorBoundary ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
