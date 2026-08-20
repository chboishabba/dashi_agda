module DASHI.Physics.YangMills.BalabanWilsonLatticeReflectionPositivityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Erhard Seiler,
-- "Gauge Field Theories on a Lattice", Annals of Physics 110 (1978),
-- 440--471.
-- DOI: 10.1016/0003-4916(78)90039-8.
--
-- P. Menotti and A. Pelissetto,
-- "General Proof of Osterwalder-Schrader Positivity for the Wilson Action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251.
--
-- Erhard Seiler,
-- "Gauge Theories as a Problem of Constructive Quantum Field Theory and
-- Statistical Mechanics", Lecture Notes in Physics 159, Springer, 1982.
-- DOI: 10.1007/3-540-11559-5.
--
-- SOURCE ROLE
--
-- Osterwalder--Seiler prove physical/reflection positivity for lattice gauge
-- Schwinger functions and obtain a positive self-adjoint transfer matrix.
-- Menotti--Pelissetto sharpen the Wilson-action statement to reflections in
-- planes containing sites, for arbitrary gauge-invariant observables and all
-- Euclidean time separations.
--
-- DASHI CONTRIBUTION
--
-- Isolate the exact algebraic core consumed by a finite reflection-positivity
-- proof: after the cross-plane Wilson weight has been factorized into a finite
-- sum of modular squares, every contribution is a nonnegative coefficient
-- times a square.  This file proves that finite sum nonnegative over exact
-- rationals.  It deliberately does NOT claim that the current Bałaban/Wilson
-- carrier has already been identified with the Osterwalder--Seiler character
-- expansion: that source-specific identification remains a physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; _≤_)
import Data.Rational.Properties as ℚP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as FiniteL2
import DASHI.Physics.YangMills.BalabanPositiveRGDirichletGeometryExact as PositiveRG

------------------------------------------------------------------------
-- Exact finite modular-square carrier.
------------------------------------------------------------------------

record ReflectionSquareAtom : Set where
  constructor reflectionSquareAtom
  field
    coefficient : ℚ
    amplitude : ℚ
    coefficientNonnegative : 0ℚ ≤ coefficient
open ReflectionSquareAtom public

reflectionSquareValue : ReflectionSquareAtom → ℚ
reflectionSquareValue atom =
  coefficient atom * FiniteL2.square (amplitude atom)

reflectionSquareValueNonnegative :
  ∀ atom → 0ℚ ≤ reflectionSquareValue atom
reflectionSquareValueNonnegative atom =
  PositiveRG.nonnegativeProduct
    (coefficientNonnegative atom)
    (FiniteL2.squareNonnegative (amplitude atom))

reflectionQuadratic : List ReflectionSquareAtom → ℚ
reflectionQuadratic [] = 0ℚ
reflectionQuadratic (atom ∷ rest) =
  reflectionSquareValue atom + reflectionQuadratic rest

reflectionQuadraticNonnegative :
  ∀ atoms → 0ℚ ≤ reflectionQuadratic atoms
reflectionQuadraticNonnegative [] = ℚP.≤-refl
reflectionQuadraticNonnegative (atom ∷ rest) =
  FiniteL2.addNonnegative
    (reflectionSquareValueNonnegative atom)
    (reflectionQuadraticNonnegative rest)

record FiniteWilsonReflectionSquareFactorization : Set where
  constructor finiteWilsonReflectionSquareFactorization
  field
    atoms : List ReflectionSquareAtom
open FiniteWilsonReflectionSquareFactorization public

finiteWilsonReflectionPositive :
  ∀ factorization →
  0ℚ ≤ reflectionQuadratic (atoms factorization)
finiteWilsonReflectionPositive factorization =
  reflectionQuadraticNonnegative (atoms factorization)

------------------------------------------------------------------------
-- Proof-level boundary.
------------------------------------------------------------------------

-- The literature theorem is not re-proved here.
osterwalderSeilerLatticeGaugeReflectionPositivityLevel : ProofLevel
osterwalderSeilerLatticeGaugeReflectionPositivityLevel = standardImported

menottiPelissettoWilsonSitePlaneReflectionPositivityLevel : ProofLevel
menottiPelissettoWilsonSitePlaneReflectionPositivityLevel = standardImported

-- The finite sum-of-modular-squares implication itself is local algebra.
finiteReflectionSquareFactorizationImpliesPositivityLevel : ProofLevel
finiteReflectionSquareFactorizationImpliesPositivityLevel = machineChecked

-- This is the actual source-facing seam: derive the reflection-square
-- factorization for the SAME literal Wilson action/background/cutoff carrier
-- used by the Bałaban RG construction.
literalDASHIWilsonReflectionSquareIdentificationLevel : ProofLevel
literalDASHIWilsonReflectionSquareIdentificationLevel = conditional

-- Continuum OS positivity additionally requires convergence of the reflected
-- observable products on the common continuum subsequence.  Lattice RP alone
-- is therefore not silently promoted to continuum RP.
continuumReflectionPositivityPassageLevel : ProofLevel
continuumReflectionPositivityPassageLevel = conditional
