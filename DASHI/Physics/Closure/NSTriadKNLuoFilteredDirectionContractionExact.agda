module DASHI.Physics.Closure.NSTriadKNLuoFilteredDirectionContractionExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Author: Runlong Yu.
-- Title: "Filtered Vortex Stretching and Subgrid Defects for the
-- Three-Dimensional Navier-Stokes Equations".
-- DOI: 10.48550/arXiv.2606.27560.
-- Status: arXiv preprint, submitted 25 June 2026.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Yu's exact strain-kernel contraction contains
--
--   |(xi . r) (xi x r)| <= 1/2
--
-- for unit directions xi and r.  The repository proves the radical-free
-- squared form exactly:
--
--   4 (xi.r)^2 |xi x r|^2 <= 1.
--
-- The proof is the sharp defect factorization
--
--   1 - 4 c^2 (1-c^2) = (1-2c^2)^2 >= 0.
--
-- This closes the finite angular constant in the filtered near-field kernel;
-- the principal-value integration and physical 3/(4 pi) normalization remain
-- analytic rather than rational-algebraic obligations.
------------------------------------------------------------------------

open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram

record UnitDirectionRadialPair : Set where
  constructor unitDirectionRadialPair
  field
    direction radial : Gram.Vec3
    directionUnit : Gram.normSquared direction ≡ 1ℚ
    radialUnit : Gram.normSquared radial ≡ 1ℚ

open UnitDirectionRadialPair public

asUnitPair : UnitDirectionRadialPair → Gram.UnitDirectionPair
asUnitPair pair =
  Gram.unit-direction-pair
    (direction pair)
    (radial pair)
    (directionUnit pair)
    (radialUnit pair)

cosineSquared : UnitDirectionRadialPair → ℚ
cosineSquared pair =
  L2.square (Gram.dot (direction pair) (radial pair))

sineSquared : UnitDirectionRadialPair → ℚ
sineSquared pair =
  Gram.crossNormSquared (direction pair) (radial pair)

sineSquaredMeaning :
  ∀ pair →
  sineSquared pair ≡ 1ℚ - cosineSquared pair
sineSquaredMeaning pair =
  sym (Gram.directionalDefectEqualsCrossSquare (asUnitPair pair))

contractionDefect : UnitDirectionRadialPair → ℚ
contractionDefect pair =
  L2.square (1ℚ - 2 * cosineSquared pair)

sharpContractionIdentity :
  ∀ pair →
  4 * cosineSquared pair * sineSquared pair
    + contractionDefect pair
  ≡ 1ℚ
sharpContractionIdentity pair
  rewrite sineSquaredMeaning pair =
  solve (cosineSquared pair ∷ [])

filteredDirectionContractionSquaredBound :
  ∀ pair →
  4 * cosineSquared pair * sineSquared pair ≤ 1ℚ
filteredDirectionContractionSquaredBound pair =
  let
    contraction = 4 * cosineSquared pair * sineSquared pair
    defect = contractionDefect pair

    addDefect : contraction + 0ℚ ≤ contraction + defect
    addDefect =
      ℚₚ.+-monoʳ-≤
        contraction
        (L2.squareNonnegative
          (1ℚ - 2 * cosineSquared pair))

    leftClosed : contraction + 0ℚ ≡ contraction
    leftClosed = solve (contraction ∷ [])

    normalized : contraction ≤ contraction + defect
    normalized =
      subst
        (λ left → left ≤ contraction + defect)
        leftClosed
        addDefect
  in
  subst
    (λ upper → contraction ≤ upper)
    (sharpContractionIdentity pair)
    normalized

record FilteredContractionAuthorityBoundary : Set where
  constructor filteredContractionAuthorityBoundary
  field
    sharpAngularFactorProved : Set
    principalValueContractionIntegrated : Set
    periodicKernelNormalizationProved : Set

canonicalFilteredContractionAuthorityBoundary :
  FilteredContractionAuthorityBoundary
canonicalFilteredContractionAuthorityBoundary =
  filteredContractionAuthorityBoundary ⊤ ⊥ ⊥
  where
  open import Data.Unit using (⊤)
  open import Data.Empty using (⊥)
