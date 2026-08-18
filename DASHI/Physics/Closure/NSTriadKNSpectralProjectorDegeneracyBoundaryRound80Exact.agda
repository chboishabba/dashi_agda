module DASHI.Physics.Closure.NSTriadKNSpectralProjectorDegeneracyBoundaryRound80Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Chandler Davis; W. M. Kahan.
-- Title: "The Rotation of Eigenvectors by a Perturbation. III".
-- SIAM Journal on Numerical Analysis 7 (1970), 1--46.
-- DOI: 10.1137/0707001.
--
-- Author: Tosio Kato.
-- Title: "Perturbation Theory for Linear Operators", 2nd ed.
-- DOI: 10.1007/978-3-642-66282-9.
--
-- ROUND80 / PROJECTOR CORRECTION
--
-- Projectors remove the arbitrary choice of a basis INSIDE a degenerate
-- eigenspace, but they do not manufacture a separated nontrivial spectral
-- cluster.  At the Round79 pure-rotation point S=0, every subspace is
-- invariant.  In particular two distinct rank-one orthogonal projectors are
-- both perfectly legitimate invariant projectors of the same zero strain.
--
-- Hence there is no canonical e2/e3 line projector at complete degeneracy.
-- The only basis-independent projector determined by the whole degenerate
-- spectrum is the full-space projector I, which contains no directional
-- e2/e3 information.  Davis--Kahan therefore replaces an individual-vector
-- gap by a CLUSTER-vs-COMPLEMENT gap; it does not remove separation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Physics.Closure.NSTriadKNLuoAngularStrainDisplayedFormulaZeroExact as M

zeroM : M.Matrix3
zeroM = M.zeroMatrix

identityM : M.Matrix3
identityM = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 1ℚ

p1 p2 : M.Matrix3
p1 = M.matrix3
  1ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

p2 = M.matrix3
  0ℚ 0ℚ 0ℚ
  0ℚ 1ℚ 0ℚ
  0ℚ 0ℚ 0ℚ

mul : M.Matrix3 → M.Matrix3 → M.Matrix3
mul a b = M.matrix3
  (M.m11 a * M.m11 b + M.m12 a * M.m21 b + M.m13 a * M.m31 b)
  (M.m11 a * M.m12 b + M.m12 a * M.m22 b + M.m13 a * M.m32 b)
  (M.m11 a * M.m13 b + M.m12 a * M.m23 b + M.m13 a * M.m33 b)
  (M.m21 a * M.m11 b + M.m22 a * M.m21 b + M.m23 a * M.m31 b)
  (M.m21 a * M.m12 b + M.m22 a * M.m22 b + M.m23 a * M.m32 b)
  (M.m21 a * M.m13 b + M.m22 a * M.m23 b + M.m23 a * M.m33 b)
  (M.m31 a * M.m11 b + M.m32 a * M.m21 b + M.m33 a * M.m31 b)
  (M.m31 a * M.m12 b + M.m32 a * M.m22 b + M.m33 a * M.m32 b)
  (M.m31 a * M.m13 b + M.m32 a * M.m23 b + M.m33 a * M.m33 b)

record InvariantProjector (operator projector : M.Matrix3) : Set where
  field
    idempotent : mul projector projector ≡ projector
    commutes : mul operator projector ≡ mul projector operator

open InvariantProjector public

p1Idempotent : mul p1 p1 ≡ p1
p1Idempotent =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

p2Idempotent : mul p2 p2 ≡ p2
p2Idempotent =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

zeroCommutesP1 : mul zeroM p1 ≡ mul p1 zeroM
zeroCommutesP1 =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

zeroCommutesP2 : mul zeroM p2 ≡ mul p2 zeroM
zeroCommutesP2 =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

p1InvariantAtCompleteDegeneracy : InvariantProjector zeroM p1
p1InvariantAtCompleteDegeneracy = record
  { idempotent = p1Idempotent
  ; commutes = zeroCommutesP1
  }

p2InvariantAtCompleteDegeneracy : InvariantProjector zeroM p2
p2InvariantAtCompleteDegeneracy = record
  { idempotent = p2Idempotent
  ; commutes = zeroCommutesP2
  }

-- Any proposed rule saying that complete degeneracy itself determines one
-- rank-one invariant projector must identify p1 and p2, hence 1 = 0 in the
-- (1,1) entry.  We keep the contradiction as an exact equality target rather
-- than depending on a particular rational inequality library lemma.
record CompleteDegeneracyDeterminesUniqueInvariantProjector : Set where
  field
    unique :
      (left right : M.Matrix3) →
      InvariantProjector zeroM left →
      InvariantProjector zeroM right →
      left ≡ right

open CompleteDegeneracyDeterminesUniqueInvariantProjector public

completeDegeneracyCannotSelectUniqueRankOneLine :
  CompleteDegeneracyDeterminesUniqueInvariantProjector →
  1ℚ ≡ 0ℚ
completeDegeneracyCannotSelectUniqueRankOneLine selector =
  cong M.m11
    (unique selector p1 p2
      p1InvariantAtCompleteDegeneracy
      p2InvariantAtCompleteDegeneracy)

-- The full-space projector is canonical at total degeneracy but deliberately
-- carries only the entire three-dimensional cluster.
identityIdempotent : mul identityM identityM ≡ identityM
identityIdempotent =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

zeroCommutesIdentity : mul zeroM identityM ≡ mul identityM zeroM
zeroCommutesIdentity =
  M.matrixExt (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])
              (solve []) (solve []) (solve [])

fullDegenerateClusterProjector : InvariantProjector zeroM identityM
fullDegenerateClusterProjector = record
  { idempotent = identityIdempotent
  ; commutes = zeroCommutesIdentity
  }

round80ProjectorsRemoveInternalBasisChoice : Bool
round80ProjectorsRemoveInternalBasisChoice = true

round80ProjectorsRemoveNeedForClusterComplementGap : Bool
round80ProjectorsRemoveNeedForClusterComplementGap = false

round80CompleteDegeneracyDeterminesDirectionalLineProjector : Bool
round80CompleteDegeneracyDeterminesDirectionalLineProjector = false

round80ProjectorsRemoveNeedForClusterComplementGapIsFalse :
  round80ProjectorsRemoveNeedForClusterComplementGap ≡ false
round80ProjectorsRemoveNeedForClusterComplementGapIsFalse = refl
