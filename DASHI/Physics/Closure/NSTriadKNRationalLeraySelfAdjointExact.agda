module DASHI.Physics.Closure.NSTriadKNRationalLeraySelfAdjointExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- Acta Mathematica 63 (1934), 193--248.
-- DOI: 10.1007/BF02547354.
--
-- PURPOSE
-- Complete the exact rational Leray package with self-adjointness and removal
-- of the projector against a transverse test vector.  Both theorems concern
-- the literal rank-one formula from NSTriadKNRationalLerayProjectionExact;
-- no abstract orthogonal-projection law is assumed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as Leray

projectSelfAdjoint :
  (data : Leray.ProjectionMode) →
  (left right : Leray.Vector3) →
  Leray.dot left (Leray.project data right)
  ≡ Leray.dot (Leray.project data left) right
projectSelfAdjoint data left right
  with Leray.mode data | left | right
... | Leray.v3 mx my mz
    | Leray.v3 lx ly lz
    | Leray.v3 rx ry rz =
  solve
    ( mx ∷ my ∷ mz
    ∷ lx ∷ ly ∷ lz
    ∷ rx ∷ ry ∷ rz
    ∷ Leray.inverseNormSquared data
    ∷ []
    )

removeProjectorAgainstTransverseTest :
  (data : Leray.ProjectionMode) →
  (test value : Leray.Vector3) →
  Leray.dot (Leray.mode data) test ≡ 0ℚ →
  Leray.dot test (Leray.project data value)
  ≡ Leray.dot test value
removeProjectorAgainstTransverseTest data test value transverse =
  trans
    (projectSelfAdjoint data test value)
    (cong
      (λ projectedTest → Leray.dot projectedTest value)
      (Leray.projectFixesTransverse data test transverse))

rationalLeraySelfAdjointClosed : Bool
rationalLeraySelfAdjointClosed = true

rationalLerayTransverseTestRemovalClosed : Bool
rationalLerayTransverseTestRemovalClosed = true

rationalLeraySelfAdjointClosedIsTrue :
  rationalLeraySelfAdjointClosed ≡ true
rationalLeraySelfAdjointClosedIsTrue = refl

rationalLerayTransverseTestRemovalClosedIsTrue :
  rationalLerayTransverseTestRemovalClosed ≡ true
rationalLerayTransverseTestRemovalClosedIsTrue = refl
