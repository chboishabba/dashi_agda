module DASHI.Physics.Closure.NSTriadKNPhysicalProjectorDefectRound37Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier--Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and
-- Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
--
-- DASHI CONTRIBUTION
--
-- Connect the orientation-free line-projector defect to the repository's
-- already physical, amplitude-weighted vorticity interaction.  For
--
--   omega_x = a xi,  omega_y = b eta,
--
-- with unit directions, the existing physical theorem proves
--
--   |omega_x cross omega_y|^2 = a^2 b^2 Theta(xi,eta).
--
-- Round 37 proves
--
--   ||Pi_xi-Pi_eta||_F^2 = 2 Theta(xi,eta).
--
-- This module combines the two without division:
--
--   a^2 b^2 ||Pi_xi-Pi_eta||_F^2
--     = 2 |omega_x cross omega_y|^2.
--
-- Thus the projector/stabilizer formulation preserves the exact physical
-- amplitude weights needed in a PV strain estimate; it is not merely a
-- normalized angular picture.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSTriadKNRationalLerayProjectionExact as V
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoDirectionalDefectGramExact as Gram
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalDirectionalDefectExact as Physical
import DASHI.Physics.Closure.NSTriadKNDirectionalProjectorStabilizerRound37Exact as Projector

toProjectorVector : Gram.Vec3 → V.Vector3
toProjectorVector vector =
  V.v3 (Gram.x vector) (Gram.y vector) (Gram.z vector)

normMeaning : ∀ vector →
  V.normSquared (toProjectorVector vector) ≡ Gram.normSquared vector
normMeaning vector = refl

dotMeaning : ∀ left right →
  V.dot (toProjectorVector left) (toProjectorVector right)
  ≡ Gram.dot left right
dotMeaning left right = refl

toProjectorUnit :
  (vector : Gram.Vec3) →
  Gram.normSquared vector ≡ Projector.one →
  Projector.UnitDirection
toProjectorUnit vector unit =
  Projector.unit-direction
    (toProjectorVector vector)
    (trans (normMeaning vector) unit)
  where
  Projector.one = _
