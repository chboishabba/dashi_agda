module DASHI.Moonshine.P11Level44TwoAdicFixedVectorSeparationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kimball Martin,
-- "The basis problem revisited", Transactions of the American Mathematical
-- Society 373 (2020), 4523--4559. DOI: 10.1090/tran/8077.
--
-- Martin's classical Jacquet--Langlands formulation is deliberately important
-- here for a NEGATIVE reason: on oldspaces the JL map is not canonical.  The
-- quaternionic and classical spaces decompose into local fixed-vector spaces
-- pi_f^K, and away-from-level Hecke preservation does not identify two
-- different choices of compact-open K as the same concrete fixed-vector
-- subspace.
--
-- Fred Diamond and Jerry Shurman,
-- "A First Course in Modular Forms", Graduate Texts in Mathematics 228,
-- Springer, 2005. DOI: 10.1007/978-0-387-27226-9.
-- Classical degeneracy maps / oldforms and local level structure.
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups", Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
-- The natural action of GL_2(F_2) on P^1(F_2) is the three-point permutation
-- representation of S_3 = 1 + std.
--
-- DASHI CONTRIBUTION
--
-- Correct the p=11 level-44 comparison target before promoting a false
-- same-object theorem.
--
-- The marked full-level-2 carrier has a genuine deck S3 action.  Its
-- three-dimensional level-11 Hecke-isotypic block is therefore naturally a
-- PRINCIPAL-LEVEL-2 local fixed-vector model.  By contrast, the familiar
-- classical oldforms
--
--   f(z), f(2z), f(4z)
--
-- are the Gamma_0(4) degeneracy model.  These may realize the same GLOBAL
-- automorphic representation and the same good-prime Hecke eigencharacter
-- without being the same local fixed-vector subspace.
--
-- This file constructs the finite local geometry explicitly:
--
--   P^1(F_2) = {(1,0),(0,1),(1,1)},
--
-- with matrix generators
--
--   r = [[0,1],[1,1]],       s = [[1,1],[0,1]],
--
-- satisfying r^3=s^2=1 and srs=r^-1.  Their action is exactly the existing
-- Old3 permutation action and, through the already-constructed marked
-- realization, exactly the actual marked deck action.
--
-- The second result is an explicit no-collapse theorem:
-- sharing the same Old3 coordinate vector does NOT identify the
-- principal-level-2 and Gamma_0(4) local realization roles.
--
-- Consequently the remaining source theorem is now more precise than the old
-- phrase "analytic oldspace = marked oldspace": one must construct the local
-- 2-adic comparison inside the SAME global automorphic representation and say
-- exactly how the K(2)-fixed and K_0(4)-fixed models are related.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Moonshine.P11MarkedLevel44PermutationIntertwinerExact as Marked
import DASHI.Moonshine.P11MarkedLevel44PermutationOldspaceExact as Perm

------------------------------------------------------------------------
-- F_2 and an explicit GL_2(F_2) generator pair.
------------------------------------------------------------------------

data F2 : Set where
  f0 f1 : F2

_+₂_ : F2 → F2 → F2
f0 +₂ y = y
f1 +₂ f0 = f1
f1 +₂ f1 = f0

_*₂_ : F2 → F2 → F2
f0 *₂ y = f0
f1 *₂ y = y

record Vec2F2 : Set where
  constructor vec2
  field
    first second : F2
open Vec2F2 public

record Mat2F2 : Set where
  constructor mat2
  field
    a11 a12 a21 a22 : F2
open Mat2F2 public

actMatrix : Mat2F2 → Vec2F2 → Vec2F2
actMatrix M v = vec2
  ((a11 M *₂ first v) +₂ (a12 M *₂ second v))
  ((a21 M *₂ first v) +₂ (a22 M *₂ second v))

identityMatrix : Mat2F2
identityMatrix = mat2 f1 f0 f0 f1

rotationMatrix : Mat2F2
rotationMatrix = mat2 f0 f1 f1 f1

reflectionMatrix : Mat2F2
reflectionMatrix = mat2 f1 f1 f0 f1

------------------------------------------------------------------------
-- P^1(F_2).  Since F_2^x={1}, the three nonzero vectors are literally the
-- three projective points; no scalar quotient remains to perform.
------------------------------------------------------------------------

data P1F2 : Set where
  point1 point2 point4 : P1F2

p1Vector : P1F2 → Vec2F2
p1Vector point1 = vec2 f1 f0
p1Vector point2 = vec2 f0 f1
p1Vector point4 = vec2 f1 f1

rotateP1 : P1F2 → P1F2
rotateP1 point1 = point2
rotateP1 point2 = point4
rotateP1 point4 = point1

reflectP1 : P1F2 → P1F2
reflectP1 point1 = point1
reflectP1 point2 = point4
reflectP1 point4 = point2

rotationMatrixActsAsRotateP1 :
  (x : P1F2) →
  actMatrix rotationMatrix (p1Vector x) ≡ p1Vector (rotateP1 x)
rotationMatrixActsAsRotateP1 point1 = refl
rotationMatrixActsAsRotateP1 point2 = refl
rotationMatrixActsAsRotateP1 point4 = refl

reflectionMatrixActsAsReflectP1 :
  (x : P1F2) →
  actMatrix reflectionMatrix (p1Vector x) ≡ p1Vector (reflectP1 x)
reflectionMatrixActsAsReflectP1 point1 = refl
reflectionMatrixActsAsReflectP1 point2 = refl
reflectionMatrixActsAsReflectP1 point4 = refl

rotateP1Cube : (x : P1F2) → rotateP1 (rotateP1 (rotateP1 x)) ≡ x
rotateP1Cube point1 = refl
rotateP1Cube point2 = refl
rotateP1Cube point4 = refl

reflectP1Square : (x : P1F2) → reflectP1 (reflectP1 x) ≡ x
reflectP1Square point1 = refl
reflectP1Square point2 = refl
reflectP1Square point4 = refl

reflectRotateReflect :
  (x : P1F2) →
  reflectP1 (rotateP1 (reflectP1 x)) ≡ rotateP1 (rotateP1 x)
reflectRotateReflect point1 = refl
reflectRotateReflect point2 = refl
reflectRotateReflect point4 = refl

------------------------------------------------------------------------
-- Exact identification with the existing Old3 three-copy permutation module.
-- The names 1,2,4 remain coordinate labels here; this theorem does NOT turn
-- the analytic degeneracy forms into deck points.
------------------------------------------------------------------------

p1Basis : P1F2 → Marked.Old3
p1Basis point1 = Marked.oldBasis1
p1Basis point2 = Marked.oldBasis2
p1Basis point4 = Marked.oldBasis4

oldRIsP1Rotation :
  (x : P1F2) →
  Marked.oldR (p1Basis x) ≡ p1Basis (rotateP1 x)
oldRIsP1Rotation point1 = refl
oldRIsP1Rotation point2 = refl
oldRIsP1Rotation point4 = refl

oldSIsP1Reflection :
  (x : P1F2) →
  Marked.oldS (p1Basis x) ≡ p1Basis (reflectP1 x)
oldSIsP1Reflection point1 = refl
oldSIsP1Reflection point2 = refl
oldSIsP1Reflection point4 = refl

------------------------------------------------------------------------
-- The same finite generators act on the ACTUAL marked five-state carrier via
-- the source-native deck action already proved on the branch.
------------------------------------------------------------------------

markedDeckRotationFromP1 :
  (x : P1F2) →
  Marked.realizeOld3 (p1Basis (rotateP1 x))
  ≡ Perm.deckR5 (Marked.realizeOld3 (p1Basis x))
markedDeckRotationFromP1 x =
  trans
    (cong Marked.realizeOld3 (sym (oldRIsP1Rotation x)))
    (Marked.realizeDeckR (p1Basis x))

markedDeckReflectionFromP1 :
  (x : P1F2) →
  Marked.realizeOld3 (p1Basis (reflectP1 x))
  ≡ Perm.deckS5 (Marked.realizeOld3 (p1Basis x))
markedDeckReflectionFromP1 x =
  trans
    (cong Marked.realizeOld3 (sym (oldSIsP1Reflection x)))
    (Marked.realizeDeckS (p1Basis x))

------------------------------------------------------------------------
-- Two different local fixed-vector roles.
--
-- principalLevel2K2:
--   the full-level-2 / principal-congruence realization carrying the genuine
--   GL_2(F_2)=S3 deck action.
--
-- gamma0FourK0:
--   the classical degeneracy realization f(z),f(2z),f(4z).
--
-- They can be two realizations of one automorphic representation without being
-- definitionally or canonically the same local subspace.
------------------------------------------------------------------------

data TwoAdicFixedVectorRole : Set where
  principalLevel2K2 gamma0FourK0 : TwoAdicFixedVectorRole

data Impossible : Set where

rolesAreDistinct : principalLevel2K2 ≡ gamma0FourK0 → Impossible
rolesAreDistinct ()

record LocalOld3Presentation : Set where
  constructor localPresentation
  field
    role : TwoAdicFixedVectorRole
    coordinates : Marked.Old3
open LocalOld3Presentation public

markedLocalPresentation : Marked.Old3 → LocalOld3Presentation
markedLocalPresentation v = localPresentation principalLevel2K2 v

analyticDegeneracyPresentation : Marked.Old3 → LocalOld3Presentation
analyticDegeneracyPresentation v = localPresentation gamma0FourK0 v

forgetLocalRole : LocalOld3Presentation → Marked.Old3
forgetLocalRole = coordinates

sameOld3AfterForgettingRole :
  (v : Marked.Old3) →
  forgetLocalRole (markedLocalPresentation v)
  ≡ forgetLocalRole (analyticDegeneracyPresentation v)
sameOld3AfterForgettingRole v = refl

sameCoordinatesDoNotIdentifyLocalRealization :
  (v : Marked.Old3) →
  markedLocalPresentation v ≡ analyticDegeneracyPresentation v → Impossible
sameCoordinatesDoNotIdentifyLocalRealization v equality =
  rolesAreDistinct (cong role equality)

------------------------------------------------------------------------
-- Boundary / corrected frontier.
------------------------------------------------------------------------

record P11Level44TwoAdicFixedVectorBoundary : Set where
  field
    explicitP1F2CarrierConstructed : Bool
    explicitGL2F2GeneratorsConstructed : Bool
    s3RelationsProvedOnP1F2 : Bool
    old3PermutationIdentifiedWithP1F2 : Bool
    markedDeckActionIdentifiedWithP1F2 : Bool
    sharedOld3CoordinatesIdentifyLocalRole : Bool
    analyticGamma0FourDeckActionSourceConstructed : Bool
    localK2ToK0FourAutomorphicComparisonConstructed : Bool

canonicalP11Level44TwoAdicFixedVectorBoundary :
  P11Level44TwoAdicFixedVectorBoundary
canonicalP11Level44TwoAdicFixedVectorBoundary = record
  { explicitP1F2CarrierConstructed = true
  ; explicitGL2F2GeneratorsConstructed = true
  ; s3RelationsProvedOnP1F2 = true
  ; old3PermutationIdentifiedWithP1F2 = true
  ; markedDeckActionIdentifiedWithP1F2 = true
  ; sharedOld3CoordinatesIdentifyLocalRole = false
  ; analyticGamma0FourDeckActionSourceConstructed = false
  ; localK2ToK0FourAutomorphicComparisonConstructed = false
  }
