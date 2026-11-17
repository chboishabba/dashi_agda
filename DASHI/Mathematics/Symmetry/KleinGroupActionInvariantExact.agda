module DASHI.Mathematics.Symmetry.KleinGroupActionInvariantExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Felix Klein,
-- "Vergleichende Betrachtungen über neuere geometrische Forschungen"
-- (the Erlangen Programme, 1872).  No DOI was assigned to the original.
--
-- Jeremy J. Gray,
-- "Felix Klein's Erlangen Program, 'Comparative considerations of recent
-- geometrical researches' (1872)", in Landmark Writings in Western
-- Mathematics 1640--1940.
-- DOI: 10.1016/B978-044450871-3/50123-6.
--
-- Lizhen Ji and Athanase Papadopoulos, editors,
-- "Sophus Lie and Felix Klein: The Erlangen Program and Its Impact in
-- Mathematics and Physics".
-- DOI: 10.4171/148.
--
-- DASHI CONTRIBUTION
--
-- Package the reusable exact core of the Erlangen viewpoint: an action, an
-- observable invariant under that action, and the theorem that the observable
-- is constant on every witnessed orbit.  This is the correct common surface
-- for rigid geometry, gauge equivalence, and Navier--Stokes scaling actions.
--
-- The record takes the group/action laws as explicit fields.  It does not
-- manufacture a quotient, Lie differentiation, Haar measure, gauge fixing, or
-- a moduli-space regularity theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

record GroupAction : Set₁ where
  field
    G X : Set
    identity : G
    compose : G → G → G
    act : G → X → X
    identityActs : ∀ x → act identity x ≡ x
    composeActs : ∀ g h x →
      act (compose g h) x ≡ act g (act h x)

open GroupAction public

Invariant : (actionData : GroupAction) →
  (X actionData → ℚ) → Set
Invariant actionData observable =
  ∀ groupElement point →
    observable (act actionData groupElement point) ≡ observable point

invariantUnderComposite :
  ∀ actionData observable →
  Invariant actionData observable →
  ∀ g h point →
  observable (act actionData (compose actionData g h) point)
  ≡ observable point
invariantUnderComposite actionData observable invariant g h point =
  trans
    (cong observable (composeActs actionData g h point))
    (trans
      (invariant g (act actionData h point))
      (invariant h point))

invariantUnderIdentity :
  ∀ actionData observable →
  Invariant actionData observable →
  ∀ point →
  observable (act actionData (identity actionData) point)
  ≡ observable point
invariantUnderIdentity actionData observable invariant point =
  invariant (identity actionData) point

record SameOrbit (actionData : GroupAction)
    (left right : X actionData) : Set where
  constructor orbitWitness
  field
    transform : G actionData
    reaches : act actionData transform left ≡ right

open SameOrbit public

identityOrbitWitness : ∀ actionData point →
  SameOrbit actionData point point
identityOrbitWitness actionData point =
  orbitWitness
    (identity actionData)
    (identityActs actionData point)

composeOrbitWitness :
  ∀ actionData {firstPoint secondPoint thirdPoint} →
  SameOrbit actionData firstPoint secondPoint →
  SameOrbit actionData secondPoint thirdPoint →
  SameOrbit actionData firstPoint thirdPoint
composeOrbitWitness actionData
    (orbitWitness firstTransform firstReaches)
    (orbitWitness secondTransform secondReaches) =
  orbitWitness
    (compose actionData secondTransform firstTransform)
    (trans
      (composeActs actionData secondTransform firstTransform _)
      (trans
        (cong (act actionData secondTransform) firstReaches)
        secondReaches))

invariantOnOrbit :
  ∀ actionData observable →
  Invariant actionData observable →
  ∀ {left right} →
  SameOrbit actionData left right →
  observable right ≡ observable left
invariantOnOrbit actionData observable invariant
    (orbitWitness transform reaches) =
  trans
    (sym (cong observable reaches))
    (invariant transform _)

record InvariantGeometry : Set₁ where
  field
    transformationAction : GroupAction
    geometricObservable : X transformationAction → ℚ
    geometricInvariant :
      Invariant transformationAction geometricObservable

open InvariantGeometry public

geometryConstantOnWitnessedOrbit :
  ∀ geometry {left right} →
  SameOrbit (transformationAction geometry) left right →
  geometricObservable geometry right
  ≡ geometricObservable geometry left
geometryConstantOnWitnessedOrbit geometry =
  invariantOnOrbit
    (transformationAction geometry)
    (geometricObservable geometry)
    (geometricInvariant geometry)
