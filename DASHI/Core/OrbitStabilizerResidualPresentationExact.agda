module DASHI.Core.OrbitStabilizerResidualPresentationExact where

------------------------------------------------------------------------
-- ORBIT QUOTIENT + STABILIZER-INDEXED RESIDUAL PRESENTATION
--
-- DASHI repeatedly uses exact codes of the form
--
--   fine state ~= Sigma orbit (residual orbit).
--
-- For a symmetry action, the residual over an orbit is naturally a presentation
-- of G / Stab(representative).  Agda has no built-in quotient type, so this
-- module does not pretend to construct raw cosets by definitional equality.
-- Instead it requires a code whose equality is sound and complete for
--
--   g ~ h  iff  g.representative = h.representative.
--
-- That is exactly the action-kernel equivalence defining the stabilizer coset.
-- A chosen group representative for each residual class then gives an exact
-- reopen theorem.  Fibre cardinality may vary with stabilizer type.
--
-- SOURCE / METHOD CALIBRATION
--
-- Jean-Pierre Serre, "Linear Representations of Finite Groups",
-- Graduate Texts in Mathematics 42, Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- The theorem below is elementary group-action mathematics.  The citation is
-- calibration for orbit/stabilizer/representation terminology.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DependentRecoverableProjectionExact as Recoverable
import DASHI.Core.ResidualSymmetryCollisionFibreExact as Symmetry

record OrbitPresentation
    {State Group : Set}
    (action : Symmetry.InvertibleSymmetryAction State Group) : Set₁ where
  constructor orbitPresentation
  field
    Orbit : Set
    orbitOf : State -> Orbit
    representative : Orbit -> State

    orbitInvariant :
      (g : Group) (state : State) ->
      orbitOf (Symmetry.act action g state) ≡ orbitOf state

    representativeInOrbit :
      (orbit : Orbit) ->
      orbitOf (representative orbit) ≡ orbit

    transporter : State -> Group
    transporterHits :
      (state : State) ->
      Symmetry.act action
        (transporter state)
        (representative (orbitOf state))
      ≡ state

open OrbitPresentation public

StabilizerEquivalent :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group} ->
  (presentation : OrbitPresentation action) ->
  (orbit : Orbit presentation) ->
  Group -> Group -> Set
StabilizerEquivalent {action = action} presentation orbit g h =
  Symmetry.act action g (representative presentation orbit)
  ≡ Symmetry.act action h (representative presentation orbit)

record StabilizerResidualPresentation
    {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    (orbitPresentation : OrbitPresentation action) : Set₁ where
  constructor stabilizerResidualPresentation
  field
    Residual : Orbit orbitPresentation -> Set

    groupClass :
      (orbit : Orbit orbitPresentation) ->
      Group ->
      Residual orbit

    classEqualitySound :
      ∀ {orbit g h} ->
      groupClass orbit g ≡ groupClass orbit h ->
      StabilizerEquivalent orbitPresentation orbit g h

    classEqualityComplete :
      ∀ {orbit g h} ->
      StabilizerEquivalent orbitPresentation orbit g h ->
      groupClass orbit g ≡ groupClass orbit h

    chooseGroup :
      (orbit : Orbit orbitPresentation) ->
      Residual orbit ->
      Group

    chooseGroupRightInverse :
      (orbit : Orbit orbitPresentation)
      (residual : Residual orbit) ->
      groupClass orbit (chooseGroup orbit residual) ≡ residual

open StabilizerResidualPresentation public

orbitResidualOf :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    {orbitPresentation : OrbitPresentation action} ->
  (residualPresentation :
    StabilizerResidualPresentation orbitPresentation) ->
  (state : State) ->
  Residual residualPresentation (orbitOf orbitPresentation state)
orbitResidualOf {orbitPresentation = orbitPresentation}
  residualPresentation state =
  groupClass residualPresentation
    (orbitOf orbitPresentation state)
    (transporter orbitPresentation state)

reopenOrbitResidual :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    {orbitPresentation : OrbitPresentation action} ->
  (residualPresentation :
    StabilizerResidualPresentation orbitPresentation) ->
  (orbit : Orbit orbitPresentation) ->
  Residual residualPresentation orbit ->
  State
reopenOrbitResidual {action = action} {orbitPresentation = orbitPresentation}
  residualPresentation orbit residual =
  Symmetry.act action
    (chooseGroup residualPresentation orbit residual)
    (representative orbitPresentation orbit)

orbitResidualReopensExactly :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    {orbitPresentation : OrbitPresentation action}
    (residualPresentation :
      StabilizerResidualPresentation orbitPresentation)
    (state : State) ->
  reopenOrbitResidual residualPresentation
    (orbitOf orbitPresentation state)
    (orbitResidualOf residualPresentation state)
  ≡ state
orbitResidualReopensExactly
  {action = action}
  {orbitPresentation = orbitPresentation}
  residualPresentation state =
  trans
    (classEqualitySound residualPresentation
      (chooseGroupRightInverse residualPresentation
        (orbitOf orbitPresentation state)
        (orbitResidualOf residualPresentation state)))
    (transporterHits orbitPresentation state)

orbitStabilizerDependentRecoverableProjection :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    (orbitPresentation : OrbitPresentation action)
    (residualPresentation :
      StabilizerResidualPresentation orbitPresentation) ->
  Recoverable.DependentExactRecoverableProjection
    State
    (Orbit orbitPresentation)
orbitStabilizerDependentRecoverableProjection
  orbitPresentation residualPresentation =
  Recoverable.dependentExactRecoverableProjection
    (Residual residualPresentation)
    (orbitOf orbitPresentation)
    (orbitResidualOf residualPresentation)
    (reopenOrbitResidual residualPresentation)
    (orbitResidualReopensExactly residualPresentation)

orbitPlusStabilizerResidualSeparatesFineCarrier :
  ∀ {State Group : Set}
    {action : Symmetry.InvertibleSymmetryAction State Group}
    (orbitPresentation : OrbitPresentation action)
    (residualPresentation :
      StabilizerResidualPresentation orbitPresentation) ->
  Recoverable.DependentCodeSeparating
    (orbitStabilizerDependentRecoverableProjection
      orbitPresentation residualPresentation)
orbitPlusStabilizerResidualSeparatesFineCarrier
  orbitPresentation residualPresentation =
  Recoverable.dependentCodeSeparating
    (orbitStabilizerDependentRecoverableProjection
      orbitPresentation residualPresentation)

record OrbitStabilizerResidualBoundary : Set where
  constructor orbitStabilizerResidualBoundary
  field
    quotientAloneAlwaysReconstructs : Bool
    stabilizerResidualMayDependOnOrbit : Bool
    quotientPlusResidualReopensExactly : Bool
    rawCosetQuotientTypeConstructedDefinitionally : Bool
    sameResidualCardinalityForcedOnEveryOrbitType : Bool

canonicalOrbitStabilizerResidualBoundary : OrbitStabilizerResidualBoundary
canonicalOrbitStabilizerResidualBoundary =
  orbitStabilizerResidualBoundary false true true false false
