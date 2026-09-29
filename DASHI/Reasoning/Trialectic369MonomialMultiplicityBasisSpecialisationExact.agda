module DASHI.Reasoning.Trialectic369MonomialMultiplicityBasisSpecialisationExact where

------------------------------------------------------------------------
-- OPTIONAL MONOMIAL FIN90 SPECIALISATION OF THE CANONICAL LINEAR ROUTE
--
-- The canonical 3B multiplicity is S_zeta = Hom_E(H_zeta,W_zeta).
-- The source-attributed central-phase character rules out the historical
-- PURE 90-point permutation representation; it does not by itself rule out
-- a MONOMIAL representation with explicit scalar multipliers.
--
-- This module therefore keeps BOTH the index map and phase/scale. The
-- scalar multipliers cannot be erased without a separate same-object proof.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans)

import DASHI.Geometry.HilbertLorentzForcing as Linear
import DASHI.Wikimedia.IbrahimMonster3BMultiplicityBasisLinearWrongTypeCorrectionExact as WrongType
import DASHI.Wikimedia.IbrahimMonster3BSuzukiNinetyPermutationCharacterNoGoExact as NoGo

RouteGroup :
  WrongType.CanonicalLinearMultiplicityRoute → Set
RouteGroup route =
  Linear.Group
    (WrongType.linearAction
      (WrongType.linearRepresentation route))

record MonomialMultiplicityBasisSpecialisation
    (route : WrongType.CanonicalLinearMultiplicityRoute) : Set₁ where
  field
    basisVector :
      Fin 90 →
      Linear.Vector
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))

    basisComplete : Set
    basisIndependent : Set

    indexAct : RouteGroup route → Fin 90 → Fin 90
    scalarAct :
      RouteGroup route →
      Fin 90 →
      Linear.Scalar
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))

    actionOnBasisIsMonomial :
      (g : RouteGroup route) →
      (index : Fin 90) →
      Linear.act
        (WrongType.linearAction
          (WrongType.linearRepresentation route))
        g (basisVector index)
      ≡
      Linear._·_
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))
        (scalarAct g index)
        (basisVector (indexAct g index))

open MonomialMultiplicityBasisSpecialisation public

-- A genuine monomial basis has nonzero coefficients and invertible index
-- motion. Those hypotheses remain explicit: the generic LinearAction only
-- exposes an action function, not group multiplication/inverse laws.
record FullMonomialBasisReceipt
    (route : WrongType.CanonicalLinearMultiplicityRoute) : Set₁ where
  field
    monomial : MonomialMultiplicityBasisSpecialisation route
    inverseIndexAct : RouteGroup route → Fin 90 → Fin 90
    inverseAfterIndexAct :
      (g : RouteGroup route) (index : Fin 90) →
      inverseIndexAct g (indexAct monomial g index) ≡ index
    indexActAfterInverse :
      (g : RouteGroup route) (index : Fin 90) →
      indexAct monomial g (inverseIndexAct g index) ≡ index
    scalarZero :
      Linear.Scalar
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))
    nonzeroScalarCoefficient :
      (g : RouteGroup route) (index : Fin 90) →
      scalarAct monomial g index ≢ scalarZero

open FullMonomialBasisReceipt public

indexAfterInverseRoundTrip :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (receipt : FullMonomialBasisReceipt route) →
  (g : RouteGroup route) →
  (index : Fin 90) →
  indexAct (monomial receipt) g (inverseIndexAct receipt g index) ≡ index
indexAfterInverseRoundTrip route receipt =
  indexActAfterInverse receipt

-- A monomial action becomes pure permutation only if its scalars act
-- trivially ON THE CHOSEN BASIS; nonzero scalars alone do not suffice.
record ScalarTrivialOnBasis
    (route : WrongType.CanonicalLinearMultiplicityRoute)
    (receipt : MonomialMultiplicityBasisSpecialisation route) : Set₁ where
  field
    scalarActsTrivially :
      (g : RouteGroup route) (index : Fin 90) →
      Linear._·_
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))
        (scalarAct receipt g index)
        (basisVector receipt (indexAct receipt g index))
      ≡ basisVector receipt (indexAct receipt g index)

open ScalarTrivialOnBasis public

purePermutationFromTrivialScalars :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (receipt : MonomialMultiplicityBasisSpecialisation route) →
  ScalarTrivialOnBasis route receipt →
  WrongType.PermutationBasisSpecialisation
    (WrongType.linearRepresentation route)
purePermutationFromTrivialScalars route receipt trivial =
  record
    { basisVector = basisVector receipt
    ; basisIsComplete = basisComplete receipt
    ; basisIsIndependent = basisIndependent receipt
    ; basisPermutation = indexAct receipt
    ; actionPreservesChosenBasis = λ g i →
        trans
          (actionOnBasisIsMonomial receipt g i)
          (scalarActsTrivially trivial g i)
    }

------------------------------------------------------------------------
-- Typed source-character obstruction: a genuinely NON-permutation source
-- forces some monomial scalar action to be nontrivial on the chosen basis.
--
-- The Suzuki owner supplies the attribution/character calculation; an actual
-- same-linear-route no-go must still inhabit this typed receipt. We do not
-- turn a Bool or cyclotomic String into that proof.
------------------------------------------------------------------------

record SourceExcludesPureBasisPermutation
    (route : WrongType.CanonicalLinearMultiplicityRoute) : Set₁ where
  field
    rejectsPure :
      WrongType.PermutationBasisSpecialisation
        (WrongType.linearRepresentation route) →
      ⊥

open SourceExcludesPureBasisPermutation public

sourceNonPermutationForcesNontrivialMonomialScalars :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (monomial : MonomialMultiplicityBasisSpecialisation route) →
  SourceExcludesPureBasisPermutation route →
  ScalarTrivialOnBasis route monomial →
  ⊥
sourceNonPermutationForcesNontrivialMonomialScalars
  route monomial excluded trivial =
  rejectsPure excluded
    (purePermutationFromTrivialScalars route monomial trivial)

-- Conversely every genuine pure permutation specialization is a monomial
-- specialization if a chosen scalar acts as identity on the basis.
record UnitScalarOnBasis
    (route : WrongType.CanonicalLinearMultiplicityRoute)
    (pure :
      WrongType.PermutationBasisSpecialisation
        (WrongType.linearRepresentation route)) : Set₁ where
  field
    unitScalar :
      Linear.Scalar
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))
    unitActsAsIdentity :
      (index : Fin 90) →
      Linear._·_
        (WrongType.linearCarrier
          (WrongType.linearRepresentation route))
        unitScalar (WrongType.basisVector pure index)
      ≡ WrongType.basisVector pure index

open UnitScalarOnBasis public

monomialFromPurePermutation :
  (route : WrongType.CanonicalLinearMultiplicityRoute) →
  (pure :
    WrongType.PermutationBasisSpecialisation
      (WrongType.linearRepresentation route)) →
  UnitScalarOnBasis route pure →
  MonomialMultiplicityBasisSpecialisation route
monomialFromPurePermutation route pure unit =
  record
    { basisVector = WrongType.basisVector pure
    ; basisComplete = WrongType.basisIsComplete pure
    ; basisIndependent = WrongType.basisIsIndependent pure
    ; indexAct = WrongType.basisPermutation pure
    ; scalarAct = λ g i → unitScalar unit
    ; actionOnBasisIsMonomial = λ g i →
        trans
          (WrongType.actionPreservesChosenBasis pure g i)
          (sym
            (unitActsAsIdentity unit
              (WrongType.basisPermutation pure g i)))
    }

-- The source-paid central character obstructs the pure route but this
-- constructor does not assert an actual MONOMIAL representation exists.
permutationNoGoReceipt :
  NoGo.PermutationCharacterNoGoReceipt
permutationNoGoReceipt =
  NoGo.canonicalPermutationCharacterNoGoReceipt

data CharacterAutomaticallyConstructsMonomialBasis : Set where
data NinetyLabelsAutomaticallyGivePhaseCoefficients : Set where

characterDoesNotConstructMonomialBasis :
  CharacterAutomaticallyConstructsMonomialBasis → ⊥
characterDoesNotConstructMonomialBasis ()

ninetyLabelsDoNotSupplyScalars :
  NinetyLabelsAutomaticallyGivePhaseCoefficients → ⊥
ninetyLabelsDoNotSupplyScalars ()

record Boundary : Set where
  constructor boundary
  field
    canonicalTargetRemainsLinearHomSpace : Bool
    monomialActionTracksScalars : Bool
    inverseIndexRequirementExplicit : Bool
    scalarTrivialityRequiredForPurePermutation : Bool
    sourceNoGoForcesNontrivialScalarAction : Bool
    pureRouteIsNotAutomatic : Bool
    sourceMonomialReceiptInhabited : Bool

canonicalBoundary : Boundary
canonicalBoundary = boundary true true true true true true false
