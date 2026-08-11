module DASHI.Cognition.PNF.ContextualRepresentationOrbit where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.NumericAuthority
import DASHI.Core.MultiscaleMDL as MDL

------------------------------------------------------------------------
-- Contextual representation orbit.
--
-- The repository already has the application-neutral SymmetryAction and
-- OrbitRelated carrier in MultiscaleMDL.  This module does not create a new
-- group/action implementation.  It adds only PNF provenance/scope around an
-- existing orbit witness so alternative surface/title/pronoun presentations can
-- be compared without being flattened into identity.
------------------------------------------------------------------------

record ContextualOrbitWitness
    {tower : MDL.MultiscaleCarrier}
    (symmetry : MDL.SymmetryAction tower)
    {r : Nat}
    (left right : MDL.Carrier tower r) : Set where
  constructor contextualOrbitWitness
  field
    orbitRelation : MDL.OrbitRelated symmetry left right
    scope : NumericScope
    region : RegionId
    provenance : String

open ContextualOrbitWitness public

------------------------------------------------------------------------
-- Stabilizers are allowed.  A representation may be fixed by a nontrivial
-- supplied symmetry witness; nothing here assumes free action or full orbit
-- cardinality.
------------------------------------------------------------------------

record ContextualStabilizerWitness
    {tower : MDL.MultiscaleCarrier}
    (symmetry : MDL.SymmetryAction tower)
    {r : Nat}
    (point : MDL.Carrier tower r) : Set where
  constructor contextualStabilizerWitness
  field
    stabilizingSymmetry : MDL.Symmetry symmetry r
    stabilizesPoint :
      MDL.act symmetry stabilizingSymmetry point ≡ point
    scope : NumericScope
    region : RegionId

open ContextualStabilizerWitness public

------------------------------------------------------------------------
-- Orbit-related representation is candidate/canonicalisation evidence only.
-- Entity identity still requires the existing proof-relevant identity fibre.
------------------------------------------------------------------------

data OrbitIdentityPromotionPermission : Set where

orbitRelationAloneCannotPromoteIdentity :
  OrbitIdentityPromotionPermission → ⊥
orbitRelationAloneCannotPromoteIdentity ()

record ContextualRepresentationOrbitBoundary : Set where
  constructor contextualRepresentationOrbitBoundary
  field
    orbitCoreIsReused : Set₁
    freeActionAssumed : Set
    orbitRelationPromotesIdentity : OrbitIdentityPromotionPermission → ⊥

open ContextualRepresentationOrbitBoundary public

canonicalContextualRepresentationOrbitBoundary :
  ContextualRepresentationOrbitBoundary
canonicalContextualRepresentationOrbitBoundary =
  contextualRepresentationOrbitBoundary
    MDL.MultiscaleCarrier
    ⊥
    orbitRelationAloneCannotPromoteIdentity
