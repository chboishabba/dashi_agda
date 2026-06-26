module DASHI.Core.FibreRestrictionCore where

open import Agda.Builtin.Bool using (Bool)

------------------------------------------------------------------------
-- Generic fibre-restriction core.
--
-- Evidence can narrow a projected fibre without recovering the hidden
-- carrier. This is the DASHI boundary:
--
--   evidence restricts fibre
--   /=
--   evidence recovers carrier
--   /=
--   evidence promotes truth
------------------------------------------------------------------------

record FibreRestrictionCore : Set₁ where
  constructor fibreRestrictionCore
  field
    Carrier                : Set
    Surface                : Set
    Evidence               : Set
    project                : Carrier → Surface
    Fibre                  : Surface → Set
    restrictsFibre         : Evidence → Surface → Set
    doesNotRecoverCarrier  : Bool
    promotesTruth          : Bool

open FibreRestrictionCore public

ProjectionLossWitness :
  (core : FibreRestrictionCore) →
  Surface core → Set
ProjectionLossWitness core surface =
  Fibre core surface
