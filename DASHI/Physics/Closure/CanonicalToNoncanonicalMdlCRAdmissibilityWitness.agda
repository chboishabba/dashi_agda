module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRAdmissibilityWitness where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)

open import DASHI.Algebra.Trit using (pos)
open import DASHI.Geometry.ShiftLorentzEmergenceInstance as SLEI
open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Smallest local witness packaging for the active CR-retarget requirement.
--
-- The active continuum lane does not need a new bridge theorem here; it needs
-- the exact admissibility witness demanded by the current requirement surface.

canonicalTransportStateCR-inBasin :
  SRGOI.ShiftCanonicalInBasin (CAMI.canonicalTransportState CI.CR)
canonicalTransportStateCR-inBasin = refl

canonicalTransportStateCR-coneCompatible :
  SRGOI.ShiftConeCompatible (CAMI.canonicalTransportState CI.CR)
canonicalTransportStateCR-coneCompatible =
  SLEI.canonicalShiftExecutionConeWitness

canonicalTransportStateCR-shiftRGAdmissible :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR)
canonicalTransportStateCR-shiftRGAdmissible =
  canonicalTransportStateCR-inBasin
  ,
  canonicalTransportStateCR-coneCompatible
