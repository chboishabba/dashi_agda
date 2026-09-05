module DASHI.Analysis.NonArchimedeanTwistedRestrictionCoreIntertwinerExact where

------------------------------------------------------------------------
-- CORE INTERTWINER REUSE FOR THE TWISTED RESTRICTION
--
-- Once the source-specific binary-sheet adapter supplies
--
--   D_n (Ext- f) = Ext- (S_n f),
--
-- this is exactly an instance of the repository's project-neutral
-- `Core.Intertwiner`.  No new spectral transport datatype is required.
------------------------------------------------------------------------

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Core
import DASHI.Analysis.NonArchimedeanTwistedRestrictionIntertwinerExact as Restrict

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

coreTwistedRestrictionIntertwiner :
  (data : Restrict.TwistedRestrictionData) →
  Core.Intertwiner
    (Restrict.extendMinus data)
    (Restrict.extendMinus data)
    (Restrict.twistedStep data)
    (Restrict.fullStep data)
coreTwistedRestrictionIntertwiner data =
  Core.intertwiner
    (Restrict.fullStepIntertwinesTwistedRestriction data)

record CoreReuseBoundary : Set where
  constructor coreReuseBoundary
  field
    genericIntertwinerAlreadyOwned : Bool
    twistedRestrictionInstantiatesCoreIntertwiner : Bool
    bespokeSpatialCharacterTransportDatatypeRequired : Bool
    compositionWithExistingCharacterRechartAllowed : Bool

canonicalCoreReuseBoundary : CoreReuseBoundary
canonicalCoreReuseBoundary =
  coreReuseBoundary true true false true

noBespokeTransportKernelRequired :
  CoreReuseBoundary.bespokeSpatialCharacterTransportDatatypeRequired
    canonicalCoreReuseBoundary
  ≡ false
noBespokeTransportKernelRequired = refl
