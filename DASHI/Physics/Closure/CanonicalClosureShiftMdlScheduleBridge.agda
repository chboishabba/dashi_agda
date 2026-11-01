module DASHI.Physics.Closure.CanonicalClosureShiftMdlScheduleBridge where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalAbstractGaugeMatterInstance as CAMI
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as C2NMST
open import DASHI.Physics.Closure.ShiftRGObservableInstance as SRGOI
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- Canonical-side MDL bridge into the transported schedule surface.
--
-- This file stays sibling-scoped: it attacks only the source-side MDL
-- obligation already isolated by `CanonicalToNoncanonicalMdlSeamTheorem`.
-- The honest outcome is mixed:
-- - `CR` bridges directly.
-- - `CP` and `CC` are explicitly obstructed.

sourceCanonicalToScheduleMdl-CR :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CR) →
  C2NMST.transportedScheduleMdl CI.CR
sourceCanonicalToScheduleMdl-CR _ = refl

sourceCanonicalToScheduleMdl-CP-obstructed :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CP) →
  C2NMST.transportedScheduleMdl CI.CP →
  ⊥
sourceCanonicalToScheduleMdl-CP-obstructed _ ()

sourceCanonicalToScheduleMdl-CC-obstructed :
  SRGOI.shiftRGAdmissible (CAMI.canonicalTransportState CI.CC) →
  C2NMST.transportedScheduleMdl CI.CC →
  ⊥
sourceCanonicalToScheduleMdl-CC-obstructed _ ()
