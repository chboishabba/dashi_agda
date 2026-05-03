module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlGlobalObligationImpossible where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlCRRetargetRequirement as CRRetarget
open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as Align
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- The continuum/MDL board must not ask for the old global obligation.
--
-- That target includes schedule-to-noncanonical alignment for every canonical
-- carrier, but the current board has an explicit CR obstruction for exactly
-- that alignment.

oldGlobalSourceScheduleObligationImpossible :
  Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation →
  ⊥
oldGlobalSourceScheduleObligationImpossible src =
  Align.transportedScheduleMdlToNoncanonicalContinuum-CR-obstructed
    (Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation.transportedScheduleMdlToNoncanonicalContinuum
      src
      CI.CR)

record CanonicalToNoncanonicalMdlBoardCorrection : Setω where
  field
    rejectedGlobalTargetImpossible :
      Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation →
      ⊥

    correctedCRTarget :
      CRRetarget.CanonicalToNoncanonicalMdlCRRetargetTheorem

canonicalToNoncanonicalMdlBoardCorrection :
  CanonicalToNoncanonicalMdlBoardCorrection
canonicalToNoncanonicalMdlBoardCorrection =
  record
    { rejectedGlobalTargetImpossible =
        oldGlobalSourceScheduleObligationImpossible
    ; correctedCRTarget =
        CRRetarget.canonicalCRTransportedScheduleRetargetTheorem
    }
