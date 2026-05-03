module DASHI.Physics.Closure.CanonicalToNoncanonicalMdlGlobalObligationImpossible where

open import Agda.Primitive using (Setω)
open import Data.Empty using (⊥)

open import DASHI.Physics.Closure.CanonicalToNoncanonicalMdlSeamTheorem as Seam
open import DASHI.Physics.Closure.CanonicalToNoncanonicalScheduleMdlAlignmentBlocker as Align
open import DASHI.Physics.Constraints.ConcreteInstance as CI

------------------------------------------------------------------------
-- The continuum/MDL board should not ask for the old global obligation.
-- It is already contradictory on CR, because the global obligation contains
-- schedule-to-noncanonical alignment for every canonical carrier, while the
-- current board has an explicit CR obstruction for that alignment.

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
    rejectedTarget : Setω
    rejectedTargetImpossible : rejectedTarget → ⊥

    correctedTarget : Setω

canonicalToNoncanonicalMdlBoardCorrection :
  CanonicalToNoncanonicalMdlBoardCorrection
canonicalToNoncanonicalMdlBoardCorrection =
  record
    { rejectedTarget = Seam.CanonicalToNoncanonicalMdlSourceScheduleObligation
    ; rejectedTargetImpossible = oldGlobalSourceScheduleObligationImpossible
    ; correctedTarget = Set
    }
