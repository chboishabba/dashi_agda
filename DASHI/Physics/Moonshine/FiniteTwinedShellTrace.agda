module DASHI.Physics.Moonshine.FiniteTwinedShellTrace where

open import Agda.Builtin.Nat using (Nat)
open import Data.Maybe using (Maybe)

open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as FGSS
open import DASHI.Physics.Moonshine.FiniteShellAction as FSA

record FiniteTwinedShellTrace : Set where
  field
    orientationCoeff : Nat
    grade1FixedCount : Nat
    grade2FixedCount : Nat

identityTwinedTrace : Maybe Nat → Nat → Nat → FiniteTwinedShellTrace
identityTwinedTrace orientation shell1Count shell2Count =
  record
    { orientationCoeff = FGSS.orientationCount orientation
    ; grade1FixedCount = shell1Count
    ; grade2FixedCount = shell2Count
    }

twinedTraceFromAction :
  ∀ {A G : Set} →
  FSA.FiniteShellAction A G →
  Maybe Nat →
  G →
  FiniteTwinedShellTrace
twinedTraceFromAction shellAction orientation g =
  record
    { orientationCoeff = FGSS.orientationCount orientation
    ; grade1FixedCount =
        FSA.countFixedOn shellAction g
          (FSA.FiniteShellAction.shell1States shellAction)
    ; grade2FixedCount =
        FSA.countFixedOn shellAction g
          (FSA.FiniteShellAction.shell2States shellAction)
    }
