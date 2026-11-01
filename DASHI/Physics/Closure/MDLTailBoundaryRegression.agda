module DASHI.Physics.Closure.MDLTailBoundaryRegression where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.ExecutionAdmissibilityWitness as EAW

------------------------------------------------------------------------
-- Finite regression surface for the currently observed family taxonomy.
--
-- This module records only the theorem shape and the scoped repeated-family
-- observation.  It does not promote a cross-family tail law or identify the
-- underlying collider-data mechanism.

data FamilyId : Set where
  ttbar-mtt-8tev-cms : FamilyId
  z-pt-7tev-atlas : FamilyId
  atlas-4l-m4l-8tev : FamilyId
  atlas-4l-pt4l-8tev : FamilyId

data ConeOK : FamilyId → Set where
  cone-ttbar : ConeOK ttbar-mtt-8tev-cms
  cone-zpt : ConeOK z-pt-7tev-atlas
  cone-atlas-m4l : ConeOK atlas-4l-m4l-8tev
  cone-atlas-pt4l : ConeOK atlas-4l-pt4l-8tev

data FejerOK : FamilyId → Set where
  fejer-ttbar : FejerOK ttbar-mtt-8tev-cms
  fejer-zpt : FejerOK z-pt-7tev-atlas
  fejer-atlas-m4l : FejerOK atlas-4l-m4l-8tev
  fejer-atlas-pt4l : FejerOK atlas-4l-pt4l-8tev

data ClosestOK : FamilyId → Set where
  closest-ttbar : ClosestOK ttbar-mtt-8tev-cms
  closest-zpt : ClosestOK z-pt-7tev-atlas
  closest-atlas-m4l : ClosestOK atlas-4l-m4l-8tev
  closest-atlas-pt4l : ClosestOK atlas-4l-pt4l-8tev

-- Exact MDL succeeds for the checked controls but has no constructor for the
-- ttbar family.  The empty ttbar fibre is consumed below as the negative
-- premise required by MDLTailBoundaryWitness.
data MDLExactOK : FamilyId → Set where
  mdl-zpt : MDLExactOK z-pt-7tev-atlas
  mdl-atlas-m4l : MDLExactOK atlas-4l-m4l-8tev
  mdl-atlas-pt4l : MDLExactOK atlas-4l-pt4l-8tev

data TailLocalized : FamilyId → Set where
  tail-ttbar : TailLocalized ttbar-mtt-8tev-cms
  tail-zpt : TailLocalized z-pt-7tev-atlas

data TerminalBoundary : FamilyId → Set where
  terminal-ttbar : TerminalBoundary ttbar-mtt-8tev-cms
  terminal-zpt : TerminalBoundary z-pt-7tev-atlas

------------------------------------------------------------------------
-- Two compatible-batch observations of the same ttbar family.

ttbar-observation-1 :
  EAW.MDLTailBoundaryWitness
    FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary
ttbar-observation-1 = record
  { family = ttbar-mtt-8tev-cms
  ; coneOK = cone-ttbar
  ; fejerOK = fejer-ttbar
  ; closestOK = closest-ttbar
  ; mdlExactFails = λ ()
  ; tailLocalized = tail-ttbar
  ; terminalBoundary = terminal-ttbar
  }

ttbar-observation-2 :
  EAW.MDLTailBoundaryWitness
    FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary
ttbar-observation-2 = record
  { family = ttbar-mtt-8tev-cms
  ; coneOK = cone-ttbar
  ; fejerOK = fejer-ttbar
  ; closestOK = closest-ttbar
  ; mdlExactFails = λ ()
  ; tailLocalized = tail-ttbar
  ; terminalBoundary = terminal-ttbar
  }

repeated-ttbar-witness :
  EAW.RepeatedMDLTailBoundaryWitness
    FamilyId ConeOK FejerOK ClosestOK MDLExactOK TailLocalized TerminalBoundary
repeated-ttbar-witness = record
  { first = ttbar-observation-1
  ; second = ttbar-observation-2
  ; sameFamily = refl
  }

------------------------------------------------------------------------
-- Regression claims.

repeated-ttbar-is-one-family-evidence :
  EAW.repeatedMDLTailBoundary-scope repeated-ttbar-witness ≡
  EAW.RepeatedOneFamily
repeated-ttbar-is-one-family-evidence = refl

ttbar-family-class-is-MDL-tail-boundary :
  EAW.mdlTailBoundary-familyClass ttbar-observation-1 ≡
  EAW.MDLTailBoundaryFamily
ttbar-family-class-is-MDL-tail-boundary = refl

ttbar-geometric-core :
  EAW.GeometricAdmissibility ConeOK FejerOK ClosestOK ttbar-mtt-8tev-cms
ttbar-geometric-core = EAW.mdlTailBoundary-geometric ttbar-observation-1

ttbar-not-exact-MDL : MDLExactOK ttbar-mtt-8tev-cms → ⊥
ttbar-not-exact-MDL = EAW.mdlTailBoundary-not-exact-MDL ttbar-observation-1
