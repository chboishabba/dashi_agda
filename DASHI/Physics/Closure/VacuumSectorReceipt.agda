module DASHI.Physics.Closure.VacuumSectorReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NormalisedH0OSPositivity as H0Norm

data VacuumSectorStatus : Set where
  separateZeroParticleVacuumRequired : VacuumSectorStatus

data VacuumSectorBlocker : Set where
  p2LaneZeroModeMustBeProjectedOrMassLifted : VacuumSectorBlocker
  massiveSubspaceOSCheckRequired : VacuumSectorBlocker
  physicalMassMatrixRequired : VacuumSectorBlocker

canonicalVacuumSectorBlockers : List VacuumSectorBlocker
canonicalVacuumSectorBlockers =
  p2LaneZeroModeMustBeProjectedOrMassLifted
  ∷ massiveSubspaceOSCheckRequired
  ∷ physicalMassMatrixRequired
  ∷ []

vacuumSectorStatement : String
vacuumSectorStatement =
  "The previously checked H0 is a one-particle/quark-sector block, not the full Hamiltonian with a separate zero-particle vacuum sector."

record VacuumSectorReceipt : Setω where
  field
    normalisedH0Receipt :
      H0Norm.NormalisedH0OSPositivityReceipt

    normalisedH0StillOpen :
      H0Norm.h0OSPositiveAfterNormalisation normalisedH0Receipt ≡ false

    status :
      VacuumSectorStatus

    fullHamiltonianHasSeparateVacuumSector :
      Bool

    fullHamiltonianHasSeparateVacuumSectorIsTrue :
      fullHamiltonianHasSeparateVacuumSector ≡ true

    vacuumEnergyZeroByConvention :
      Bool

    vacuumEnergyZeroByConventionIsTrue :
      vacuumEnergyZeroByConvention ≡ true

    h0IsQuarkSectorBlock :
      Bool

    h0IsQuarkSectorBlockIsTrue :
      h0IsQuarkSectorBlock ≡ true

    p2LaneMasslessInChiralLimit :
      Bool

    p2LaneMasslessInChiralLimitIsTrue :
      p2LaneMasslessInChiralLimit ≡ true

    osPositivityOnMassiveSubspaceChecked :
      Bool

    osPositivityOnMassiveSubspaceCheckedIsFalse :
      osPositivityOnMassiveSubspaceChecked ≡ false

    osPositivityInhabited :
      Bool

    osPositivityInhabitedIsFalse :
      osPositivityInhabited ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ vacuumSectorStatement

    blockers :
      List VacuumSectorBlocker

    blockersAreCanonical :
      blockers ≡ canonicalVacuumSectorBlockers

    receiptBoundary :
      List String

open VacuumSectorReceipt public

canonicalVacuumSectorReceipt : VacuumSectorReceipt
canonicalVacuumSectorReceipt =
  record
    { normalisedH0Receipt =
        H0Norm.canonicalNormalisedH0OSPositivityReceipt
    ; normalisedH0StillOpen =
        refl
    ; status =
        separateZeroParticleVacuumRequired
    ; fullHamiltonianHasSeparateVacuumSector =
        true
    ; fullHamiltonianHasSeparateVacuumSectorIsTrue =
        refl
    ; vacuumEnergyZeroByConvention =
        true
    ; vacuumEnergyZeroByConventionIsTrue =
        refl
    ; h0IsQuarkSectorBlock =
        true
    ; h0IsQuarkSectorBlockIsTrue =
        refl
    ; p2LaneMasslessInChiralLimit =
        true
    ; p2LaneMasslessInChiralLimitIsTrue =
        refl
    ; osPositivityOnMassiveSubspaceChecked =
        false
    ; osPositivityOnMassiveSubspaceCheckedIsFalse =
        refl
    ; osPositivityInhabited =
        false
    ; osPositivityInhabitedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; statement =
        vacuumSectorStatement
    ; statementIsCanonical =
        refl
    ; blockers =
        canonicalVacuumSectorBlockers
    ; blockersAreCanonical =
        refl
    ; receiptBoundary =
        "The p2 zero entry is recorded as a massless chiral-limit mode, not as the physical vacuum"
        ∷ "OS positivity must be rechecked after separating the vacuum and projecting or lifting the zero mode"
        ∷ "No unconditional OS positivity, Wightman reconstruction, or Clay Yang-Mills promotion follows"
        ∷ []
    }

vacuumSectorDoesNotPromoteClay :
  clayYangMillsPromoted canonicalVacuumSectorReceipt ≡ false
vacuumSectorDoesNotPromoteClay =
  refl

