module DASHI.Physics.Closure.MassiveSubspaceOSPositivity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.VacuumSectorReceipt as Vacuum

data MassiveSubspaceMatrixStatus : Set where
  p3p5BlockNotPSDWithBareYukawaCoupling : MassiveSubspaceMatrixStatus

massiveSubspaceMatrixStatement : String
massiveSubspaceMatrixStatement =
  "Projected p3/p5 block: [[log(9/8),14/sqrt(24)],[14/sqrt(24),log(5/4)]]. Its determinant is about -8.1407, so it is not PSD."

record MassiveSubspaceOSPositivityReceipt : Setω where
  field
    vacuumSectorReceipt :
      Vacuum.VacuumSectorReceipt

    vacuumSectorSeparatesH0 :
      Vacuum.h0IsQuarkSectorBlock vacuumSectorReceipt ≡ true

    status :
      MassiveSubspaceMatrixStatus

    zeroModeProjected :
      Bool

    zeroModeProjectedIsTrue :
      zeroModeProjected ≡ true

    p3DiagonalNonNegative :
      Bool

    p3DiagonalNonNegativeIsTrue :
      p3DiagonalNonNegative ≡ true

    p5DiagonalNonNegative :
      Bool

    p5DiagonalNonNegativeIsTrue :
      p5DiagonalNonNegative ≡ true

    p3p5DeterminantNonNegative :
      Bool

    p3p5DeterminantNonNegativeIsFalse :
      p3p5DeterminantNonNegative ≡ false

    massiveSubspacePSDWithBareYukawa :
      Bool

    massiveSubspacePSDWithBareYukawaIsFalse :
      massiveSubspacePSDWithBareYukawa ≡ false

    yukawaCouplingsNotHamiltonianEntries :
      Bool

    yukawaCouplingsNotHamiltonianEntriesIsTrue :
      yukawaCouplingsNotHamiltonianEntries ≡ true

    h0OSPositivityRequiresPhysicalMassMatrix :
      Bool

    h0OSPositivityRequiresPhysicalMassMatrixIsTrue :
      h0OSPositivityRequiresPhysicalMassMatrix ≡ true

    physicalMassMatrixRequiresVEV :
      Bool

    physicalMassMatrixRequiresVEVIsTrue :
      physicalMassMatrixRequiresVEV ≡ true

    osPositivityInhabited :
      Bool

    osPositivityInhabitedIsFalse :
      osPositivityInhabited ≡ false

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    matrixStatement :
      String

    matrixStatementIsCanonical :
      matrixStatement ≡ massiveSubspaceMatrixStatement

    receiptBoundary :
      List String

open MassiveSubspaceOSPositivityReceipt public

canonicalMassiveSubspaceOSPositivityReceipt :
  MassiveSubspaceOSPositivityReceipt
canonicalMassiveSubspaceOSPositivityReceipt =
  record
    { vacuumSectorReceipt =
        Vacuum.canonicalVacuumSectorReceipt
    ; vacuumSectorSeparatesH0 =
        refl
    ; status =
        p3p5BlockNotPSDWithBareYukawaCoupling
    ; zeroModeProjected =
        true
    ; zeroModeProjectedIsTrue =
        refl
    ; p3DiagonalNonNegative =
        true
    ; p3DiagonalNonNegativeIsTrue =
        refl
    ; p5DiagonalNonNegative =
        true
    ; p5DiagonalNonNegativeIsTrue =
        refl
    ; p3p5DeterminantNonNegative =
        false
    ; p3p5DeterminantNonNegativeIsFalse =
        refl
    ; massiveSubspacePSDWithBareYukawa =
        false
    ; massiveSubspacePSDWithBareYukawaIsFalse =
        refl
    ; yukawaCouplingsNotHamiltonianEntries =
        true
    ; yukawaCouplingsNotHamiltonianEntriesIsTrue =
        refl
    ; h0OSPositivityRequiresPhysicalMassMatrix =
        true
    ; h0OSPositivityRequiresPhysicalMassMatrixIsTrue =
        refl
    ; physicalMassMatrixRequiresVEV =
        true
    ; physicalMassMatrixRequiresVEVIsTrue =
        refl
    ; osPositivityInhabited =
        false
    ; osPositivityInhabitedIsFalse =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; matrixStatement =
        massiveSubspaceMatrixStatement
    ; matrixStatementIsCanonical =
        refl
    ; receiptBoundary =
        "Projecting the p2 zero mode does not make the bare p3/p5 block PSD"
        ∷ "The obstruction is using bare Yukawa constants as Hamiltonian entries"
        ∷ "The OS base-case route now depends on a physical mass matrix with a VEV calibration"
        ∷ []
    }

massiveSubspaceBareYukawaNotPSD :
  massiveSubspacePSDWithBareYukawa
    canonicalMassiveSubspaceOSPositivityReceipt
  ≡
  false
massiveSubspaceBareYukawaNotPSD =
  refl

