module DASHI.Physics.QuantumVacuum.BrownMaclayParallelPlateSourceAuthorityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- BOUNDED SOURCE AUTHORITY FOR THE IDEAL CONDUCTING-PLATE SYSTEM
--
-- Lowell S. Brown and G. Jordan Maclay,
-- "Vacuum Stress between Conducting Plates: An Image Solution",
-- Physical Review 184 (1969), 1272-1279.
-- DOI: 10.1103/PhysRev.184.1272
--
-- The paper treats the electromagnetic vacuum stress between two perfectly
-- conducting parallel plates and computes the finite zero-temperature stress
-- tensor without identifying that source result with DASHI's mode-sum proof.
------------------------------------------------------------------------

record BrownMaclayParallelPlateAuthority : Set where
  field
    sourceName : String
    doi : String
    perfectConductingParallelPlates : Set
    electromagneticVacuumStress : Set
    zeroTemperatureFiniteStress : Set
    virtualWorkPressureEnergyAgreement : Set
    sourceUsesImageGreenFunctionRoute : Set
    sourceDoesNotSupplyDASHIModeCompletenessProof : Set
    sourceBackedOnly : Set
    reading : String

open BrownMaclayParallelPlateAuthority public

brownMaclay1969 : BrownMaclayParallelPlateAuthority
brownMaclay1969 = record
  { sourceName = "Brown and Maclay, Physical Review 184 (1969) 1272-1279"
  ; doi = "10.1103/PhysRev.184.1272"
  ; perfectConductingParallelPlates = ⊤
  ; electromagneticVacuumStress = ⊤
  ; zeroTemperatureFiniteStress = ⊤
  ; virtualWorkPressureEnergyAgreement = ⊤
  ; sourceUsesImageGreenFunctionRoute = ⊤
  ; sourceDoesNotSupplyDASHIModeCompletenessProof = ⊤
  ; sourceBackedOnly = ⊤
  ; reading = "Brown-Maclay source-backs the same ideal conducting-plate physical system and finite vacuum stress, but not DASHI's missing TE/TM mode-completeness derivation."
  }

data BrownMaclayAutomaticallyClosesModePDE : Set where

sourceResultDoesNotAutoCloseModePDE :
  BrownMaclayAutomaticallyClosesModePDE → ⊥
sourceResultDoesNotAutoCloseModePDE ()
