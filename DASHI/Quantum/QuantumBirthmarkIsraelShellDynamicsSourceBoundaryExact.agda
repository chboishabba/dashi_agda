{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkIsraelShellDynamicsSourceBoundaryExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

record ThinShellSourceReceipt : Set where
  constructor thin-shell-source-receipt
  field
    identifier : String
    sourceClaim : String
    authorityForJunctionDynamics : Bool
    authorityForBirthmarkSelection : Bool

open ThinShellSourceReceipt public

israel1966 : ThinShellSourceReceipt
israel1966 =
  thin-shell-source-receipt
    "W. Israel, Il Nuovo Cimento B 44 (1966) 1-14, DOI 10.1007/BF02710419"
    "General-relativistic junction formalism for singular hypersurfaces/thin shells, including spherical-shell dynamics"
    true false

israel1967Erratum : ThinShellSourceReceipt
israel1967Erratum =
  thin-shell-source-receipt
    "W. Israel, Il Nuovo Cimento B 48 (1967) 463, DOI 10.1007/BF02712210"
    "Erratum to the 1966 thin-shell paper"
    true false

israelThinShellDynamicsAuthorityPinned : Bool
israelThinShellDynamicsAuthorityPinned = true

israelDoesNotSupplyBirthmarkHistoryMechanism : Bool
israelDoesNotSupplyBirthmarkHistoryMechanism = true

selectedFixtureAlgebraOwnedElsewhere : Bool
selectedFixtureAlgebraOwnedElsewhere = true
