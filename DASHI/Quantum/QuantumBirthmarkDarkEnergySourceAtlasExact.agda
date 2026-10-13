{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkDarkEnergySourceAtlasExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE ATLAS: HISTORY-SECTOR DARK-ENERGY CROSS-POLLINATION
--
-- This atlas distinguishes what the cited source actually establishes from the
-- model-level hypotheses introduced by the DASHI synthesis.
------------------------------------------------------------------------

record SourceReceipt : Set where
  constructor source-receipt
  field
    identifier : String
    sourceClaim : String
    supportsHistoryDarkEnergyMechanism : Bool
    supportsDirectEmpiricalConfirmation : Bool

open SourceReceipt public

landauer1961 : SourceReceipt
landauer1961 =
  source-receipt
    "R. Landauer, IBM J. Res. Dev. 5 (1961) 183-191"
    "Logical erasure has a thermodynamic cost; this does not establish a converse gravitational cost for persistent information"
    false false

birthmarkPRX2026 : SourceReceipt
birthmarkPRX2026 =
  source-receipt
    "Graf et al., Phys. Rev. X 16, 031063 (2026), DOI 10.1103/dhzb-28rb"
    "Closed nonstationary quantum systems can retain generic long-time history-sensitive birthmark structure beyond conventional scarring"
    false false

birthmarkRMT2026 : SourceReceipt
birthmarkRMT2026 =
  source-receipt
    "Xiaoya, Graf, Heller, Keski-Rahkonen, arXiv:2602.00891"
    "Universal birthmark/RMT factors and finite-N corrections for the selected symmetry classes"
    false false

jacobson1995 : SourceReceipt
jacobson1995 =
  source-receipt
    "T. Jacobson, Phys. Rev. Lett. 75 (1995) 1260-1263"
    "Einstein equation as an equation of state from local horizon Clausius plus entropy-area and local Rindler assumptions"
    false false

desiDR2LyAlpha2026 : SourceReceipt
desiDR2LyAlpha2026 =
  source-receipt
    "DESI Collaboration, DR2 Ly-alpha full-shape result, 2026-07-30"
    "Latest Ly-alpha full-shape constraints move toward LambdaCDM relative to earlier evolving-dark-energy hints; evolving dark energy is not established"
    false false

euclid2026 : SourceReceipt
euclid2026 =
  source-receipt
    "Euclid Consortium mission/data-release status, 2026"
    "Euclid is actively surveying structure/expansion; first core cosmology results are a discriminator channel, not confirmation of the history-sector model"
    false false

roman2026 : SourceReceipt
roman2026 =
  source-receipt
    "NASA Nancy Grace Roman Space Telescope launch, 2026-08-30"
    "Roman launched and will constrain dark-energy/structure observables after commissioning; launch itself provides no dark-energy mechanism evidence"
    false false

------------------------------------------------------------------------
-- Synthesis boundaries.
------------------------------------------------------------------------

noSourceAboveDirectlyEstablishesHistoryDarkEnergy : Bool
noSourceAboveDirectlyEstablishesHistoryDarkEnergy = true

landauerDoesNotSupplyGravityConverse : Bool
landauerDoesNotSupplyGravityConverse = true

desiDoesNotEstablishEvolvingDarkEnergy : Bool
desiDoesNotEstablishEvolvingDarkEnergy = true

surveySensitivityIsNotMechanismIdentification : Bool
surveySensitivityIsNotMechanismIdentification = true
