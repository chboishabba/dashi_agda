module DASHI.Physics.Chemistry.AmmoniaProtonationReactionValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaProtonationReactionExact as Protonation

nitrogenConserved :
  Protonation.ProtonationStoichiometry.reactantNitrogen
    Protonation.canonicalProtonationStoichiometry
  ≡ Protonation.ProtonationStoichiometry.productNitrogen
    Protonation.canonicalProtonationStoichiometry
nitrogenConserved = refl

hydrogenConserved :
  Protonation.ProtonationStoichiometry.reactantHydrogen
    Protonation.canonicalProtonationStoichiometry
  ≡ Protonation.ProtonationStoichiometry.productHydrogen
    Protonation.canonicalProtonationStoichiometry
hydrogenConserved = refl

chargeConserved :
  Protonation.ProtonationStoichiometry.reactantNetChargeMagnitude
    Protonation.canonicalProtonationStoichiometry
  ≡ Protonation.ProtonationStoichiometry.productNetChargeMagnitude
    Protonation.canonicalProtonationStoichiometry
chargeConserved = refl

protonAffinityIs8536Tenths :
  Protonation.ProtonationThermochemistry.protonAffinityTenthsKJPerMol
    Protonation.canonicalProtonationThermochemistry
  ≡ 8536
protonAffinityIs8536Tenths = refl

atomAccountingPaid :
  Protonation.ProtonationBoundary.atomInventoryConservationPaid
    Protonation.canonicalProtonationBoundary
  ≡ true
atomAccountingPaid = refl

chargeAccountingPaid :
  Protonation.ProtonationBoundary.chargeAccountingPaid
    Protonation.canonicalProtonationBoundary
  ≡ true
chargeAccountingPaid = refl

lewisElectronBondAccountingPaid :
  Protonation.ProtonationBoundary.lewisElectronAndBondAccountingPaid
    Protonation.canonicalProtonationBoundary
  ≡ true
lewisElectronBondAccountingPaid = refl

thermochemicalPaymentPaid :
  Protonation.ProtonationBoundary.sourceBackedProtonAffinityPaid
    Protonation.canonicalProtonationBoundary
  ≡ true
thermochemicalPaymentPaid = refl

kineticsStillUnpaid :
  Protonation.ProtonationBoundary.sameReactionQuantitativeKineticsPaid
    Protonation.canonicalProtonationBoundary
  ≡ false
kineticsStillUnpaid = refl

notAFirstPrinciplesReactionPath :
  Protonation.ProtonationBoundary.protonAffinityDeterminesMicroscopicReactionPath
    Protonation.canonicalProtonationBoundary
  ≡ false
notAFirstPrinciplesReactionPath = refl
