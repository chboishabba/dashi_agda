module DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferExact as Transfer

reactantHydrogenCountIsSix :
  Transfer.H3AmmoniaStoichiometry.reactantHydrogen
    Transfer.canonicalH3AmmoniaStoichiometry
  ≡ 6
reactantHydrogenCountIsSix = refl

productHydrogenCountIsSix :
  Transfer.H3AmmoniaStoichiometry.productHydrogen
    Transfer.canonicalH3AmmoniaStoichiometry
  ≡ 6
productHydrogenCountIsSix = refl

chargeMagnitudeConserved :
  Transfer.H3AmmoniaStoichiometry.reactantNetChargeMagnitude
    Transfer.canonicalH3AmmoniaStoichiometry
  ≡ Transfer.H3AmmoniaStoichiometry.productNetChargeMagnitude
    Transfer.canonicalH3AmmoniaStoichiometry
chargeMagnitudeConserved = refl

rateMantissaTenthsIs42 :
  Transfer.H3AmmoniaKineticReceipt.rateMantissaTenths
    Transfer.canonicalH3AmmoniaKineticReceipt
  ≡ 42
rateMantissaTenthsIs42 = refl

temperatureIs297K :
  Transfer.H3AmmoniaKineticReceipt.temperatureKelvin
    Transfer.canonicalH3AmmoniaKineticReceipt
  ≡ 297
temperatureIs297K = refl

relativeUncertaintyPercentIs20 :
  Transfer.H3AmmoniaKineticReceipt.relativeUncertaintyPercent
    Transfer.canonicalH3AmmoniaKineticReceipt
  ≡ 20
relativeUncertaintyPercentIs20 = refl

productsByproductsPaid :
  Transfer.H3AmmoniaBoundary.productsAndByproductsPaid
    Transfer.canonicalH3AmmoniaBoundary
  ≡ true
productsByproductsPaid = refl

sameReactionKineticsPaid :
  Transfer.H3AmmoniaBoundary.sameReactionQuantitativeKineticsPaid
    Transfer.canonicalH3AmmoniaBoundary
  ≡ true
sameReactionKineticsPaid = refl

numericCarrierIsNotPrimaryPaperLocator :
  Transfer.H3AmmoniaBoundary.numericLabTablePromotedToPrimaryPaperLocator
    Transfer.canonicalH3AmmoniaBoundary
  ≡ false
numericCarrierIsNotPrimaryPaperLocator = refl

microscopicPathStillUnpaid :
  Transfer.H3AmmoniaBoundary.microscopicTransitionPathPaid
    Transfer.canonicalH3AmmoniaBoundary
  ≡ false
microscopicPathStillUnpaid = refl
