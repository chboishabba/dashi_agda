module DASHI.Physics.Chemistry.AmmoniaH3PlusProtonTransferExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction

------------------------------------------------------------------------
-- Same-reaction products/byproducts + kinetics fixture:
--
--   H3+ + NH3 -> NH4+ + H2
--
-- Provenance is deliberately split:
--   * Hemsworth--Payzant--Schiff--Bohme 1974 is primary paper authority that
--     the XH+ + NH3 -> NH4+ + X family, explicitly including X=H2, was measured
--     at 297 K by flowing afterglow.
--   * the York University Ion Chemistry Laboratory table is the current numeric
--     compilation carrier for the specific H3+ row: 4.2e-9 cm^3 molecule^-1
--     s^-1, ±20%, 297 K, FA.
--
-- The numeric table is NOT silently promoted to a primary-paper locator, and
-- neither source creates a microscopic transition trajectory or DASHI proof.
------------------------------------------------------------------------

hemsworthPayzantSchiffBohme1974 : Source.AttributedSource
hemsworthPayzantSchiffBohme1974 =
  Source.mkDOISource
    "R. S. Hemsworth; J. D. Payzant; H. I. Schiff; D. K. Bohme"
    "Rate constants at 297 K for proton transfer reactions with NH3. Comparisons with classical theories and exothermicity"
    "Chemical Physics Letters 26(3), 417-421"
    "1974"
    "10.1016/0009-2614(74)89061-5"
    "https://doi.org/10.1016/0009-2614(74)89061-5"
    Source.academicArticleSource
    "primary scientific authority that XH+ + NH3 -> NH4+ + X proton-transfer reactions, explicitly including X=H2, were measured at 297 K by flowing afterglow; this source role does not assign the current York compilation's specific 4.2e-9 row to an unverified paper table locator"
    Source.publicAttribution

yorkIonChemistryNumericTable : Source.AttributedSource
yorkIonChemistryNumericTable =
  Source.mkNoDOISource
    "Ion Chemistry Laboratory, Centre for Research in Mass Spectrometry, York University"
    "Positive Ion Proton-Transfer Reactions table"
    "York University Ion Chemistry Laboratory reaction database"
    "2026"
    "https://www.yorku.ca/dkbohme/research/kdb_Proton_Trans.html"
    Source.institutionalSource
    "institutional numeric compilation carrier for the specific H3+ + NH3 -> NH4+ + H2 row: product distribution 1, k=4.2 x 10^-9 cm^3 molecule^-1 s^-1, ±20%, 297 K, flowing afterglow; not promoted here to independent authorship or a primary-paper locator"
    Source.publicAttribution

record H3AmmoniaStoichiometry : Set where
  constructor h3AmmoniaStoichiometry
  field
    reactantNitrogen : Nat
    productNitrogen : Nat
    reactantHydrogen : Nat
    productHydrogen : Nat
    reactantNetChargeMagnitude : Nat
    productNetChargeMagnitude : Nat
    reactantTotalElectrons : Nat
    productTotalElectrons : Nat

open H3AmmoniaStoichiometry public

-- H3+ has two electrons; NH3 has ten. NH4+ has ten; H2 has two.
canonicalH3AmmoniaStoichiometry : H3AmmoniaStoichiometry
canonicalH3AmmoniaStoichiometry =
  h3AmmoniaStoichiometry 1 1 6 6 1 1 12 12

nitrogenConserved :
  reactantNitrogen canonicalH3AmmoniaStoichiometry
  ≡ productNitrogen canonicalH3AmmoniaStoichiometry
nitrogenConserved = refl

hydrogenConserved :
  reactantHydrogen canonicalH3AmmoniaStoichiometry
  ≡ productHydrogen canonicalH3AmmoniaStoichiometry
hydrogenConserved = refl

chargeMagnitudeConserved :
  reactantNetChargeMagnitude canonicalH3AmmoniaStoichiometry
  ≡ productNetChargeMagnitude canonicalH3AmmoniaStoichiometry
chargeMagnitudeConserved = refl

electronCountConserved :
  reactantTotalElectrons canonicalH3AmmoniaStoichiometry
  ≡ productTotalElectrons canonicalH3AmmoniaStoichiometry
electronCountConserved = refl

record H3AmmoniaKineticReceipt : Set where
  constructor h3AmmoniaKineticReceipt
  field
    reactionLabel : String
    rateMantissaTenths : Nat
    ratePowerOfTen : String
    rateUnits : String
    temperatureKelvin : Nat
    relativeUncertaintyPercent : Nat
    method : String
    productDistribution : Nat
    primaryReactionFamilySource : Source.AttributedSource
    numericCompilationCarrier : Source.AttributedSource

open H3AmmoniaKineticReceipt public

canonicalH3AmmoniaKineticReceipt : H3AmmoniaKineticReceipt
canonicalH3AmmoniaKineticReceipt =
  h3AmmoniaKineticReceipt
    "H3+ + NH3 -> NH4+ + H2"
    42
    "10^-9"
    "cm^3 molecule^-1 s^-1"
    297
    20
    "flowing afterglow"
    1
    hemsworthPayzantSchiffBohme1974
    yorkIonChemistryNumericTable

------------------------------------------------------------------------
-- Reaction bookkeeping at the species/count level.
-- This deliberately does not invent a femtosecond electron trajectory or a
-- transition-state wavefunction from a bimolecular rate coefficient.
------------------------------------------------------------------------

record H3AmmoniaReactionAccounting : Set where
  constructor h3AmmoniaReactionAccounting
  field
    atomInventoryConserved : Bool
    chargeConserved : Bool
    electronCountConserved : Bool
    ammoniaAcceptsProton : Bool
    hydrogenMoleculeIsByproduct : Bool
    productsByproductsResolved : Bool
    kineticRateSameReaction : Bool

canonicalH3AmmoniaReactionAccounting : H3AmmoniaReactionAccounting
canonicalH3AmmoniaReactionAccounting =
  h3AmmoniaReactionAccounting true true true true true true true

record H3AmmoniaBoundary : Set where
  constructor h3AmmoniaBoundary
  field
    productsAndByproductsPaid : Bool
    productsAndByproductsPaidIsTrue : productsAndByproductsPaid ≡ true

    atomChargeElectronAccountingPaid : Bool
    atomChargeElectronAccountingPaidIsTrue :
      atomChargeElectronAccountingPaid ≡ true

    sameReactionQuantitativeKineticsPaid : Bool
    sameReactionQuantitativeKineticsPaidIsTrue :
      sameReactionQuantitativeKineticsPaid ≡ true

    temperatureMethodAndUncertaintyPaid : Bool
    temperatureMethodAndUncertaintyPaidIsTrue :
      temperatureMethodAndUncertaintyPaid ≡ true

    numericLabTablePromotedToPrimaryPaperLocator : Bool
    numericLabTablePromotedToPrimaryPaperLocatorIsFalse :
      numericLabTablePromotedToPrimaryPaperLocator ≡ false

    institutionalTableCreatesIndependentAuthorship : Bool
    institutionalTableCreatesIndependentAuthorshipIsFalse :
      institutionalTableCreatesIndependentAuthorship ≡ false

    microscopicTransitionPathPaid : Bool
    microscopicTransitionPathPaidIsFalse :
      microscopicTransitionPathPaid ≡ false

    transitionStateWavefunctionPaid : Bool
    transitionStateWavefunctionPaidIsFalse :
      transitionStateWavefunctionPaid ≡ false

    rateCoefficientDefinesUniversalEnvironmentIndependentLaw : Bool
    rateCoefficientDefinesUniversalEnvironmentIndependentLawIsFalse :
      rateCoefficientDefinesUniversalEnvironmentIndependentLaw ≡ false

    reactionCreatesMonsterOrGravityClaim : Bool
    reactionCreatesMonsterOrGravityClaimIsFalse :
      reactionCreatesMonsterOrGravityClaim ≡ false

open H3AmmoniaBoundary public

canonicalH3AmmoniaBoundary : H3AmmoniaBoundary
canonicalH3AmmoniaBoundary =
  h3AmmoniaBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

reactionAdmissibilityBoundary : Reaction.ReactionMDLBoundary
reactionAdmissibilityBoundary = Reaction.canonicalReactionMDLBoundary
