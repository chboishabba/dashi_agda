module DASHI.Physics.Chemistry.AmmoniaProtonationReactionExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction

------------------------------------------------------------------------
-- Source-backed gas-phase protonation fixture:
--
--   NH3 + H+ -> NH4+
--
-- Attribution boundary:
--   * Hunter & Lias 1998 / NIST pay the evaluated proton affinity 853.6 kJ/mol
--     and the NH3 -> NH4+ protonation identity.
--   * DASHI pays the finite atom/charge/Lewis-bookkeeping reconstruction below.
--   * The proton-affinity datum is thermochemical; it is not a rate constant,
--     transition-state geometry, trajectory, or microscopic reaction path.
------------------------------------------------------------------------

hunterLias1998 : Source.AttributedSource
hunterLias1998 =
  Source.mkDOISource
    "Edward P. L. Hunter; Sharon G. Lias"
    "Evaluated Gas Phase Basicities and Proton Affinities of Molecules: An Update"
    "Journal of Physical and Chemical Reference Data 27(3), 413-656"
    "1998"
    "10.1063/1.556018"
    "https://doi.org/10.1063/1.556018"
    Source.academicArticleSource
    "evaluated gas-phase proton-affinity authority; NH3 is reported with proton affinity 853.6 kJ/mol and protonated product NH4+; does not provide DASHI stoichiometric proofs or kinetics"
    Source.publicAttribution

nistProtonAffinityCarrier : Source.AttributedSource
nistProtonAffinityCarrier =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "CCCBDB list of experimental proton affinities"
    "NIST Computational Chemistry Comparison and Benchmark Database"
    "2026"
    "https://cccbdb.nist.gov/palistx.asp"
    Source.institutionalSource
    "institutional access/compilation carrier exposing the Hunter-Lias evaluated NH3 proton affinity and NH4+ product identity; does not create independent scientific authority"
    Source.publicAttribution

data SpeciesRole : Set where
  ammoniaReactant protonReactant ammoniumProduct : SpeciesRole

record ProtonationStoichiometry : Set where
  constructor protonationStoichiometry
  field
    reactantNitrogen : Nat
    productNitrogen : Nat
    reactantHydrogen : Nat
    productHydrogen : Nat
    reactantNetChargeMagnitude : Nat
    productNetChargeMagnitude : Nat
    reactantValenceElectrons : Nat
    productValenceElectrons : Nat
    reactantNHBonds : Nat
    productNHBonds : Nat
    reactantNitrogenLonePairs : Nat
    productNitrogenLonePairs : Nat

open ProtonationStoichiometry public

canonicalProtonationStoichiometry : ProtonationStoichiometry
canonicalProtonationStoichiometry =
  protonationStoichiometry
    1 1
    4 4
    1 1
    8 8
    3 4
    1 0

nitrogenInventoryConserved :
  reactantNitrogen canonicalProtonationStoichiometry
  ≡ productNitrogen canonicalProtonationStoichiometry
nitrogenInventoryConserved = refl

hydrogenInventoryConserved :
  reactantHydrogen canonicalProtonationStoichiometry
  ≡ productHydrogen canonicalProtonationStoichiometry
hydrogenInventoryConserved = refl

chargeMagnitudeConserved :
  reactantNetChargeMagnitude canonicalProtonationStoichiometry
  ≡ productNetChargeMagnitude canonicalProtonationStoichiometry
chargeMagnitudeConserved = refl

valenceElectronCountConserved :
  reactantValenceElectrons canonicalProtonationStoichiometry
  ≡ productValenceElectrons canonicalProtonationStoichiometry
valenceElectronCountConserved = refl

------------------------------------------------------------------------
-- Lewis-accounting interpretation.
--
-- At this declared bookkeeping level the incoming proton contributes no
-- electron; the NH3 nitrogen lone pair becomes the fourth N-H bond pair.
-- This is not asserted to be a time-resolved electron trajectory.
------------------------------------------------------------------------

record LewisBondChangeReceipt : Set where
  constructor lewisBondChangeReceipt
  field
    sourceNHBonds : Nat
    targetNHBonds : Nat
    sourceNitrogenLonePairs : Nat
    targetNitrogenLonePairs : Nat
    incomingProtonElectrons : Nat
    totalValenceElectronCount : Nat
    donorPairToBondBookkeeping : Bool
    microscopicElectronTrajectoryMeasured : Bool

open LewisBondChangeReceipt public

canonicalLewisBondChangeReceipt : LewisBondChangeReceipt
canonicalLewisBondChangeReceipt =
  lewisBondChangeReceipt
    3 4
    1 0
    0
    8
    true
    false

record ProtonationThermochemistry : Set where
  constructor protonationThermochemistry
  field
    reactionLabel : String
    protonAffinityTenthsKJPerMol : Nat
    valueMeaning : String
    primaryEvaluationSource : Source.AttributedSource
    accessCarrier : Source.AttributedSource
    sameReactionIdentityPaid : Bool
    kineticRateConstantPaid : Bool

open ProtonationThermochemistry public

canonicalProtonationThermochemistry : ProtonationThermochemistry
canonicalProtonationThermochemistry =
  protonationThermochemistry
    "NH3 + H+ -> NH4+"
    8536
    "evaluated gas-phase proton affinity, stored in tenths of kJ/mol"
    hunterLias1998
    nistProtonAffinityCarrier
    true
    false

------------------------------------------------------------------------
-- Admissibility cross-pollination.
--
-- The generic reaction owner remains the authority for enablement vs kinetics.
-- This fixture records a typed semantic target without inventing environmental
-- guards or a rate law from the proton-affinity number.
------------------------------------------------------------------------

record ProtonationAdmissibilitySocket : Set₁ where
  constructor protonationAdmissibilitySocket
  field
    TransitionCarrier : Set
    EnvironmentCarrier : Set
    Enabled : TransitionCarrier → EnvironmentCarrier → Set
    atomInventoryInvariant : Set
    chargeInvariant : Set
    electronBookkeepingInvariant : Set
    bondChangeReference : String
    environmentGuardReference : String
    rateLawReference : String

record ProtonationBoundary : Set where
  constructor protonationBoundary
  field
    atomInventoryConservationPaid : Bool
    atomInventoryConservationPaidIsTrue :
      atomInventoryConservationPaid ≡ true

    chargeAccountingPaid : Bool
    chargeAccountingPaidIsTrue : chargeAccountingPaid ≡ true

    lewisElectronAndBondAccountingPaid : Bool
    lewisElectronAndBondAccountingPaidIsTrue :
      lewisElectronAndBondAccountingPaid ≡ true

    sourceBackedProtonAffinityPaid : Bool
    sourceBackedProtonAffinityPaidIsTrue :
      sourceBackedProtonAffinityPaid ≡ true

    sameReactionQuantitativeKineticsPaid : Bool
    sameReactionQuantitativeKineticsPaidIsFalse :
      sameReactionQuantitativeKineticsPaid ≡ false

    transitionStateGeometryPaid : Bool
    transitionStateGeometryPaidIsFalse : transitionStateGeometryPaid ≡ false

    protonAffinityDeterminesMicroscopicReactionPath : Bool
    protonAffinityDeterminesMicroscopicReactionPathIsFalse :
      protonAffinityDeterminesMicroscopicReactionPath ≡ false

    accessCarrierCreatesIndependentAuthority : Bool
    accessCarrierCreatesIndependentAuthorityIsFalse :
      accessCarrierCreatesIndependentAuthority ≡ false

    thisReactionCreatesMonsterOrGravityClaim : Bool
    thisReactionCreatesMonsterOrGravityClaimIsFalse :
      thisReactionCreatesMonsterOrGravityClaim ≡ false

open ProtonationBoundary public

canonicalProtonationBoundary : ProtonationBoundary
canonicalProtonationBoundary =
  protonationBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

reactionAdmissibilityBoundary : Reaction.ReactionMDLBoundary
reactionAdmissibilityBoundary = Reaction.canonicalReactionMDLBoundary
