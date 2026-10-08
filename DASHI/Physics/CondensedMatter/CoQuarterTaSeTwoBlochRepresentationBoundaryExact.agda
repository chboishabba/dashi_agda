module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoBlochRepresentationBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SYMBOLIC BLOCH-REPRESENTATION CONTRACT
--
-- A magnetic Seitz element is represented as {R|t} Theta^epsilon.  The
-- repository Python validator already constructs momentum-dependent sewing
-- matrices with the translation-induced Bloch phase.  This Agda surface states
-- exactly what must hold before that numerical object is promoted to the
-- material's literal magnetic Bloch representation.
------------------------------------------------------------------------

record MagneticSeitzDescriptor : Set where
  constructor magnetic-seitz-descriptor
  field
    rotationLabel : String
    fractionalTranslationLabel : String
    antiunitary : Bool

open MagneticSeitzDescriptor public

record BlochSewingContract : Set where
  constructor bloch-sewing-contract
  field
    momentumActionDefined : Bool
    reciprocalLatticeEquivalenceDefined : Bool
    fractionalTranslationPhaseDefined : Bool
    antiunitaryComplexConjugationDefined : Bool
    sewingMatrixUnitaryOrAntiunitary : Bool
    groupCompositionCocycleChecked : Bool
    HamiltonianCovarianceChecked : Bool
    literalBNSOperationsUsed : Bool

canonicalBlochSewingContract : BlochSewingContract
canonicalBlochSewingContract =
  bloch-sewing-contract
    true true true true true
    false
    true
    false

record MaterialHamiltonianStatus : Set where
  constructor material-hamiltonian-status
  field
    fullTaSeCoOrbitalBasis : Bool
    spinOrbitCouplingIncluded : Bool
    exchangeOrderIncluded : Bool
    parametersFromDFTOrWannier : Bool
    parametersFitToMeasuredBands : Bool
    symmetryCovarianceValidated : Bool
    measuredNodalStructureReproduced : Bool
    measuredOffNodalSplittingReproduced : Bool

canonicalMaterialHamiltonianStatus : MaterialHamiltonianStatus
canonicalMaterialHamiltonianStatus =
  material-hamiltonian-status
    false false true false false true true true

record BlochPromotionBoundary : Set where
  constructor bloch-promotion-boundary
  field
    toyCovarianceImpliesMaterialHamiltonian : Bool
    nodalTheoremImpliesQuantitativeBandAgreement : Bool
    literalBNSAndMaterialParametersStillRequired : Bool

canonicalBlochPromotionBoundary : BlochPromotionBoundary
canonicalBlochPromotionBoundary =
  bloch-promotion-boundary false false true
