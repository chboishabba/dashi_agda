module DASHI.Physics.CondensedMatter.CoQuarterTaSeTwoWannierSpectralProducerExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- WANNIER90 MATERIAL-HAMILTONIAN CONSUMER BOUNDARY
--
-- Productive cross-pollination from the existing Hatanaka/Nomoto/Arita
-- DFT -> Wannier-TB route: once a literal same-object CoTa4Se8 SOC+exchange
-- `*_hr.dat` exists, scripts/co_tase2_wannier90_spectral.py consumes its
-- real-space H(R), declared spin projectors and reciprocal lattice and produces
-- the material_spectral.npz schema already required by the ARPES forward fit.
--
-- This closes producer-FORMAT/design debt only.  It does not create the DFT,
-- Wannierisation, pseudopotentials, spin basis or same-object material artifact.
------------------------------------------------------------------------

record WannierSpectralProducerContract : Set where
  constructor wannier-spectral-producer-contract
  field
    literalHrDatRequired : Bool
    realSpaceDegeneraciesConsumed : Bool
    blochFourierInterpolationImplemented : Bool
    hermiticityFailClosed : Bool
    socDeclarationRequired : Bool
    exchangeDeclarationRequired : Bool
    explicitSpinBasisRequired : Bool
    explicitSpinProjectorsRequired : Bool
    reciprocalLatticeRequired : Bool
    fermiEnergyRequired : Bool
    lorentzianBroadeningDeclared : Bool
    provenanceSHA256Produced : Bool
    existingARPESMaterialSchemaProduced : Bool

open WannierSpectralProducerContract public

canonicalWannierSpectralProducerContract : WannierSpectralProducerContract
canonicalWannierSpectralProducerContract =
  wannier-spectral-producer-contract
    true true true true true true true true true true true true true

record WannierProducerStatus : Set where
  constructor wannier-producer-status
  field
    parserImplemented : Bool
    hRToHkImplemented : Bool
    spinProjectedSpectralFunctionImplemented : Bool
    forwardFitSchemaWeldImplemented : Bool
    literalCoTa4Se8HrDatPresent : Bool
    literalProducerMetadataPresent : Bool
    materialSpectralReceiptExecuted : Bool

canonicalWannierProducerStatus : WannierProducerStatus
canonicalWannierProducerStatus =
  wannier-producer-status true true true true false false false

record WannierPromotionBoundary : Set where
  constructor wannier-promotion-boundary
  field
    parserImpliesMaterialCalculation : Bool
    publishedDFTRecipeImpliesHrDat : Bool
    independentSahTightBindingEqualsWannierArtifact : Bool
    syntheticParserSelfTestImpliesMaterialReceipt : Bool
    literalSameObjectElectronicArtifactStillRequired : Bool

canonicalWannierPromotionBoundary : WannierPromotionBoundary
canonicalWannierPromotionBoundary =
  wannier-promotion-boundary false false false false true
