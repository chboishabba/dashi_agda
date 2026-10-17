module DASHI.Biology.NonginNangNitrogenOxideRefinementExact where

open import DASHI.Core.Prelude

import DASHI.Core.NonginOnePointOneArmyRefinementExact as Nongin
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Base
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide
import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- NONGIN / NANG / NITROGEN-OXIDE CROSS-POLLINATION
--
-- User genealogy supplies the naming association `nong = nang = nitrous
-- oxide`.  Scientifically, the productive formal connection is the existing
-- Nongin coarse/fine theorem: a coarse "nitrogen oxide" presentation can hide
-- the chemically decisive NO versus N2O coordinate.  A consumer that depends
-- on that coordinate cannot descend through the coarse presentation.
------------------------------------------------------------------------

data CoarseNitrogenOxide : Set where
  nitrogenOxide : CoarseNitrogenOxide

data ChemicalSpeciesFrame : Set where
  nitricOxideFrame : ChemicalSpeciesFrame
  nitrousOxideFrame : ChemicalSpeciesFrame

nitricFrameNotNitrousFrame : nitricOxideFrame ≡ nitrousOxideFrame → ⊥
nitricFrameNotNitrousFrame ()

chemicalSpeciesFrameWitness : Nongin.NontrivialFrame ChemicalSpeciesFrame
chemicalSpeciesFrameWitness =
  Nongin.nontrivial-frame
    nitricOxideFrame
    nitrousOxideFrame
    nitricFrameNotNitrousFrame

NitrogenOxideFineCarrier : Set
NitrogenOxideFineCarrier =
  Nongin.OnePointOneCarrier CoarseNitrogenOxide ChemicalSpeciesFrame

frameToSpecies : ChemicalSpeciesFrame → Oxide.NitrogenOxideSpecies
frameToSpecies nitricOxideFrame = Oxide.nitricOxide
frameToSpecies nitrousOxideFrame = Oxide.nitrousOxide

data ChemicalConsumerOutput : Set where
  nosNitricOxideLane : ChemicalConsumerOutput
  nangNitrousOxideLane : ChemicalConsumerOutput

chemicalSpeciesConsumer : NitrogenOxideFineCarrier → ChemicalConsumerOutput
chemicalSpeciesConsumer (nitrogenOxide , nitricOxideFrame) = nosNitricOxideLane
chemicalSpeciesConsumer (nitrogenOxide , nitrousOxideFrame) = nangNitrousOxideLane

chemicalConsumerSeparatesFrames :
  chemicalSpeciesConsumer (nitrogenOxide , nitricOxideFrame)
  ≡ chemicalSpeciesConsumer (nitrogenOxide , nitrousOxideFrame)
  → ⊥
chemicalConsumerSeparatesFrames ()

chemicalFrameSensitiveConsumer :
  Nongin.FrameSensitiveConsumer chemicalSpeciesConsumer
chemicalFrameSensitiveConsumer =
  Nongin.frame-sensitive-consumer
    nitrogenOxide
    chemicalSpeciesFrameWitness
    chemicalConsumerSeparatesFrames

CoarseChemicalDescent : Set
CoarseChemicalDescent =
  Base.ConsumerDescent
    (Nongin.onePointZeroProject {CoarseNitrogenOxide} {ChemicalSpeciesFrame})
    chemicalSpeciesConsumer

coarseNitrogenOxideCannotServeFineConsumer : CoarseChemicalDescent → ⊥
coarseNitrogenOxideCannotServeFineConsumer =
  Nongin.onePointZeroCannotServeEveryFrameSensitiveConsumer
    chemicalFrameSensitiveConsumer

------------------------------------------------------------------------
-- Genealogy and semantic authority remain separate from chemistry.
------------------------------------------------------------------------

record NongNangGenealogyBoundary : Set where
  constructor nong-nang-genealogy-boundary
  field
    userGenealogyRecordsNongEqualsNang : Bool
    userGenealogyRecordsNongEqualsNangIsTrue :
      userGenealogyRecordsNongEqualsNang ≡ true
    nangLabelRefersToNitrousOxide : Bool
    nangLabelRefersToNitrousOxideIsTrue :
      nangLabelRefersToNitrousOxide ≡ true
    nongNangAliasIdentifiesNitricOxide : Bool
    nongNangAliasIdentifiesNitricOxideIsFalse :
      nongNangAliasIdentifiesNitricOxide ≡ false
    lexicalAliasCreatesBiochemicalMechanism : Bool
    lexicalAliasCreatesBiochemicalMechanismIsFalse :
      lexicalAliasCreatesBiochemicalMechanism ≡ false
    coarseNitrogenOxideIsSufficientForBH4NOSConsumer : Bool
    coarseNitrogenOxideIsSufficientForBH4NOSConsumerIsFalse :
      coarseNitrogenOxideIsSufficientForBH4NOSConsumer ≡ false

canonicalNongNangGenealogyBoundary : NongNangGenealogyBoundary
canonicalNongNangGenealogyBoundary =
  nong-nang-genealogy-boundary true refl true refl false refl false refl false refl

canonicalNonginNangNitrogenOxideReceipt : Receipt.GenericReceipt
canonicalNonginNangNitrogenOxideReceipt =
  Receipt.mkNonPromotingReceipt
    "Nongin / nang nitrogen-oxide refinement"
    "DASHI.Biology.NonginNangNitrogenOxideRefinementExact"
    "coarse nitrogenOxide -> fine {NO,N2O} chemical frame"
    "instantiates the existing Nongin 1.0/1.1 strict-refinement theorem so a frame-sensitive biochemical consumer cannot descend through a coarse nitrogen-oxide label"
    "user genealogy may retain nong=nang=N2O naming, but lexical genealogy does not identify N2O with NO or create a biochemical mechanism"
    "agda -i . DASHI/Biology/NonginNangNitrogenOxideRefinementExact.agda"
