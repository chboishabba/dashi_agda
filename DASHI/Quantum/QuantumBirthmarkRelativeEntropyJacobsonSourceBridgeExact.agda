{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumBirthmarkRelativeEntropyJacobsonSourceBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- 2026 QFT / RELATIVE-ENTROPY CROSS-POLLINATION
--
-- Philipp Dorau and Albert Much, PRL 136, 091602 (2026),
-- DOI 10.1103/lmq8-nsty.
--
-- Source-level claim shape:
--   * relative (Araki-Uhlmann) entropy between a vacuum reference and coherent
--     scalar-field excitations on a bifurcate Killing horizon is related,
--     using modular theory, to horizon energy flux;
--   * under an entropy/area proportionality assumption, the Jacobson route
--     gives the semiclassical Einstein equations.
--
-- This file records that source boundary and the exact same-object interface
-- it suggests for DASHI.  It does not import the paper as a proof.
------------------------------------------------------------------------

data RelativeEntropyJacobsonSource : Set where
  DorauMuch2026 : RelativeEntropyJacobsonSource

dorauMuch2026Source : Source.AttributedSource
dorauMuch2026Source =
  Source.mkDOISource
    "Philipp Dorau; Albert Much"
    "From Quantum Relative Entropy to the Semiclassical Einstein Equations"
    "Physical Review Letters 136, 091602"
    "2026"
    "10.1103/lmq8-nsty"
    "https://doi.org/10.1103/lmq8-nsty"
    Source.academicArticleSource
    "QFT/modular-theory source boundary for relative entropy, horizon energy flux, area variation, and the semiclassical Jacobson route"
    Source.publicAttribution

------------------------------------------------------------------------
-- Same-object target suggested by the paper.
------------------------------------------------------------------------

record RelativeEntropyHorizonFluxSurface : Set₁ where
  field
    HorizonState : Set
    RelativeEntropyValue : Set
    EnergyFluxValue : Set
    AreaVariationValue : Set

    vacuumReference : HorizonState
    coherentExcitation : HorizonState

    relativeEntropy :
      HorizonState → HorizonState → RelativeEntropyValue
    horizonEnergyFlux :
      HorizonState → HorizonState → EnergyFluxValue
    areaVariation :
      HorizonState → HorizonState → AreaVariationValue

    relativeEntropyEnergyFlux :
      RelativeEntropyValue → EnergyFluxValue → Set

    areaVariationAssumption :
      EnergyFluxValue → AreaVariationValue → Set

    coherentScalarExcitationScope : Bool

open RelativeEntropyHorizonFluxSurface public

------------------------------------------------------------------------
-- Source / promotion firewall.
------------------------------------------------------------------------

record RelativeEntropyJacobsonAuthorityBoundary : Set where
  constructor relativeEntropyJacobsonAuthorityBoundary
  field
    sourceIsPeerReviewedPRL2026 : Bool
    modularRelativeEntropyEnergyFluxClaimRecorded : Bool
    entropyAreaInputIsAssumption : Bool
    coherentScalarExcitationScope : Bool
    localBifurcateKillingHorizonScope : Bool
    relativeEntropyIsNotBirthmarkMemory : Bool
    relativeEntropyIsNotRyuTakayanagiEntropy : Bool
    paperDoesNotEstablishGeneralStateUniversality : Bool
    paperDoesNotEstablishNonperturbativeQuantumGravity : Bool
    sourceCitationDoesNotImportKernelProof : Bool

canonicalRelativeEntropyJacobsonAuthorityBoundary :
  RelativeEntropyJacobsonAuthorityBoundary
canonicalRelativeEntropyJacobsonAuthorityBoundary =
  relativeEntropyJacobsonAuthorityBoundary
    true true true true true true true true true true

relativeEntropyHorizonFluxAuthorityOwned : Bool
relativeEntropyHorizonFluxAuthorityOwned = true

relativeEntropyAreaSameObjectPhysicalReceiptStillRequired : Bool
relativeEntropyAreaSameObjectPhysicalReceiptStillRequired = true

relativeEntropyIsNotBirthmarkMemory : Bool
relativeEntropyIsNotBirthmarkMemory = true

relativeEntropyIsNotRyuTakayanagiEntropy : Bool
relativeEntropyIsNotRyuTakayanagiEntropy = true

paperDoesNotEstablishGeneralStateUniversality : Bool
paperDoesNotEstablishGeneralStateUniversality = true

paperDoesNotEstablishNonperturbativeQuantumGravity : Bool
paperDoesNotEstablishNonperturbativeQuantumGravity = true

status : String
status =
  "DORAU-MUCH-2026-AUTHORITY-RECORDED / RELATIVE-ENTROPY-FLUX-SAME-OBJECT-PHYSICAL-RECEIPT-PENDING"
