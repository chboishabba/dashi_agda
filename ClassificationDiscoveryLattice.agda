module ClassificationDiscoveryLattice where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import Agda.Primitive using (Setω)

import DASHI.Interop.SensibLawResidualLattice as Residual
import Ontology.Hecke.PNFResidualBridge as Hecke

------------------------------------------------------------------------
-- Classification discovery lattice carrier.
--
-- This is a compact typing surface for the local chain:
-- residual witnessing, ITIR/PNF bridging, and Bott-incomplete Clifford
-- scaffolding. It intentionally keeps claims closed and records explicit
-- non-promotion boundaries.

data ClassificationCarrier : Set where
  residualCarrier : ClassificationCarrier
  pnfCarrier : ClassificationCarrier
  heckeCarrier : ClassificationCarrier
  bottCarrier : ClassificationCarrier

canonicalClassificationCarriers : List ClassificationCarrier
canonicalClassificationCarriers =
  residualCarrier
  ∷ pnfCarrier
  ∷ heckeCarrier
  ∷ bottCarrier
  ∷ []

data ClassificationDiscoveryBoundary : Set where
  noYangBaxterPromotion : ClassificationDiscoveryBoundary
  noPhysicsTheoremPromotion : ClassificationDiscoveryBoundary
  noCliffordEquivalencePromotion : ClassificationDiscoveryBoundary
  noNSYMClaimPromotion : ClassificationDiscoveryBoundary

record ClassificationDiscoveryLattice : Setω where
  field
    carriers :
      List ClassificationCarrier

    carriersAreCanonical :
      carriers ≡ canonicalClassificationCarriers

    residualChain :
      List Residual.ResidualLevel

    residualChainIsCanonical :
      residualChain
      ≡
      Residual.exact
      ∷ Residual.partial
      ∷ Residual.noTypedMeet
      ∷ Residual.contradiction
      ∷ []

    pnfBridgeSurface :
      Hecke.HeckePNFResidualBridgeSurface

    pnfBridgeSurfaceIsCanonical :
      pnfBridgeSurface ≡ Hecke.heckePNFResidualBridgeSurface

    pnfConsumptionDiagnosticSummary :
      String

    bottScaffoldSummary :
      String

    discoveryBoundary :
      List ClassificationDiscoveryBoundary

    discoveryBoundaryIsCanonical :
      discoveryBoundary
      ≡
      noYangBaxterPromotion
      ∷ noPhysicsTheoremPromotion
      ∷ noCliffordEquivalencePromotion
      ∷ noNSYMClaimPromotion
      ∷ []

    noPromotionClaim :
      Bool

    noPromotionClaimIsTrue :
      noPromotionClaim ≡ true

    classificationDiscoveryRank :
      Nat

    classificationDiscoveryRankIsFour :
      classificationDiscoveryRank ≡ 4

open ClassificationDiscoveryLattice public

canonicalClassificationDiscoveryLattice :
  ClassificationDiscoveryLattice
canonicalClassificationDiscoveryLattice =
  record
    { carriers =
        canonicalClassificationCarriers
    ; carriersAreCanonical =
        refl
    ; residualChain =
        Residual.exact
        ∷ Residual.partial
        ∷ Residual.noTypedMeet
        ∷ Residual.contradiction
        ∷ []
    ; residualChainIsCanonical =
        refl
    ; pnfBridgeSurface =
        Hecke.heckePNFResidualBridgeSurface
    ; pnfBridgeSurfaceIsCanonical =
        refl
    ; pnfConsumptionDiagnosticSummary =
        "PNF receipt diagnostics remain runtime-bound and boundary-only"
    ; bottScaffoldSummary =
        "Bott incomplete scaffold remains a typed attachment only; no Bott/Clifford promotion is introduced"
    ; discoveryBoundary =
        noYangBaxterPromotion
        ∷ noPhysicsTheoremPromotion
        ∷ noCliffordEquivalencePromotion
        ∷ noNSYMClaimPromotion
        ∷ []
    ; discoveryBoundaryIsCanonical =
        refl
    ; noPromotionClaim =
        true
    ; noPromotionClaimIsTrue =
        refl
    ; classificationDiscoveryRank =
        4
    ; classificationDiscoveryRankIsFour =
        refl
    }
