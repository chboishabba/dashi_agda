module DASHI.Interop.PNFSpectralPhiPsiABICore where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Interop.PNFSpectralNumericABICore as ABI
import DASHI.Interop.PNFSpectralVectorIndex as Vector
import DASHI.Interop.PNFSpectralCoordinateRebuildability as Rebuild

------------------------------------------------------------------------
-- Candidate-only Phi/Psi ABI socket for the PNF spectral numeric ABI.
--
-- Phi carries rebuildable object-row spectral coordinates.
-- Psi carries probe/query/resolver/selector proposal rows over Phi only.
-- Pairing is checked as candidate-only and fail-closed; it does not promote
-- truth, committed support, admissibility, or runtime authority.

data PNFPhiPsiABIStatus : Set where
  checkedCandidateOnlyPhiPsiSocketNoPromotion :
    PNFPhiPsiABIStatus

data PNFPhiPsiABIComponent : Set where
  phiCoordinateTableComponent :
    PNFPhiPsiABIComponent

  psiProbeTableComponent :
    PNFPhiPsiABIComponent

  phiPsiPairingComponent :
    PNFPhiPsiABIComponent

  numericABIBoundaryComponent :
    PNFPhiPsiABIComponent

canonicalPNFPhiPsiABIComponents :
  List PNFPhiPsiABIComponent
canonicalPNFPhiPsiABIComponents =
  phiCoordinateTableComponent
  ∷ psiProbeTableComponent
  ∷ phiPsiPairingComponent
  ∷ numericABIBoundaryComponent
  ∷ []

pnfPhiPsiABIStatement : String
pnfPhiPsiABIStatement =
  "PNF spectral Phi/Psi ABI surfaces are candidate-only. Phi carries rebuildable object-row spectral coordinates, Psi carries probe/query/resolver/selector proposal rows over Phi, and pairing stays fail-closed without promoting truth, support, admissibility, or runtime authority."

pnfPhiPsiABIBoundaryStatement : String
pnfPhiPsiABIBoundaryStatement =
  "This Phi/Psi socket is a checked intake surface only. It binds to the numeric ABI and rebuildability ABI, but it remains candidate-only and does not authorize runtime promotion."

data PNFPhiPsiABIPromotion : Set where

pnfPhiPsiABIPromotionImpossible :
  PNFPhiPsiABIPromotion →
  ⊥
pnfPhiPsiABIPromotionImpossible ()

------------------------------------------------------------------------
-- Phi: rebuildable object-row spectral coordinates.

canonicalPhiRows :
  List Rebuild.SpectralCoordinateMapRow
canonicalPhiRows =
  Rebuild.canonicalSpectralCoordinateMapRow ∷ []

record PhiCoordinateTable : Set where
  constructor mkPhiCoordinateTable
  field
    phiNumericABIReceipt :
      ABI.PNFSpectralNumericABICoreReceipt

    phiNumericABIReceiptIsCanonical :
      phiNumericABIReceipt ≡ ABI.canonicalPNFSpectralNumericABICoreReceipt

    phiRow :
      Rebuild.SpectralCoordinateMapRow

    phiRowIsCanonical :
      phiRow ≡ Rebuild.canonicalSpectralCoordinateMapRow

    phiCoordinate :
      Vector.VectorCoordinate

    phiCoordinateIsRowCoordinate :
      phiCoordinate ≡ Rebuild.mapCoordinate phiRow

    phiRows :
      List Rebuild.SpectralCoordinateMapRow

    phiRowsAreCanonical :
      phiRows ≡ canonicalPhiRows

    phiCandidateOnly :
      Bool

    phiCandidateOnlyIsTrue :
      phiCandidateOnly ≡ true

    phiRebuildable :
      Bool

    phiRebuildableIsTrue :
      phiRebuildable ≡ true

    phiCarriesTruth :
      Bool

    phiCarriesTruthIsFalse :
      phiCarriesTruth ≡ false

    phiCarriesSupport :
      Bool

    phiCarriesSupportIsFalse :
      phiCarriesSupport ≡ false

    phiCarriesAdmissibility :
      Bool

    phiCarriesAdmissibilityIsFalse :
      phiCarriesAdmissibility ≡ false

    phiCarriesRuntimeAuthority :
      Bool

    phiCarriesRuntimeAuthorityIsFalse :
      phiCarriesRuntimeAuthority ≡ false

    phiPromoted :
      Bool

    phiPromotedIsFalse :
      phiPromoted ≡ false

open PhiCoordinateTable public

canonicalPhiCoordinateTable :
  PhiCoordinateTable
canonicalPhiCoordinateTable =
  mkPhiCoordinateTable
    ABI.canonicalPNFSpectralNumericABICoreReceipt
    refl
    Rebuild.canonicalSpectralCoordinateMapRow
    refl
    (Rebuild.mapCoordinate Rebuild.canonicalSpectralCoordinateMapRow)
    refl
    canonicalPhiRows
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

canonicalPhiCoordinateTableIsCanonical :
  phiRow canonicalPhiCoordinateTable ≡ Rebuild.canonicalSpectralCoordinateMapRow
canonicalPhiCoordinateTableIsCanonical =
  refl

------------------------------------------------------------------------
-- Psi: probe/query/resolver/selector proposal rows over Phi.

data PsiProposalKind : Set where
  psiProbeProposal :
    PsiProposalKind

  psiQueryProposal :
    PsiProposalKind

  psiResolverProposal :
    PsiProposalKind

  psiSelectorProposal :
    PsiProposalKind

canonicalPsiProposalKinds :
  List PsiProposalKind
canonicalPsiProposalKinds =
  psiProbeProposal
  ∷ psiQueryProposal
  ∷ psiResolverProposal
  ∷ psiSelectorProposal
  ∷ []

record PsiProbeRow : Set where
  constructor psiProbeRow
  field
    psiProposalKind :
      PsiProposalKind

    psiPhiTable :
      PhiCoordinateTable

    psiProposalCoordinate :
      Vector.VectorCoordinate

    psiProposalCoordinateIsPhiCoordinate :
      psiProposalCoordinate ≡ phiCoordinate psiPhiTable

    psiRowLabel :
      String

    psiCandidateOnly :
      Bool

    psiCandidateOnlyIsTrue :
      psiCandidateOnly ≡ true

    psiProximityOnly :
      Bool

    psiProximityOnlyIsTrue :
      psiProximityOnly ≡ true

    psiCarriesTruth :
      Bool

    psiCarriesTruthIsFalse :
      psiCarriesTruth ≡ false

    psiCarriesSupport :
      Bool

    psiCarriesSupportIsFalse :
      psiCarriesSupport ≡ false

    psiCarriesAdmissibility :
      Bool

    psiCarriesAdmissibilityIsFalse :
      psiCarriesAdmissibility ≡ false

    psiCarriesRuntimeAuthority :
      Bool

    psiCarriesRuntimeAuthorityIsFalse :
      psiCarriesRuntimeAuthority ≡ false

    psiPromoted :
      Bool

    psiPromotedIsFalse :
      psiPromoted ≡ false

open PsiProbeRow public

canonicalPsiProbeRows :
  List PsiProbeRow
canonicalPsiProbeRows =
  psiProbeRow
    psiProbeProposal
    canonicalPhiCoordinateTable
    (phiCoordinate canonicalPhiCoordinateTable)
    refl
    "psi probe proposal over canonical phi"
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
  ∷ psiProbeRow
    psiQueryProposal
    canonicalPhiCoordinateTable
    (phiCoordinate canonicalPhiCoordinateTable)
    refl
    "psi query proposal over canonical phi"
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
  ∷ psiProbeRow
    psiResolverProposal
    canonicalPhiCoordinateTable
    (phiCoordinate canonicalPhiCoordinateTable)
    refl
    "psi resolver proposal over canonical phi"
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
  ∷ psiProbeRow
    psiSelectorProposal
    canonicalPhiCoordinateTable
    (phiCoordinate canonicalPhiCoordinateTable)
    refl
    "psi selector proposal over canonical phi"
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
  ∷ []

record PsiProbeTable : Set where
  constructor mkPsiProbeTable
  field
    psiRows :
      List PsiProbeRow

    psiRowsAreCanonical :
      psiRows ≡ canonicalPsiProbeRows

    psiCandidateOnly :
      Bool

    psiCandidateOnlyIsTrue :
      psiCandidateOnly ≡ true

    psiProximityOnly :
      Bool

    psiProximityOnlyIsTrue :
      psiProximityOnly ≡ true

    psiCarriesTruth :
      Bool

    psiCarriesTruthIsFalse :
      psiCarriesTruth ≡ false

    psiCarriesSupport :
      Bool

    psiCarriesSupportIsFalse :
      psiCarriesSupport ≡ false

    psiCarriesAdmissibility :
      Bool

    psiCarriesAdmissibilityIsFalse :
      psiCarriesAdmissibility ≡ false

    psiCarriesRuntimeAuthority :
      Bool

    psiCarriesRuntimeAuthorityIsFalse :
      psiCarriesRuntimeAuthority ≡ false

    psiPromoted :
      Bool

    psiPromotedIsFalse :
      psiPromoted ≡ false

open PsiProbeTable public

canonicalPsiProbeTable :
  PsiProbeTable
canonicalPsiProbeTable =
  mkPsiProbeTable
    canonicalPsiProbeRows
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Phi/Psi pairing.

record PhiPsiPairing : Set where
  constructor mkPhiPsiPairing
  field
    pairingPhiTable :
      PhiCoordinateTable

    pairingPsiTable :
      PsiProbeTable

    pairingCandidateOnly :
      Bool

    pairingCandidateOnlyIsTrue :
      pairingCandidateOnly ≡ true

    pairingProximityOnly :
      Bool

    pairingProximityOnlyIsTrue :
      pairingProximityOnly ≡ true

    pairingCarriesTruth :
      Bool

    pairingCarriesTruthIsFalse :
      pairingCarriesTruth ≡ false

    pairingCarriesSupport :
      Bool

    pairingCarriesSupportIsFalse :
      pairingCarriesSupport ≡ false

    pairingCarriesAdmissibility :
      Bool

    pairingCarriesAdmissibilityIsFalse :
      pairingCarriesAdmissibility ≡ false

    pairingCarriesRuntimeAuthority :
      Bool

    pairingCarriesRuntimeAuthorityIsFalse :
      pairingCarriesRuntimeAuthority ≡ false

    pairingPromoted :
      Bool

    pairingPromotedIsFalse :
      pairingPromoted ≡ false

open PhiPsiPairing public

canonicalPhiPsiPairing :
  PhiPsiPairing
canonicalPhiPsiPairing =
  mkPhiPsiPairing
    canonicalPhiCoordinateTable
    canonicalPsiProbeTable
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl

------------------------------------------------------------------------
-- Aggregate receipt.

record PNFPhiPsiABICoreReceipt : Set where
  constructor pnfPhiPsiABICoreReceipt
  field
    status :
      PNFPhiPsiABIStatus

    statusIsCandidateOnly :
      status ≡ checkedCandidateOnlyPhiPsiSocketNoPromotion

    components :
      List PNFPhiPsiABIComponent

    componentsAreCanonical :
      components ≡ canonicalPNFPhiPsiABIComponents

    numericABIReceipt :
      ABI.PNFSpectralNumericABICoreReceipt

    numericABIReceiptIsCanonical :
      numericABIReceipt ≡ ABI.canonicalPNFSpectralNumericABICoreReceipt

    phiCoordinateTable :
      PhiCoordinateTable

    phiCoordinateTableIsCanonical :
      phiCoordinateTable ≡ canonicalPhiCoordinateTable

    psiProbeTable :
      PsiProbeTable

    psiProbeTableIsCanonical :
      psiProbeTable ≡ canonicalPsiProbeTable

    phiPsiPairing :
      PhiPsiPairing

    phiPsiPairingIsCanonical :
      phiPsiPairing ≡ canonicalPhiPsiPairing

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    promoted :
      Bool

    promotedIsFalse :
      promoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ pnfPhiPsiABIStatement

    boundaryStatement :
      String

    boundaryStatementIsCanonical :
      boundaryStatement ≡ pnfPhiPsiABIBoundaryStatement

open PNFPhiPsiABICoreReceipt public

canonicalPNFPhiPsiABICoreReceipt :
  PNFPhiPsiABICoreReceipt
canonicalPNFPhiPsiABICoreReceipt =
  pnfPhiPsiABICoreReceipt
    checkedCandidateOnlyPhiPsiSocketNoPromotion
    refl
    canonicalPNFPhiPsiABIComponents
    refl
    ABI.canonicalPNFSpectralNumericABICoreReceipt
    refl
    canonicalPhiCoordinateTable
    refl
    canonicalPsiProbeTable
    refl
    canonicalPhiPsiPairing
    refl
    true
    refl
    false
    refl
    pnfPhiPsiABIStatement
    refl
    pnfPhiPsiABIBoundaryStatement
    refl

canonicalPNFPhiPsiABICoreReceiptStatusIsCandidateOnly :
  status canonicalPNFPhiPsiABICoreReceipt
  ≡
  checkedCandidateOnlyPhiPsiSocketNoPromotion
canonicalPNFPhiPsiABICoreReceiptStatusIsCandidateOnly =
  refl

canonicalPNFPhiPsiABICoreReceiptCandidateOnlyIsTrue :
  candidateOnly canonicalPNFPhiPsiABICoreReceipt ≡ true
canonicalPNFPhiPsiABICoreReceiptCandidateOnlyIsTrue =
  refl

canonicalPNFPhiPsiABICoreReceiptPromotedIsFalse :
  promoted canonicalPNFPhiPsiABICoreReceipt ≡ false
canonicalPNFPhiPsiABICoreReceiptPromotedIsFalse =
  refl
