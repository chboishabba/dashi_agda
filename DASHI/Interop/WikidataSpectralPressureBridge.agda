module DASHI.Interop.WikidataSpectralPressureBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.CandidateOnlyCore as CandidateOnly
import DASHI.Interop.PNFResidualSpectralSeverityReceipt as Spectral
import DASHI.Interop.SensibLawResidualLattice as Residual
import DASHI.Interop.WikidataCandidateRoleBridge as Wikidata
import UFTC_Lattice as UFTC

------------------------------------------------------------------------
-- Wikidata candidate pressure as a finite diagonal spectrum.
--
-- This is the precise reusable claim supported by the current carriers:
-- once a *local* PNF assignment has classified a Wikidata candidate into a
-- comparable residual case, that residual has a finite diagonal severity
-- eigenvalue.  It is useful as a domain-specific triage/pressure observable.
--
-- It is deliberately not the claim that Wikidata has a physical Hamiltonian,
-- that every candidate has a canonical spectrum, or that a spectral reading
-- creates semantic, theorem, or external-data authority.

------------------------------------------------------------------------
-- Only the residual cases already comparable in the PNF lattice may be
-- embedded without another local receipt.  In particular, `scopeExceeded`
-- and `unresolved` cannot be silently collapsed to a numerical eigenvalue.

data SpectralizableCandidateResidual :
  Wikidata.CandidateResidual → Set where

  exactResidual :
    SpectralizableCandidateResidual Wikidata.exactCandidateResidual

  partialResidual :
    SpectralizableCandidateResidual Wikidata.partialCandidateResidual

  noTypedMeetResidual :
    SpectralizableCandidateResidual Wikidata.noTypedMeetCandidateResidual

contextualResidualLevel :
  ∀ {r} →
  SpectralizableCandidateResidual r →
  Residual.ResidualLevel
contextualResidualLevel exactResidual =
  Residual.exact
contextualResidualLevel partialResidual =
  Residual.partial
contextualResidualLevel noTypedMeetResidual =
  Residual.noTypedMeet

------------------------------------------------------------------------
-- The operator is diagonal by construction: a residual label is its basis
-- state and `residualSeverity` is its eigenvalue.  This is a finite operator
-- reading, not a self-adjoint analytic Hamiltonian or a continuum theorem.

record FiniteDiagonalPressureOperator : Set where
  constructor finiteDiagonalPressureOperator
  field
    basisResidual :
      Residual.ResidualLevel

    eigenvalue :
      UFTC.Severity

    eigenvalueIsSeverity :
      eigenvalue ≡ Spectral.fourLevelSeveritySpectrum basisResidual

    finiteDiagonalOnly :
      Bool

    finiteDiagonalOnlyIsTrue :
      finiteDiagonalOnly ≡ true

    physicalHamiltonianAuthority :
      Bool

    physicalHamiltonianAuthorityIsFalse :
      physicalHamiltonianAuthority ≡ false

    continuumSpectralAuthority :
      Bool

    continuumSpectralAuthorityIsFalse :
      continuumSpectralAuthority ≡ false

open FiniteDiagonalPressureOperator public

operatorForResidual :
  Residual.ResidualLevel →
  FiniteDiagonalPressureOperator
operatorForResidual residual =
  finiteDiagonalPressureOperator
    residual
    (Spectral.fourLevelSeveritySpectrum residual)
    refl
    true
    refl
    false
    refl
    false
    refl

exactPressureIsZero :
  eigenvalue (operatorForResidual Residual.exact) ≡ 0
exactPressureIsZero =
  refl

partialPressureIsOne :
  eigenvalue (operatorForResidual Residual.partial) ≡ 1
partialPressureIsOne =
  refl

noTypedMeetPressureIsThree :
  eigenvalue (operatorForResidual Residual.noTypedMeet) ≡ 3
noTypedMeetPressureIsThree =
  refl

------------------------------------------------------------------------
-- A spectral pressure witness needs the separate PNF role-in-context
-- assignment.  The Wikidata surface itself supplies only identity and hints.

record WikidataSpectralPressureWitness : Set where
  constructor wikidataSpectralPressureWitness
  field
    localAssignment :
      Wikidata.PNFCandidateAssignment

    residualComparable :
      SpectralizableCandidateResidual
        (Wikidata.pnfResidual localAssignment)

    localReceiptId :
      String

    candidateOnly :
      Wikidata.candidateOnly
        (Wikidata.pnfCandidate localAssignment)
      ≡
      true

open WikidataSpectralPressureWitness public

witnessResidual :
  WikidataSpectralPressureWitness →
  Residual.ResidualLevel
witnessResidual witness =
  contextualResidualLevel (residualComparable witness)

witnessPressureOperator :
  WikidataSpectralPressureWitness →
  FiniteDiagonalPressureOperator
witnessPressureOperator witness =
  operatorForResidual (witnessResidual witness)

witnessPressure :
  WikidataSpectralPressureWitness →
  UFTC.Severity
witnessPressure witness =
  eigenvalue (witnessPressureOperator witness)

------------------------------------------------------------------------
-- The already-proved PNF join law transfers directly: combining two local
-- residual observations takes the maximum finite spectral pressure.

joinWitnessPressure :
  WikidataSpectralPressureWitness →
  WikidataSpectralPressureWitness →
  UFTC.Severity
joinWitnessPressure left right =
  Spectral.fourLevelSeveritySpectrum
    (Residual.joinResidual (witnessResidual left) (witnessResidual right))

joinWitnessPressureIsSpectralMaximum :
  (left right : WikidataSpectralPressureWitness) →
  joinWitnessPressure left right
  ≡
  UFTC._⊔s_ (witnessPressure left) (witnessPressure right)
joinWitnessPressureIsSpectralMaximum left right =
  Spectral.fourLevelJoinIsSpectralMax
    (witnessResidual left)
    (witnessResidual right)

------------------------------------------------------------------------
-- Non-promotion boundary.  These are the claims that make the word
-- “spectral” safe in this setting: it describes a finite, contextual
-- pressure representation and does not upgrade the original Wikidata row.

witnessDoesNotCreateTruthAuthority :
  (witness : WikidataSpectralPressureWitness) →
  CandidateOnly.carriesTruthAuthority
    (Wikidata.wikidataCandidateOnlyCoreAdapter
      (Wikidata.pnfCandidate (localAssignment witness)))
  ≡
  false
witnessDoesNotCreateTruthAuthority witness =
  Wikidata.wikidataCandidateOnlyCoreTruthAuthorityFalse
    (Wikidata.pnfCandidate (localAssignment witness))

witnessDoesNotCreateTheoremAuthority :
  (witness : WikidataSpectralPressureWitness) →
  CandidateOnly.carriesTheoremAuthority
    (Wikidata.wikidataCandidateOnlyCoreAdapter
      (Wikidata.pnfCandidate (localAssignment witness)))
  ≡
  false
witnessDoesNotCreateTheoremAuthority witness =
  Wikidata.wikidataCandidateOnlyCoreTheoremAuthorityFalse
    (Wikidata.pnfCandidate (localAssignment witness))

data WikidataSpectralPressurePromotion : Set where

wikidataSpectralPressurePromotionImpossible :
  WikidataSpectralPressurePromotion →
  ⊥
wikidataSpectralPressurePromotionImpossible ()

spectralPressureStatement :
  String
spectralPressureStatement =
  "A Wikidata candidate may receive a finite diagonal spectral-pressure reading only after a local PNF role/residual receipt places it in an exact, partial, or no-typed-meet case. The eigenvalue is the existing residual severity, and joined local residuals take spectral maximum. This is not a physical Hamiltonian, a continuum spectral theorem, Wikidata truth, or external authority."
