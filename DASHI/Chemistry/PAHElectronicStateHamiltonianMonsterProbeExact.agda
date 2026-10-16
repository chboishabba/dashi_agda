module DASHI.Chemistry.PAHElectronicStateHamiltonianMonsterProbeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Chemistry.LineageAcquiredPrimaryEvidenceExact as Evidence
import DASHI.Chemistry.PAHMechanismStatePromotionExact as PAH

------------------------------------------------------------------------
-- PAH ELECTRONIC-STATE / HAMILTONIAN / MONSTER PROMOTION PROBE
--
-- This deliberately mirrors the successful NH3 escalation, but does not copy
-- its conclusions.  We construct a literal finite catalytic-state carrier and
-- ask what the PAH sources actually pay.  They pay source-bounded structural
-- Fe(II) states, a source-bounded high-spin Fe(IV) catalytic intermediate in a
-- bacterial PheH experiment, and kinetic transitions.  They do not currently
-- pay a numerical human-PAH electronic Hamiltonian, wavefunction coefficients,
-- or a same-object C3 coordinate from which a Monster-3B action could follow.
------------------------------------------------------------------------

panayEtAl2011Ferryl : Source.AttributedSource
panayEtAl2011Ferryl =
  Source.mkDOISource
    "Aram Joel Panay; Michael Lee; Carsten Krebs; J. Martin Bollinger Jr.; Paul F. Fitzpatrick"
    "Evidence for a High-Spin Fe(IV) Species in the Catalytic Cycle of a Bacterial Phenylalanine Hydroxylase"
    "Biochemistry 50(11):1928-1933"
    "2011"
    "10.1021/bi1019868"
    "https://pmc.ncbi.nlm.nih.gov/articles/PMC3059337/"
    Source.academicArticleSource
    "Primary rapid-freeze-quench/Mossbauer study of Chromobacterium violaceum PheH. Pays a kinetically competent high-spin Fe(IV) intermediate and source-conditioned rate constants; it does not establish that the identical numerical electronic state occurs in full-length human PAH or provide a released Hamiltonian/eigenvector."
    Source.publicAttribution

data PAHCatalyticElectronicState : Set where
  humanFeIIBH4StructuralState : PAHCatalyticElectronicState
  bacterialFeIISubstrateCofactorState : PAHCatalyticElectronicState
  bacterialHighSpinFeIVHydroxylatingState : PAHCatalyticElectronicState
  postHydroxylationProductReleaseState : PAHCatalyticElectronicState

record PAHElectronicStateReceipt : Set where
  constructor pahElectronicStateReceipt
  field
    state : PAHCatalyticElectronicState
    systemScope : String
    oxidationSpinReference : String
    evidenceReference : String
    kineticReference : String
    sameObjectHumanState : Bool
    sourceBacked : Bool
    sourceBackedIsTrue : sourceBacked ≡ true

open PAHElectronicStateReceipt public

humanFeIIBH4Receipt : PAHElectronicStateReceipt
humanFeIIBH4Receipt =
  pahElectronicStateReceipt
    humanFeIIBH4StructuralState
    "human PAH catalytic domain / full-length hPAH structural carriers"
    "Fe(II):BH4 structural state; no source-paid spin eigenvector in this receipt"
    "Andersen/Flatmark/Hough 2001 + PDB 1J8U; Flydal et al. 2019 + PDB 6HYC"
    "structural/precatalytic state only"
    true
    true refl

bacterialFerrylReceipt : PAHElectronicStateReceipt
bacterialFerrylReceipt =
  pahElectronicStateReceipt
    bacterialHighSpinFeIVHydroxylatingState
    "Chromobacterium violaceum phenylalanine hydroxylase"
    "high-spin Fe(IV), assigned as Fe(IV)=O by spectroscopic/kinetic comparison"
    "Panay et al. 2011 DOI 10.1021/bi1019868; rapid-freeze-quench 57Fe Mossbauer"
    "Fe(IV) formation 19 mM^-1 s^-1; hydroxylation 42 s^-1; product release 6 s^-1 at 5 C in the reported model"
    false
    true refl

record FiniteCatalyticHamiltonianProbe : Set₁ where
  constructor finiteCatalyticHamiltonianProbe
  field
    Basis : Set
    MatrixElement : Set
    matrixElement : Basis → Basis → MatrixElement
    basisInterpretation : String
    operatorInterpretation : String
    sourceBackedStateCarrierPaid : Bool
    sourceBackedStateCarrierPaidIsTrue : sourceBackedStateCarrierPaid ≡ true
    sourceBackedNumericalHamiltonianMatrixPaid : Bool
    sourceBackedNumericalHamiltonianMatrixPaidIsFalse :
      sourceBackedNumericalHamiltonianMatrixPaid ≡ false
    numericalDiagonalizationPaid : Bool
    numericalDiagonalizationPaidIsFalse : numericalDiagonalizationPaid ≡ false
    eigenvectorCoefficientsPaid : Bool
    eigenvectorCoefficientsPaidIsFalse : eigenvectorCoefficientsPaid ≡ false

open FiniteCatalyticHamiltonianProbe public

canonicalPAHFiniteHamiltonianProbe : FiniteCatalyticHamiltonianProbe
canonicalPAHFiniteHamiltonianProbe =
  finiteCatalyticHamiltonianProbe
    PAHCatalyticElectronicState
    String
    (λ _ _ → "unpaid numerical Hamiltonian matrix element")
    "finite catalytic electronic/mechanistic state basis assembled from source-backed PAH states"
    "literal operator type used to expose the remaining payment: matrix elements are not manufactured from structures, kinetics or QM/MM prose"
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- MONSTER / C3 PROMOTION ATTEMPT
--
-- Full-length hPAH:BH4 PDB 6HYC is an author-defined homotetramer with D2
-- global assembly symmetry.  That does not provide the same-object C3 phase
-- coordinate that made the NH3 <-> Monster-3B probe meaningful.
------------------------------------------------------------------------

record PAHMonster3BProbe : Set where
  constructor pahMonster3BProbe
  field
    physicalObjectReference : String
    observedAssemblySymmetry : String
    sameObjectC3CoordinatePaid : Bool
    sameObjectC3CoordinatePaidIsFalse : sameObjectC3CoordinatePaid ≡ false
    canonicalD2ToMonsterC3IntertwinerPaid : Bool
    canonicalD2ToMonsterC3IntertwinerPaidIsFalse :
      canonicalD2ToMonsterC3IntertwinerPaid ≡ false
    nontrivialMonsterActionOnPAHStatePaid : Bool
    nontrivialMonsterActionOnPAHStatePaidIsFalse :
      nontrivialMonsterActionOnPAHStatePaid ≡ false
    trivialGroupActionMathematicallyAvailable : Bool
    trivialGroupActionMathematicallyAvailableIsTrue :
      trivialGroupActionMathematicallyAvailable ≡ true
    trivialActionCountsAsPhysicalMonsterEvidence : Bool
    trivialActionCountsAsPhysicalMonsterEvidenceIsFalse :
      trivialActionCountsAsPhysicalMonsterEvidence ≡ false
    blocker : String

open PAHMonster3BProbe public

canonicalPAHMonster3BProbe : PAHMonster3BProbe
canonicalPAHMonster3BProbe =
  pahMonster3BProbe
    "full-length human PAH:BH4 structural artifact PDB 6HYC"
    "author-assigned biological assembly: homotetramer with D2 global symmetry"
    false refl
    false refl
    false refl
    true refl
    false refl
    "no source-paid same-object C3 phase coordinate or physical PAH-to-Monster representation map; importing a C3 solely from the wider 369/Monster programme would be analogy, not an intertwiner"

record PAHElectronicMonsterBoundary : Set where
  constructor pahElectronicMonsterBoundary
  field
    literalCatalyticStateCarrierPaid : Bool
    literalCatalyticStateCarrierPaidIsTrue : literalCatalyticStateCarrierPaid ≡ true
    sourceBackedHighSpinFeIVStatePaid : Bool
    sourceBackedHighSpinFeIVStatePaidIsTrue : sourceBackedHighSpinFeIVStatePaid ≡ true
    bacterialFeIVAutomaticallyEqualsHumanFeIVSameObject : Bool
    bacterialFeIVAutomaticallyEqualsHumanFeIVSameObjectIsFalse :
      bacterialFeIVAutomaticallyEqualsHumanFeIVSameObject ≡ false
    literalElectronicHamiltonianPaid : Bool
    literalElectronicHamiltonianPaidIsFalse : literalElectronicHamiltonianPaid ≡ false
    literalElectronicWavefunctionPaid : Bool
    literalElectronicWavefunctionPaidIsFalse : literalElectronicWavefunctionPaid ≡ false
    nontrivialMonsterActionPaid : Bool
    nontrivialMonsterActionPaidIsFalse : nontrivialMonsterActionPaid ≡ false
    microscopicPromotionPaysBH4AllocationFlux : Bool
    microscopicPromotionPaysBH4AllocationFluxIsFalse :
      microscopicPromotionPaysBH4AllocationFlux ≡ false

open PAHElectronicMonsterBoundary public

canonicalPAHElectronicMonsterBoundary : PAHElectronicMonsterBoundary
canonicalPAHElectronicMonsterBoundary =
  pahElectronicMonsterBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
