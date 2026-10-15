module DASHI.Physics.Chemistry.AmmoniaC3ElectronicSymmetryExact where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Moonshine.C3FourierConjugationExact as Fourier

------------------------------------------------------------------------
-- NH3 electronic / vibronic C3 symmetry fixture.
--
-- Attribution boundary:
--   * NIST is used as an evaluated/compiled source for the neutral NH3
--     ground-state label 1A1, C3v symmetry, and symmetry-resolved modes.
--   * Yin et al. 2002 is used for the published neutral-ground-state orbital
--     configuration (1a1)^2(2a1)^2(1e)^4(3a1)^2.
--   * The restriction E|C3 = zeta + zeta^2 is DASHI representation-theory
--     reconstruction using the already-certified exact C3 Fourier carrier.
--
-- None of these citations supplies a DASHI proof, a literal many-electron
-- wavefunction, a Hamiltonian, or a reaction mechanism.
------------------------------------------------------------------------

nistNH3EvaluatedElectronicSource : Source.AttributedSource
nistNH3EvaluatedElectronicSource =
  Source.mkNoDOISource
    "National Institute of Standards and Technology"
    "Ammonia evaluated symmetry and energetic data"
    "NIST Chemistry WebBook / CCCBDB"
    "2026"
    "https://cccbdb.nist.gov/palistx.asp"
    Source.institutionalSource
    "evaluated compilation recording neutral NH3 as 1A1, C3v and linking the protonated species; used only for claim-specific state/symmetry coordinates"
    Source.publicAttribution

yinEtAl2002OrbitalSource : Source.AttributedSource
yinEtAl2002OrbitalSource =
  Source.mkDOISource
    "Shu-Hui Yin; Hong-Ping Liu; Jian-Yang Zhang; Bo Jiang; Da-Li Xu; Li Wang; Guo-He Sha; Nan-Quan Lou"
    "Femtosecond (2+1') pump-probe mass spectroscopy on the Rydberg states of ammonia"
    "Chemical Physics Letters 356 (2002) 227-232"
    "2002"
    "10.1016/S0009-2614(02)00255-5"
    "https://doi.org/10.1016/S0009-2614(02)00255-5"
    Source.academicArticleSource
    "published source explicitly stating pyramidal C3v ground-state ammonia with orbital configuration (1a1)^2(2a1)^2(1e)^4(3a1)^2; not authority for DASHI's C3 Fourier restriction theorem"
    Source.publicAttribution

ritchieKing1967SCFSource : Source.AttributedSource
ritchieKing1967SCFSource =
  Source.mkDOISource
    "C. D. Ritchie; Harry F. King"
    "Gaussian Basis SCF Calculations for OH-, H2O, NH3, and CH4"
    "The Journal of Chemical Physics 47 (1967) 564-570"
    "1967"
    "10.1063/1.1711932"
    "https://doi.org/10.1063/1.1711932"
    Source.academicArticleSource
    "independent computational electronic-structure provenance for NH3 SCF/LCAO treatment; does not create experimental authority or a same-object DASHI Hamiltonian"
    Source.publicAttribution

data ElectronicC3Phase : Set where
  invariant zeta zetaSquared : ElectronicC3Phase

phaseFourierRow : ElectronicC3Phase → Fourier.FourierRow
phaseFourierRow invariant = Fourier.chi0
phaseFourierRow zeta = Fourier.chi1
phaseFourierRow zetaSquared = Fourier.chi2

zetaAndZetaSquaredAreConjugate :
  Fourier.conjugateRow (phaseFourierRow zeta)
  ≡ phaseFourierRow zetaSquared
zetaAndZetaSquaredAreConjugate = Fourier.chi1ConjugateIsChi2

data C3vIrrep : Set where
  A1 A2 E : C3vIrrep

record EPhasePair : Set where
  constructor ePhasePair
  field
    phasePlus : ElectronicC3Phase
    phaseMinus : ElectronicC3Phase
    plusFourierRow : Fourier.FourierRow
    minusFourierRow : Fourier.FourierRow

open EPhasePair public

canonicalEPhasePair : EPhasePair
canonicalEPhasePair =
  ePhasePair zeta zetaSquared Fourier.chi1 Fourier.chi2

record NeutralElectronicReceipt : Set where
  constructor neutralElectronicReceipt
  field
    molecularFormula : String
    pointGroup : String
    groundStateLabel : String
    orbitalConfiguration : String
    totalElectrons : Nat
    a1Electrons : Nat
    eElectrons : Nat
    sourceStateAuthority : Source.AttributedSource
    sourceOrbitalAuthority : Source.AttributedSource
    independentSCFProvenance : Source.AttributedSource

open NeutralElectronicReceipt public

canonicalNeutralElectronicReceipt : NeutralElectronicReceipt
canonicalNeutralElectronicReceipt =
  neutralElectronicReceipt
    "NH3"
    "C3v"
    "1A1"
    "(1a1)^2(2a1)^2(1e)^4(3a1)^2"
    10
    6
    4
    nistNH3EvaluatedElectronicSource
    yinEtAl2002OrbitalSource
    ritchieKing1967SCFSource

------------------------------------------------------------------------
-- Representation reconstruction.
--
-- A1 restricts trivially to C3.  The real two-dimensional E irrep becomes the
-- conjugate nontrivial one-dimensional phase pair over the exact cyclotomic
-- carrier.  This is DASHI group-theory reconstruction, not copied source text.
------------------------------------------------------------------------

irrepC3Phases : C3vIrrep → List ElectronicC3Phase
irrepC3Phases A1 = invariant ∷ []
irrepC3Phases A2 = invariant ∷ []
irrepC3Phases E = zeta ∷ zetaSquared ∷ []

groundStateC3Phase : ElectronicC3Phase
groundStateC3Phase = invariant

record ElectronicSymmetryBoundary : Set where
  constructor electronicSymmetryBoundary
  field
    sourceBackedOrbitalSymmetryCoordinatesPaid : Bool
    sourceBackedOrbitalSymmetryCoordinatesPaidIsTrue :
      sourceBackedOrbitalSymmetryCoordinatesPaid ≡ true

    exactC3RestrictionOfA1AndECarried : Bool
    exactC3RestrictionOfA1AndECarriedIsTrue :
      exactC3RestrictionOfA1AndECarried ≡ true

    fullAbInitioElectronicWavefunctionPaid : Bool
    fullAbInitioElectronicWavefunctionPaidIsFalse :
      fullAbInitioElectronicWavefunctionPaid ≡ false

    sameObjectHamiltonianPaid : Bool
    sameObjectHamiltonianPaidIsFalse : sameObjectHamiltonianPaid ≡ false

    orbitalLabelsDetermineReactionPath : Bool
    orbitalLabelsDetermineReactionPathIsFalse :
      orbitalLabelsDetermineReactionPath ≡ false

    nistCompilationCreatesDASHIProof : Bool
    nistCompilationCreatesDASHIProofIsFalse :
      nistCompilationCreatesDASHIProof ≡ false

    publishedOrbitalConfigurationCreatesMonsterModule : Bool
    publishedOrbitalConfigurationCreatesMonsterModuleIsFalse :
      publishedOrbitalConfigurationCreatesMonsterModule ≡ false

open ElectronicSymmetryBoundary public

canonicalElectronicSymmetryBoundary : ElectronicSymmetryBoundary
canonicalElectronicSymmetryBoundary =
  electronicSymmetryBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
