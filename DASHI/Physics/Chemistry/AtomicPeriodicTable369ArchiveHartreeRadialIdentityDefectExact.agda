module DASHI.Physics.Chemistry.AtomicPeriodicTable369ArchiveHartreeRadialIdentityDefectExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Surviving defect found by following the physical snowball into the actual
-- code-shaped Hartree object retained in the DASHI Atom archive.
--
-- Archive pages 422--425 define subshells as triples (n,l,occ), but the radial
-- solver is called as
--
--   solve_orbital(r, Z, l, V_H)
--
-- and selects select_range=(0,0): the lowest eigenpair for that l.  The
-- principal index n is discarded. Therefore 1s, 2s, 3s ... are not distinct
-- radial solver targets at a fixed Z,l,V_H. This prevents the retained code
-- object from paying a same-object atomic spectrum/ionization theorem.
--
-- This file records the defect without rewriting the historical source.  The
-- repair contract requires an n-sensitive radial-state selector (equivalently
-- radial-node/eigenpair identity plus orthogonality/tracking across SCF).
------------------------------------------------------------------------

record SubshellLabel : Set where
  constructor subshellLabel
  field
    principal : Nat
    angular : Nat

open SubshellLabel public

oneS : SubshellLabel
oneS = subshellLabel 1 0

twoS : SubshellLabel
twoS = subshellLabel 2 0

threeS : SubshellLabel
threeS = subshellLabel 3 0

threeP : SubshellLabel
threeP = subshellLabel 3 1

------------------------------------------------------------------------
-- Faithful abstraction of the archive call signature: only l survives into
-- the eigenproblem selector.
------------------------------------------------------------------------

archiveRadialTarget : SubshellLabel -> Nat
archiveRadialTarget s = angular s

oneSTarget : archiveRadialTarget oneS ≡ 0
oneSTarget = refl

twoSTarget : archiveRadialTarget twoS ≡ 0
twoSTarget = refl

threeSTarget : archiveRadialTarget threeS ≡ 0
threeSTarget = refl

sameAngularDifferentPrincipalCollapse12 :
  archiveRadialTarget oneS ≡ archiveRadialTarget twoS
sameAngularDifferentPrincipalCollapse12 = refl

sameAngularDifferentPrincipalCollapse23 :
  archiveRadialTarget twoS ≡ archiveRadialTarget threeS
sameAngularDifferentPrincipalCollapse23 = refl

------------------------------------------------------------------------
-- Minimal corrected identity: for hydrogenic/Coulomb-style radial indexing,
-- a bound (n,l) state has radial index n-l-1.  We do not implement subtraction
-- here; the repair contract carries an explicit radialStateIndex supplied by a
-- physical realization and requires it to distinguish same-l principal states.
------------------------------------------------------------------------

record RadialStateSelector : Set₁ where
  field
    RadialStateIndex : Set
    selectRadialState : SubshellLabel -> RadialStateIndex
    sameAngularDifferentPrincipalCanBeDistinguished : Set
    orthogonalityReceipt : Set
    scfStateTrackingReceipt : Set

record ArchiveHartreeRepair : Set₁ where
  field
    selector : RadialStateSelector
    Hamiltonian : Set
    Spectrum : Set
    buildHamiltonian : SubshellLabel -> Hamiltonian
    selectedSpectrum : SubshellLabel -> Spectrum
    principalIdentityPreserved : Set
    spectrumComesFromSelectedHamiltonian : Set

------------------------------------------------------------------------
-- Archive/run provenance status.
------------------------------------------------------------------------

record ArchiveHartreeRunReceipt : Set where
  constructor archiveHartreeRunReceipt
  field
    archiveCodeLocated : Bool
    archiveLaterRunClaimLocated : Bool
    earlierInterruptedRunClaimLocated : Bool
    exactStandaloneScriptLocated : Bool
    exactNumericOutputArtifactLocated : Bool
    exactFigureArtifactLocated : Bool
    principalIndexUsedByArchiveEigenSelector : Bool
    principalIndexUsedByArchiveEigenSelectorIsFalse :
      principalIndexUsedByArchiveEigenSelector ≡ false

canonicalArchiveHartreeRunReceipt : ArchiveHartreeRunReceipt
canonicalArchiveHartreeRunReceipt =
  archiveHartreeRunReceipt true true true false false false false refl

------------------------------------------------------------------------
-- Attribution receipt.  The archive is the primary programme/run narrative;
-- Hartree/Slater pay generic method provenance, not this code's correctness.
------------------------------------------------------------------------

record ArchiveHartreeAttribution : Set where
  constructor archiveHartreeAttribution
  field
    sourceObject : String
    sourcePages : String
    methodPrimaryDois : String
    qidCoordinates : String
    deweyCoordinates : String
    oeisCoordinates : String
    directLinks : String
    authority : String
    relationship : String

canonicalArchiveHartreeAttribution : ArchiveHartreeAttribution
canonicalArchiveHartreeAttribution =
  archiveHartreeAttribution
    "DASHI Atom archive, canonical thread 25ec0d2e654f33ea6f524f816b4c465e86ef21cf"
    "code pages 422-425; later run report pages 465-471; earlier interrupted-run report page 341"
    "Hartree 1928 DOI 10.1017/S0305004100011920; Slater 1928 DOI 10.1103/PhysRev.32.339"
    "atom Q9121; Hartree-Fock Q7879841; ionization energy Q483769"
    "539.7 atomic-physics topic coordinate; exact code-object Dewey not applicable"
    "A167268/A093907 structural-selector coordinates only"
    "archive attachment plus primary DOI links; exact standalone script URL unresolved"
    "primary internal provenance for what code/run was reported; generic literature authority for method family only"
    "the archive pays existence of a code-shaped Hartree attempt and a later run claim, but the n-erasure defect blocks same-object spectrum promotion"

------------------------------------------------------------------------
-- Non-promotion and corrected highest-alpha frontier.
------------------------------------------------------------------------

record ArchiveHartreeDefectBoundary : Set where
  constructor archiveHartreeDefectBoundary
  field
    laterRunClaimImpliesCorrectSpectrum : Bool
    sameLTargetCollapsePreservesPrincipalIdentity : Bool
    genericHartreeCitationRepairsImplementation : Bool
    toyIonizationCurvePaysCalibratedIonization : Bool
    repairedNSensitiveSelectorRequired : Bool

canonicalArchiveHartreeDefectBoundary : ArchiveHartreeDefectBoundary
canonicalArchiveHartreeDefectBoundary =
  archiveHartreeDefectBoundary false false false false true

record ArchiveHartreeDefectFrontier : Set where
  constructor archiveHartreeDefectFrontier
  field
    defect : String
    strongestPaidClaim : String
    firstRepair : String
    nextExecutionReceipt : String
    nextPhysicalPromotion : String
    paymentRule : String

canonicalArchiveHartreeDefectFrontier : ArchiveHartreeDefectFrontier
canonicalArchiveHartreeDefectFrontier =
  archiveHartreeDefectFrontier
    "archive solve_orbital receives l but not n and always requests the lowest eigenpair; same-l principal subshells collapse to the same radial target"
    "code-shaped Hartree implementation and later run narrative are located, with generic Hartree/Slater method provenance; physical spectrum correctness is not paid"
    "repair the eigenstate selector so each occupied (n,l) maps to a distinct radial state/node/eigenpair and preserve orthogonality plus state identity through SCF iterations"
    "commit a same-object runnable repaired producer with parameters, code hash, convergence diagnostics, energies and figure/data artifacts, then rerun it"
    "only after repaired execution: compare E(Z), IE1(Z), shell order and exceptions against authoritative atomic data and promote quantitative claims separately"
    "snowball acquisition is append-only: the later defect does not erase the historical run report, and the run report does not erase the defect"
