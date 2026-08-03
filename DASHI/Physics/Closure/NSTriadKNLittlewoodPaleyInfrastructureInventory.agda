module DASHI.Physics.Closure.NSTriadKNLittlewoodPaleyInfrastructureInventory where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; Terence Tao; Dong Li; DASHI repository contributors.
-- Titles:
--   * "Calcul symbolique et propagation des singularites pour les
--      equations aux derivees partielles non lineaires";
--   * "Fourier Analysis and Nonlinear Partial Differential Equations";
--   * "Lecture Notes 6 for 247B: Paradifferential calculus, fractional
--      chain and Leibnitz rules";
--   * "On a Frequency Localized Bernstein Inequality and Some Generalized
--      Poincare-Type Inequalities".
-- DOI:
--   * 10.24033/asens.1404;
--   * 10.1007/978-3-642-16830-7;
--   * Tao's lecture notes have no DOI;
--   * 10.48550/arXiv.1212.0183.
--
-- PURPOSE
-- Inventory the Littlewood--Paley/paradifferential infrastructure already
-- present in DASHI before selecting a frequency-localized continuation
-- theorem.  The inventory deliberately distinguishes the existing exact
-- periodic hard-shell calculus from the still-missing smooth-projector,
-- reconstruction, curl-commutation and time-dependent dissipation-wavenumber
-- interfaces required by the Cheskidov--Shvydkoy / Cheskidov--Dai routes.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNExactDyadicShellGeometry as Geometry
import DASHI.Physics.Closure.NSTriadKNHardDyadicShellOwner as HardShell
import DASHI.Physics.Closure.NSTriadKNRationalFiniteBernstein as Bernstein
import DASHI.Physics.Closure.NSTriadKNTaoFrozenLegParaproductProgram as Tao
import DASHI.Physics.Closure.NSTriadKNOutputRelocationKatoPonceBonyScopeAudit as Bony
import DASHI.Physics.Closure.NSTriadKNDongLiFrequencyLocalizedCoercivityAudit as DongLi

------------------------------------------------------------------------
-- Abstract projector interface required by localized continuation criteria.
-- No canonical inhabitant is asserted here.
------------------------------------------------------------------------

record PeriodicLittlewoodPaleyProjectorInterface : Set₁ where
  field
    Field : Set

    shellProjector : Nat → Field → Field
    lowProjector : Nat → Field → Field

    exactShellSupport : Set
    finiteNeighbourOverlap : Set
    reconstructionFromShells : Set
    lowProjectorIsShellSum : Set

    curlCommutesWithShellProjector : Set
    derivativeCommutesWithShellProjector : Set

    shellBernsteinL2ToLInfinity : Set
    shellVorticityVelocityComparison : Set

open PeriodicLittlewoodPaleyProjectorInterface public

record HardShellToSmoothProjectorComparison
    (hard smooth : PeriodicLittlewoodPaleyProjectorInterface) : Set₁ where
  field
    hardShellBandControlsSmoothShell : Set
    smoothShellBandControlsHardShell : Set
    comparisonUsesUniformFiniteBand : Set
    comparisonPreservesCurlBounds : Set

open HardShellToSmoothProjectorComparison public

------------------------------------------------------------------------
-- Proven existing infrastructure and honest open interfaces.
------------------------------------------------------------------------

record LittlewoodPaleyInfrastructureReceipt : Set where
  constructor receipt
  field
    exactThreeLegDyadicGeometryDefined :
      Geometry.canonicalAbsolutePredicatesDefined ≡ true

    hardDyadicShellConventionDefined :
      HardShell.hardDyadicShellConventionDefined ≡ true

    radiusEqualityShellTransportClosed :
      HardShell.radiusEqualityTransportClosed ≡ true

    finiteSupportBernsteinClosed :
      Bernstein.finiteBernsteinCountingClosed ≡ true

    frozenLegParaproductTrichotomyRecorded :
      Tao.taoTransposeAndTrichotomySourceRepresented ≡ true

    bonyParaproductMechanismRecorded :
      Bony.bonyParaproductMechanismRecorded ≡ true

    periodicFrequencyLocalizedCoercivityRecorded :
      DongLi.dongLiFrequencyLocalizedCoercivityRecorded ≡ true

    smoothPeriodicProjectorFamilyClosed : Bool
    shellReconstructionClosed : Bool
    curlProjectorCommutationClosed : Bool
    hardSmoothProjectorComparisonClosed : Bool
    timeDependentDissipationWavenumberClosed : Bool

open LittlewoodPaleyInfrastructureReceipt public

littlewoodPaleyInfrastructureReceipt : LittlewoodPaleyInfrastructureReceipt
littlewoodPaleyInfrastructureReceipt = receipt
  Geometry.canonicalAbsolutePredicatesDefinedIsTrue
  HardShell.hardDyadicShellConventionDefinedIsTrue
  HardShell.radiusEqualityTransportClosedIsTrue
  Bernstein.finiteBernsteinCountingClosedIsTrue
  Tao.taoTransposeAndTrichotomySourceRepresentedIsTrue
  Bony.bonyParaproductMechanismRecordedIsTrue
  DongLi.dongLiFrequencyLocalizedCoercivityRecordedIsTrue
  false
  false
  false
  false
  false

existingHardShellLPInfrastructureRecorded : Bool
existingHardShellLPInfrastructureRecorded = true

existingHardShellLPInfrastructureRecordedIsTrue :
  existingHardShellLPInfrastructureRecorded ≡ true
existingHardShellLPInfrastructureRecordedIsTrue = refl

fullLocalizedContinuationProjectorInterfaceClosed : Bool
fullLocalizedContinuationProjectorInterfaceClosed = false

fullLocalizedContinuationProjectorInterfaceClosedIsFalse :
  fullLocalizedContinuationProjectorInterfaceClosed ≡ false
fullLocalizedContinuationProjectorInterfaceClosedIsFalse = refl
