module DASHI.Physics.Closure.NSTriadKNLittlewoodPaleyInfrastructureInventory where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Jean-Michel Bony; Hajer Bahouri; Jean-Yves Chemin;
-- Raphael Danchin; Terence Tao; Dong Li; Xiaoyutao Luo;
-- DASHI repository contributors.
-- Titles:
--   * "Calcul symbolique et propagation des singularites pour les
--      equations aux derivees partielles non lineaires";
--   * "Fourier Analysis and Nonlinear Partial Differential Equations";
--   * "Lecture Notes 6 for 247B: Paradifferential calculus, fractional
--      chain and Leibnitz rules";
--   * "On a Frequency Localized Bernstein Inequality and Some Generalized
--      Poincare-Type Inequalities";
--   * "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal
--      Localization".
-- DOI:
--   * 10.24033/asens.1404;
--   * 10.1007/978-3-642-16830-7;
--   * Tao's lecture notes have no DOI;
--   * 10.48550/arXiv.1212.0183;
--   * 10.1007/s00021-019-0411-z.
--
-- PURPOSE
-- Inventory the Littlewood--Paley/paradifferential infrastructure already
-- present in DASHI.  The exact finite periodic hard-shell projector, its
-- derivative/curl commutation, resonant triad carrier, and Bony/Tao
-- classification are now constructed.  Smooth-projector norm comparison,
-- literal time-integral identification, and the continuation theorem remain
-- separate analytic obligations.
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
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as ExactLP

------------------------------------------------------------------------
-- Abstract smooth/analytic projector interface required by the external
-- continuation criteria.  The exact hard-shell module supplies the algebraic
-- support interface but not these continuous norm fields.
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

record LiteralNavierStokesBonyDecomposition : Set₁ where
  field
    VelocityField : Set
    lowHighTerm : VelocityField → VelocityField
    highLowTerm : VelocityField → VelocityField
    resonantTerm : VelocityField → VelocityField

    nonlinearTermEqualsThreeWaySplit : Set
    advectiveResidualIdentified : Set
    transverseResidualIdentified : Set

open LiteralNavierStokesBonyDecomposition public

------------------------------------------------------------------------
-- Proven infrastructure and honest open interfaces.
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

    exactPeriodicHardShellProjectorConstructed :
      ExactLP.periodicHardShellProjectorConstructed ≡ true

    ownedShellPointwiseReconstructionClosed :
      ExactLP.ownedShellPointwiseReconstructionClosed ≡ true

    exactDerivativeProjectorCommutationClosed :
      ExactLP.derivativeProjectorCommutationClosed ≡ true

    exactCurlProjectorCommutationClosed :
      ExactLP.curlProjectorCommutationClosed ≡ true

    exactBonyTaoInteractionClassificationClosed :
      ExactLP.bonyTaoInteractionClassificationClosed ≡ true

    exactFiniteInteractionRecompositionClosed :
      ExactLP.finiteInteractionRecompositionClosed ≡ true

    smoothPeriodicProjectorFamilyClosed : Bool
    smoothHardProjectorNormComparisonClosed : Bool
    physicalTimeIntegralIdentificationClosed : Bool
    blockerResidualsIdentifiedWithBonyPieces : Bool
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
  ExactLP.periodicHardShellProjectorConstructedIsTrue
  ExactLP.ownedShellPointwiseReconstructionClosedIsTrue
  ExactLP.derivativeProjectorCommutationClosedIsTrue
  ExactLP.curlProjectorCommutationClosedIsTrue
  ExactLP.bonyTaoInteractionClassificationClosedIsTrue
  ExactLP.finiteInteractionRecompositionClosedIsTrue
  false
  false
  false
  false
  false

existingHardShellLPInfrastructureRecorded : Bool
existingHardShellLPInfrastructureRecorded = true

exactPeriodicLPBonyPDEInterfaceConstructed : Bool
exactPeriodicLPBonyPDEInterfaceConstructed = true

literalNavierStokesBonyNormDecompositionClosed : Bool
literalNavierStokesBonyNormDecompositionClosed = false

fullLocalizedContinuationProjectorInterfaceClosed : Bool
fullLocalizedContinuationProjectorInterfaceClosed = false

existingHardShellLPInfrastructureRecordedIsTrue :
  existingHardShellLPInfrastructureRecorded ≡ true
existingHardShellLPInfrastructureRecordedIsTrue = refl

exactPeriodicLPBonyPDEInterfaceConstructedIsTrue :
  exactPeriodicLPBonyPDEInterfaceConstructed ≡ true
exactPeriodicLPBonyPDEInterfaceConstructedIsTrue = refl

literalNavierStokesBonyNormDecompositionClosedIsFalse :
  literalNavierStokesBonyNormDecompositionClosed ≡ false
literalNavierStokesBonyNormDecompositionClosedIsFalse = refl

fullLocalizedContinuationProjectorInterfaceClosedIsFalse :
  fullLocalizedContinuationProjectorInterfaceClosed ≡ false
fullLocalizedContinuationProjectorInterfaceClosedIsFalse = refl
