module DASHI.Physics.Closure.NSTriadKNOfficialFiniteFourierHermitianParsevalExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011. DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Select the repository's frozen coefficient-unitary convention as the
-- official finite periodic Fourier L2 convention.  The official global and
-- shell L2 quantities are represented by the same duplicate-free finite
-- Fourier folds as their coefficient counterparts.  Parseval is therefore a
-- definitional equality for this selected convention.
--
-- This module also transports the finite Hermitian coefficient pairing used by
-- the hard-projector theorem to the selected official pairing.  It does not
-- assert that an unrelated continuum-measure convention is definitionally the
-- same object; the selected convention is exactly the one already exported by
-- NSPeriodicCoefficientUnitaryNormAdapter.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.List using (List)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact as LP
import DASHI.Physics.Closure.NSTriadKNHardProjectorCoefficientSelfAdjointExact as Coefficient
import DASHI.Physics.Closure.NSTriadKNHardProjectorParsevalTransportExact as Parseval
import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorption
import DASHI.Physics.Closure.NSCompactGammaConcretePotentialInstantiation as Potential
import DASHI.Physics.Closure.NSCompactGammaAnalyticLeafCompletion as Leaves
import DASHI.Physics.Closure.NSPeriodicCoefficientUnitaryNormAdapter as Unitary
import DASHI.Physics.Closure.NSPeriodicOfficialNormIdentification as Official
open import DASHI.Physics.YangMills.CompactLieProofLevel

officialFiniteHermitianPairing :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) →
  List Z3.FourierMode →
  LP.FourierField model →
  LP.FourierField model →
  C3.Complex (LP.realField model)
officialFiniteHermitianPairing =
  Coefficient.coefficientHermitianPairing

officialFinitePairingIsCoefficientPairing :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) →
  (modes : List Z3.FourierMode) →
  (left right : LP.FourierField model) →
  Coefficient.coefficientHermitianPairing model modes left right
    ≡ officialFiniteHermitianPairing model modes left right
officialFinitePairingIsCoefficientPairing model modes left right = refl

officialFiniteHermitianParsevalTransport :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) →
  (modes : List Z3.FourierMode) →
  Parseval.PeriodicHermitianParsevalTransport model modes
officialFiniteHermitianParsevalTransport model modes = record
  { selectedHermitianPairing = officialFiniteHermitianPairing model modes
  ; pairingParseval = officialFinitePairingIsCoefficientPairing model modes
  }

officialHardProjectorOrthogonal :
  ∀ {r}
    (model : LP.PeriodicHardShellFourierPDE {r}) →
  (modes : List Z3.FourierMode) →
  (cutoff : Nat) →
  Parseval.HardProjectorOrthogonalCertificate model modes cutoff
officialHardProjectorOrthogonal model modes cutoff = record
  { parseval = officialFiniteHermitianParsevalTransport model modes
  ; lowSelfAdjoint =
      Parseval.hardLowSelectedPairingSelfAdjoint
        (officialFiniteHermitianParsevalTransport model modes) cutoff
  ; highSelfAdjoint =
      Parseval.hardHighSelectedPairingSelfAdjoint
        (officialFiniteHermitianParsevalTransport model modes) cutoff
  ; lowIdempotent =
      Coefficient.hardLowCoefficientIdempotent model cutoff
  ; highIdempotent =
      Coefficient.hardHighCoefficientIdempotent model cutoff
  }

officialCoefficientUnitaryGlobalParseval :
  ∀ {t}
    {A : Absorption.AbsorptionArithmetic}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : Unitary.CoefficientUnitaryNormInputs A C R F) →
  ∀ time state →
  Official.coefficientL2
      (Unitary.coefficientUnitaryOfficialNormIdentification I)
      time state
    ≡
  Official.physicalL2
      (Unitary.coefficientUnitaryOfficialNormIdentification I)
      time state
officialCoefficientUnitaryGlobalParseval =
  Unitary.coefficientUnitaryGlobalParseval

officialCoefficientUnitaryShellParseval :
  ∀ {t}
    {A : Absorption.AbsorptionArithmetic}
    {Time : Set t}
    {C : Potential.ThreeWayAdditiveCalculus A}
    {R : Leaves.ConcreteReserveLeaves A Time}
    {F : Leaves.RealFundamentalTheoremRealization A C R} →
  (I : Unitary.CoefficientUnitaryNormInputs A C R F) →
  ∀ time shell state →
  Official.shellCoefficientL2
      (Unitary.coefficientUnitaryOfficialNormIdentification I)
      time shell state
    ≡
  Official.shellPhysicalL2
      (Unitary.coefficientUnitaryOfficialNormIdentification I)
      time shell state
officialCoefficientUnitaryShellParseval =
  Unitary.coefficientUnitaryShellParseval

officialFiniteFourierHermitianParsevalLevel : ProofLevel
officialFiniteFourierHermitianParsevalLevel = machineChecked

officialFiniteFourierPairingSelected : Bool
officialFiniteFourierPairingSelected = true

officialPhysicalHardProjectorOrthogonalConstructed : Bool
officialPhysicalHardProjectorOrthogonalConstructed = true

officialFiniteFourierPairingSelectedIsTrue :
  officialFiniteFourierPairingSelected ≡ true
officialFiniteFourierPairingSelectedIsTrue = refl

officialPhysicalHardProjectorOrthogonalConstructedIsTrue :
  officialPhysicalHardProjectorOrthogonalConstructed ≡ true
officialPhysicalHardProjectorOrthogonalConstructedIsTrue = refl
