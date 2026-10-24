module DASHI.Physics.Gravity.KKE6OrbifoldBoundaryHiggsConsumerExact where

------------------------------------------------------------------------
-- 2026-10-25 original first-Tits E32/E33 six-invariant scalar source
-- plus a NEW gauge-allowed S1/Z2 fixed-plane 2x2 Chi term.
--
-- Actual SOURCE computation scripts:
-- check_kk_e6_orbifold_boundary_higgs_source.py (exact SymPy V6)
-- check_kk_e6_orbifold_boundary_higgs_hessian.py (PyTorch all36)
--
-- The original 36-real source belongs to unmerged E6 PR #1106:
-- V6(E32,E33+t E21)=3 t²+t⁴ (positive EW source curvature).
-- A boundary term for the orbifold-even Chi 2x2 allows a selected
-- nonzero t, but original E32/E33 amplitudes MUST respond.
-- IMPORTANT 2026-10-25 source correction: the prior gradient/Hessian are
-- for the spatially HOMOGENEOUS integrated zero-mode potential,
-- NOT a genuine solution of five-dimensional interior E-L plus
-- Robin boundary conditions. At t=.0246 the BULK t-gradient is
-- t(6-13t²)=+.147406469832, which cancels endpoint force ONLY
-- after integration. New owning BIDI is
-- KKE6OrbifoldIntervalBoundaryELConsumerExact and selected script
-- check_kk_e6_orbifold_interval_higgs_bvp.py.
-- The homogeneous full 36-real scalar matrix source has two NEGATIVE curvatures,
-- both PARITY ODD; only 18 physical constant scalar modes are even.
-- The selected EVEN 18x18 Hessian has 7 gauge zeros, 11 positive,
-- zero negative, conditional on the source trial parameters.
--
-- These finite Agda claims are CARDINAL/BIDI SOURCE LABELS, not
-- kernel proofs of a 36-real real-analysis Hessian or quantum QFT.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.Nat.Base using (_+_; _*_)
import DASHI.Physics.Gravity.KKE6OrbifoldVEVAnomalyModelForkExact as Orb
import DASHI.Core.FormalClaimTransportGeometryExact as Transport
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent

phiEvenComplexComponents : 2 * 2 ≡ 4
phiEvenComplexComponents = refl

chiEvenComplexComponents : 2 * 2 + 1 ≡ 5
chiEvenComplexComponents = refl

evenScalarRealZeroModes : 2 * (4 + 5) ≡ 18
evenScalarRealZeroModes = refl

originalBulkScalarRealComponents : 2 * (9 + 9) ≡ 36
originalBulkScalarRealComponents = refl

oddScalarRealNonzeroKKOnly : 18 + 18 ≡ 36
oddScalarRealNonzeroKKOnly = refl

evenGaugeMassiveAndPhotonCount : 7 + 1 ≡ 8
evenGaugeMassiveAndPhotonCount = refl

physicalEvenHessianCount : 7 + 11 ≡ 18
physicalEvenHessianCount = refl

-- The physical orbifold projection defines which Hessian operator
-- is the mass operator of FOUR-dimensional constant scalar modes.
data ScalarSpectrumConsumer : Set where
  unconstrainedAllThirtySixBulkDirections
  actualOrbifoldEvenEighteenZeroModes : ScalarSpectrumConsumer

originalBulkCarrierSize : ScalarSpectrumConsumer → Nat
originalBulkCarrierSize _ = 36

-- Boolean labels of actual SOURCE PYTHON NUMERIC Hessian result.
-- The two negative eigenvalues of the full 36-real Hessian belong
-- to parity-ODD bulk scalar fluctuations, not a 4D zero-mode mass.
selectedHasNegativeSourceHessianEigenvalue :
  ScalarSpectrumConsumer → Bool
selectedHasNegativeSourceHessianEigenvalue
  unconstrainedAllThirtySixBulkDirections = true
selectedHasNegativeSourceHessianEigenvalue
  actualOrbifoldEvenEighteenZeroModes = false

falseNotTrue : false ≡ true → ⊥
falseNotTrue ()

bulkCountCannotDeterminePhysicalZeroModeStability :
  Transport.ClaimNonTransportWitness
    originalBulkCarrierSize
    selectedHasNegativeSourceHessianEigenvalue
bulkCountCannotDeterminePhysicalZeroModeStability =
  Descent.consumerNonDescentWitness
    actualOrbifoldEvenEighteenZeroModes
    unconstrainedAllThirtySixBulkDirections
    refl falseNotTrue

-- The source-original E32/E33 branch has no EW E21 condensate.
-- An actual FIXED-PLANE gauge-invariant 2x2 Chi mass/quartic source
-- can introduce a conditional trial E21 stationary branch. This
-- introduces new radiative/odd KK/Dirac mass and stress obligations.
data EWSBSource : Set where
  oldPositiveSixInvariantOnly
  addedOrbifoldEvenBoundaryHiggsInteraction : EWSBSource

ewVEVAvailableInSelectedClassicalTrial : EWSBSource → Bool
ewVEVAvailableInSelectedClassicalTrial oldPositiveSixInvariantOnly = false
ewVEVAvailableInSelectedClassicalTrial
  addedOrbifoldEvenBoundaryHiggsInteraction = true

-- Global 5D UV gauge anomalies, full E6 (78) gauge source, full
-- interval odd-KK spectrum, quantum potential, and experiments
-- remain NOT PAID by finite cardinal statements.
