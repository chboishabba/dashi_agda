module DASHI.Physics.Closure.NSTriadKNResidualTransportOwnerFlowRound38Validation where

-- Round 38 is stacked on the complete Round-37 validation root.  The imports
-- below are only the new hard-math tranche: exact Fourier strain multiplier,
-- line-residual and thresholded HH-good geometry, finite/periodic PV
-- cancellation reductions, Z2-graded Com transport, evidence-indexed HH-bad
-- dissipation and occupation/crossing control, physically witnessed pre-tax
-- cancellation flow, and the F4 orbit/fibre plus ordered-incidence
-- permutation cancellation.
open import DASHI.Physics.Closure.NSTriadKNPQStabilizerSignedLedgerRound37Validation

open import DASHI.Physics.Closure.NSTriadKNFourierStrainMultiplierRound38Exact
open import DASHI.Physics.Closure.NSTriadKNVorticityLineResidualRound38Exact
open import DASHI.Physics.Closure.NSTriadKNVorticityLineOrthogonalResidualRound38Exact
open import DASHI.Physics.Closure.NSTriadKNHHGoodPhysicalThresholdStretchingRound38Exact
open import DASHI.Physics.Closure.NSTriadKNFinitePVDetailOperatorRound38Exact
open import DASHI.Physics.Closure.NSTriadKNPeriodicPVZeroMassFourierCriterionRound38Exact
open import DASHI.Physics.Closure.NSTriadKNComZ2GradingRound38Exact
open import DASHI.Physics.Closure.NSTriadKNHHBadRestrictedDissipationRound38Exact
open import DASHI.Physics.Closure.NSTriadKNHHBadOccupationCrossingRound38Exact
open import DASHI.Physics.Closure.NSTriadKNSignedOwnerCancellationFlowRound38Exact
open import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitFibreRound38Exact
open import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact
