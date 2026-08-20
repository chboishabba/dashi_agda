module DASHI.Physics.Closure.NSTriadKNLuoFilteredDefectExcursionRound21Validation where

------------------------------------------------------------------------
-- Cumulative validation root for Round Twenty-One.
-- Pinned workflow trigger after the checker definition is present on branch.
-- Validation-only stacked PR execution marker.
--
-- Imports the complete Round Twenty NEMGRO/periodic-symbol tranche and checks:
--
-- * exact magnitude-weighted direction-increment decomposition;
-- * sharp filtered angular contraction factor;
-- * finite pairwise defect-to-vorticity-increment transport;
-- * filtered-enstrophy signed surplus and finite weighted sum;
-- * deterministic bad-excursion residence tax with crossing charges;
-- * scaled Young bad-lane amplitude absorption;
-- * exact three-lane critical coefficient closure;
-- * five-class dyadic filtered-vorticity ledger;
-- * Yu/DASHI residual-basis separation and explicit regrouping;
-- * physical strain-kernel symmetry, trace, evenness and angular cancellation;
-- * polynomial cross-product defect evolution and five-source split.
--
-- No periodic principal-value distribution, continuum Calderon-Zygmund bound,
-- physical paraproduct estimate, unweighted far-field Carleson theorem,
-- Navier-Stokes crossing-charge budget, infinite critical summability, or
-- unconditional regularity theorem is asserted.
------------------------------------------------------------------------

import DASHI.Physics.Closure.NSTriadKNLuoNEMGROPhysicalAuditRound20Validation
import DASHI.Physics.Closure.NSTriadKNLuoMagnitudeWeightedDirectionIncrementExact
import DASHI.Physics.Closure.NSTriadKNLuoFilteredDirectionContractionExact
import DASHI.Physics.Closure.NSTriadKNLuoFilteredPairwiseDefectFiniteExact
import DASHI.Physics.Closure.NSTriadKNLuoFilteredEnstrophySurplusExact
import DASHI.Physics.Closure.NSTriadKNLuoBadExcursionResidenceTaxExact
import DASHI.Physics.Closure.NSTriadKNLuoBadExcursionYoungAbsorptionExact
import DASHI.Physics.Closure.NSTriadKNLuoThreeLaneCriticalClosureExact
import DASHI.Physics.Closure.NSTriadKNLuoDyadicFilteredVorticityLedgerExact
import DASHI.Physics.Closure.NSTriadKNLuoYuResidualBasisComparisonExact
import DASHI.Physics.Closure.NSTriadKNLuoPeriodicBiotSavartAngularCancellationExact
import DASHI.Physics.Closure.NSTriadKNLuoCrossProductDefectEvolutionAlgebraExact
