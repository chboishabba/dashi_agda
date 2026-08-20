module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact where

------------------------------------------------------------------------
-- ROUND87/88: SHORTEST LITERAL JAFFE--WITTEN CUTSET = FOUR ANALYTIC FAMILIES
--
-- PRIMARY SOURCE
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- IMPORTANT CORRECTION TO THE PREVIOUS PLANNING NOTE
--
-- The literal problem description DOES require local gauge-invariant curvature
-- operators whose short-distance correlations agree with asymptotic freedom;
-- it explicitly says the predicted short-distance structure includes a stress
-- tensor and operator product expansion.  Therefore OPE/stress cannot simply be
-- deleted from the submission path.
--
-- What CAN be deleted is the stronger auxiliary theorem integral T_00 = H_OS,
-- together with its charge-cutoff / essential-self-adjoint / Stone-generator
-- identification.  The positive Hamiltonian and gap are separately reconstructed
-- from the OS family.
--
-- Round88 makes two genuine internal reductions:
--
--  A: CMP109 (5.36)--(5.41) says the beta consumer only needs ONE mixed
--     derivative of an off-diagonal vacuum-polarization component.  The third-
--     order remainder disappears in the two-jet quotient.  Therefore the finite
--     literal task is the Wilson/FP/Haar off-diagonal two-jet + its mixed
--     coefficient, not an unnecessarily strong all-component kernel theorem.
--
--  B: the composite/stress Hilbert moduli are no longer primitive analytic
--     leaves.  Reusing the exact finite weighted Cauchy--Schwarz/Gram-defect
--     theorem reduces both to ONE cutoff-uniform differentiated-source
--     coefficient-energy estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound85SixAnalyticLemmaAttackExact
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact
import DASHI.Physics.YangMills.BalabanMarkedSourceCoefficientEnergyHilbertCompilerExact
import DASHI.Physics.YangMills.YangMillsSameFamilyCumulantMarginToInteractingExact
import DASHI.Physics.YangMills.BalabanClayT4SineDeterminesCosineAtomExact
import DASHI.Physics.YangMills.BalabanCMP109MixedDerivativeBetaExtractionExact
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound77FiveAnalyticCutsetExact
import DASHI.Physics.YangMills.BalabanOPECoefficientRGRecurrenceUniquenessExact
import DASHI.Physics.YangMills.BalabanPolchinskiShellIntegralDebtExact

------------------------------------------------------------------------
-- AUTHORITATIVE SHORTEST LITERAL-CLAY RESEARCH CUTSET
------------------------------------------------------------------------

round87ShortestClayAnalyticCount : Nat
round87ShortestClayAnalyticCount = 4

-- A. UV ENTRY / ASYMPTOTIC FREEDOM HISTORY
--
-- On the SAME literal Wilson + reduced-FP + Haar Bałaban carrier:
--
--   beta_j(G) = C_A(G) 11/24 + r_local(g_{j-1}) + r_irrelevant(j)
--
-- with a cutoff/volume/scale/group-uniform strictly positive lower bound.
--
-- The primitive perturbative observable is now narrowed to the literal
-- off-diagonal two-jet and its mixed coefficient.  CMP109's Ward/Euclidean
-- decomposition makes the third-order remainder invisible to this coefficient.
-- Four regular-orbit enclosures and all-group positivity remain downstream once
-- that literal mixed coefficient / regular matching calculation is supplied.
literalCompactSimplePositiveBetaLevel : ProofLevel
literalCompactSimplePositiveBetaLevel = conditional

-- B. ONE DIFFERENTIATED MARKED-SOURCE LOCALITY / COEFFICIENT-ENERGY THEOREM
--
-- On the SAME completed source-native RG state, identify physical Hessian,
-- curvature/composite and stress marks with CMP116 analytic coordinates; prove
-- common cutoff-uniform radii and the spatial shell majorant; and prove ONE
-- weighted square-energy bound for the differentiated source coefficients.
-- Exact finite weighted Cauchy then gives the composite/stress Hilbert bounds,
-- and Round85/87 transports those to nuclear-continuous fields.
physicalMarkedSourceLocalityCompositeStressCoefficientEnergyLevel : ProofLevel
physicalMarkedSourceLocalityCompositeStressCoefficientEnergyLevel = conditional

-- C. SAME-DENSITY COMPACT-LIE HEAT/LANGEVIN MASS GAP
--
-- On the SAME effective density, prove the heat/Doob negative-Hessian shell
-- debt is summable and identify/dominate the covariant derivative influence by
-- the marked Hessian locality from B.  Existing Ricci/LSI, finite-speed/Dyson,
-- clustering and OS spectral compilers then yield Delta>0 on the reconstructed H.
sameDensityCompactLieHeatLangevinMassGapLevel : ProofLevel
sameDensityCompactLieHeatLangevinMassGapLevel = conditional

-- D. SAME-FAMILY SHORT-DISTANCE OPE / STRESS / AF IDENTIFICATION
--
-- For the local fields supplied by B, prove the physical product remainder is
-- the marked RG tail; the OPE coefficients obey the SAME one-step mixing law and
-- UV normalization as the asymptotically-free reference coefficients; and the
-- stress insertion has the required local/Ward short-distance structure.  The
-- all-depth coefficient equality is already induction.  Under the Gaussian
-- reductio, expose the local two-derivative Ward kernel consumed by the existing
-- Round77 same-H Maxwell/gap contradiction, so nontriviality is downstream of
-- C + D rather than a fifth independent theorem.
sameFamilyShortDistanceOPEStressAFLevel : ProofLevel
sameFamilyShortDistanceOPEStressAFLevel = conditional

------------------------------------------------------------------------
-- DOWNSTREAM THEOREMS THAT JUSTIFY / SHARPEN THE FOUR-FAMILY RECUT
------------------------------------------------------------------------

literalClayStressOPEBoundaryLevel : ProofLevel
literalClayStressOPEBoundaryLevel = machineChecked

sameCompletedCompositeStressFieldCompilerLevel : ProofLevel
sameCompletedCompositeStressFieldCompilerLevel = machineChecked

markedSourceCoefficientEnergyToHilbertCauchyLevel : ProofLevel
markedSourceCoefficientEnergyToHilbertCauchyLevel = machineChecked

cmp109MixedDerivativeBetaExtractionLevel : ProofLevel
cmp109MixedDerivativeBetaExtractionLevel = machineChecked

sineHalfDeterminesCosineIntervalLevel : ProofLevel
sineHalfDeterminesCosineIntervalLevel = machineChecked

allDepthOPECoefficientRecurrenceLevel : ProofLevel
allDepthOPECoefficientRecurrenceLevel = machineChecked

sameFamilyBufferedCumulantAlternativeNontrivialityLevel : ProofLevel
sameFamilyBufferedCumulantAlternativeNontrivialityLevel = machineChecked

round77GapPlusLocalWardNontrivialityCompilerLevel : ProofLevel
round77GapPlusLocalWardNontrivialityCompilerLevel = machineChecked

heatShellDebtSummationLevel : ProofLevel
heatShellDebtSummationLevel = machineChecked

------------------------------------------------------------------------
-- POSSIBLE 4 -> 3 TARGET -- NOT YET A DECREMENT
------------------------------------------------------------------------

round87ThreeLemmaFusionProvedLevel : ProofLevel
round87ThreeLemmaFusionProvedLevel = conditional

-- No Clay solution inhabitant is asserted by this root.
------------------------------------------------------------------------
