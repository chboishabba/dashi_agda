module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound87FourAnalyticLemmaExact where

------------------------------------------------------------------------
-- ROUND87: SHORTEST LITERAL JAFFE--WITTEN CLAY CUTSET = FOUR ANALYTIC FAMILIES
--
-- PRIMARY SOURCE
--
-- Arthur Jaffe and Edward Witten,
-- "Quantum Yang-Mills Theory", official Clay Mathematics Institute problem
-- description, in The Millennium Prize Problems.  No DOI assigned.
--
-- IMPORTANT CORRECTION TO THE PREVIOUS PLANNING NOTE
--
-- The literal problem description DOES require local gauge-invariant curvature
-- operators whose short-distance correlations agree with asymptotic freedom;
-- it explicitly says the predicted short-distance structure includes a stress
-- tensor and operator product expansion.  Therefore OPE/stress cannot simply be
-- deleted from the submission path.
--
-- What CAN be deleted is the stronger auxiliary theorem
--
--             integral T_00 = H_OS
--
-- together with its local-charge cutoff removal / essential-self-adjointness /
-- Stone-generator identification, because the literal Clay stress/OPE
-- postcondition does not consume it.  The positive Hamiltonian and mass gap are
-- separately reconstructed from the OS family.
--
-- Round87 therefore obtains a real 5 -> 4 research cutset by:
--
--   * treating the stress insertion as another marked coordinate of the SAME
--     completed differentiated RG state, so its nuclear-field completion is
--     downstream of the strengthened marked-source Hilbert-modulus theorem;
--
--   * keeping the physical short-distance stress/OPE/Ward/AF statement together
--     with OPE coefficient/remainder identification;
--
--   * using the existing Round77 same-H Gaussian/Ward/Maxwell + positive-gap
--     reductio for nontriviality, so no independent fourth-cumulant theorem is
--     required on the shortest route.
--
-- The optional cumulant route is also strengthened in Round87: a finite
-- same-family buffered cumulant plus the existing continuum error transport now
-- constructs an interacting continuum witness exactly.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound85SixAnalyticLemmaAttackExact
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact
import DASHI.Physics.YangMills.BalabanMarkedSourceCompositeStressFieldExact
import DASHI.Physics.YangMills.YangMillsSameFamilyCumulantMarginToInteractingExact
import DASHI.Physics.YangMills.BalabanClayT4SineDeterminesCosineAtomExact
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
-- Round86 already compiles four joint regular orbit enclosures in [-1/2,1/2]
-- into all-group positivity once the literal evaluator/trig/remainder data exist.
-- Round87 further removes an independent cosine interval producer: coherent
-- cos(k) intervals are derived algebraically from the primitive sin(k/2) boxes.
literalCompactSimplePositiveBetaLevel : ProofLevel
literalCompactSimplePositiveBetaLevel = conditional

-- B. ONE DIFFERENTIATED MARKED-SOURCE LOCALITY / FIELD THEOREM
--
-- On the SAME completed source-native RG state, prove mark-parametric locality
-- for physical Hessian separation and local insertions, and supply uniform
-- Hilbertian test-function moduli for BOTH curvature/composite and stress
-- insertion source derivatives.  Round85/87 then construct their nuclear fields
-- automatically with shared completed-state provenance.
physicalMarkedSourceLocalityCompositeStressHilbertModuliLevel : ProofLevel
physicalMarkedSourceLocalityCompositeStressHilbertModuliLevel = conditional

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
-- DOWNSTREAM THEOREMS THAT JUSTIFY THE 5 -> 4 RECUT
------------------------------------------------------------------------

literalClayStressOPEBoundaryLevel : ProofLevel
literalClayStressOPEBoundaryLevel = machineChecked

sameCompletedCompositeStressFieldCompilerLevel : ProofLevel
sameCompletedCompositeStressFieldCompilerLevel = machineChecked

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
--
-- A genuine next reduction would require an actual theorem that the SAME
-- differentiated marked-source construction in B also produces the physical
-- product/OPE one-step mixing law and stress short-distance Ward structure in D.
-- Merely putting B and D in one record would not count.  No 3-lemma claim is
-- asserted here.
------------------------------------------------------------------------

round87ThreeLemmaFusionProvedLevel : ProofLevel
round87ThreeLemmaFusionProvedLevel = conditional

-- No Clay solution inhabitant is asserted by this root.
------------------------------------------------------------------------
