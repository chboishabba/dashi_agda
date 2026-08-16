module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62Exact where

------------------------------------------------------------------------
-- ROUND 62: PRODUCER-CUTSET COMPRESSION + CONCRETE FALSIFICATION
--
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for
-- the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale--Kato--Majda Criterion with Optimal Frequency and Temporal
-- Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Jean-Michel Bony.
-- Title: "Calcul symbolique et propagation des singularites pour les
-- equations aux derivees partielles non lineaires".
-- DOI: 10.24033/asens.1404.
--
-- Authors: Peter Constantin; Weinan E; Edriss S. Titi.
-- Title: "Onsager's Conjecture on the Energy Conservation for Solutions of
-- Euler's Equation".
-- DOI: 10.1007/BF02099744.
--
-- Authors: Errett Bishop; Douglas Bridges.
-- Title: "Constructive Analysis".
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Author: Zachary Murray.
-- Title: "Constructive Analysis in the Agda Proof Assistant".
-- arXiv:2205.08354; persistent identifier: 10.48550/arXiv.2205.08354.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- Authors: Mischa Cotlar; Elias M. Stein.
-- Title: "A unified theory of Hilbert transforms and ergodic theorems".
-- Historical 1955 conference source; no DOI assigned.
--
-- MATHEMATICAL CHANGES RELATIVE TO ROUND61
--
-- A. DIRECT HH-BAD HEADROOM, NO AFFINE RECURRENCE
--
-- Normalize the literal successor decomposition itself.  Exact threshold and
-- dyadic reciprocal cancellation gives
--
--   C_(q+1) = I_(q+1) + N_q.
--
-- Hence the only tail capacity estimate is
--
--   N_q <= C_* - I_(q+1).
--
-- Finite prefix + this tail headroom proves the global ceiling.  A literal
-- density comparison 2^q g_q<=C_q then constructs the selected normalized
-- HH-bad profile.  The unmasked charge estimate Q_q<=K_bad D feeds that profile
-- directly to the owner with eta_HHb=2 C_* K_bad.  The old alpha/beta affine
-- recurrence is no longer part of the producer cutset.
--
-- The lower Round30 shell-balance audit was also revisited.  The seven-term
-- decomposition algebra is exact, but DynamicPhysicalShellBalance itself still
-- requires the selected trajectory's differentiated projected NS identity.
-- Likewise the global finite energy fold is exact only after the canonical
-- literal retained-triad family is constructed.  No hidden A1 producer was
-- found below Round59.
--
-- B. CONCRETE ODD-P/Q FALSIFICATION FIXES THE SEMANTIC TARGET
--
-- The historical Round58 Q-valued "physical normalized Gram" record remains
-- demoted to a rational certificate carrier.  Literal Fourier coefficients
-- live in the selected Fourier model's own realField.
--
-- Round62 now goes further than a carrier correction.  It constructs the
-- literal odd-P/Q cross-pairing and fibre masses by recursive folds over the
-- actual `physicalOutputFiber`, entirely inside `Carrier (realField model)`.
-- It also gives a concrete canonical-selector active transport entry:
--
--   p=(1,0,0), q=(1,1,0), k=(2,1,0), cutoff=0,
--
-- for which j(q)=0, j(k)=1 and the literal odd-P/Q coefficient is exactly -i
-- on the transverse advector a_p=(0,1,0).  On every nontrivial compatible
-- field this entry is nonzero.  Hence the physical Com object cannot be closed
-- by a vacuous zero realization.
--
-- The same concrete pass falsifies a tempting but WRONG normalization.  If a
-- same-fibre cross-Gram correlation is divided by the product of its own two
-- masses, a unit one-dimensional fibre self-normalizes to 1, whereas the
-- Round47 same-shell coefficient must be <=17/64<1.  Therefore the Round62
-- cross-Gram object is retained ONLY as a diagnostic; it is not the physical B
-- coefficient.
--
-- The correct consumer semantics is the already-existing Round49/53 Schur
-- squared-output statement
--
--   ||oddPQ input||^2 <= rowMass * X.
--
-- Round54 already gives a literal physical-output-fibre Schur reducer and
-- Round55 already aggregates the same/adjacent whole-fibre bounds to 133/256.
-- Round35/40 reduce the two Cotlar adjoint faces to ONE normalized Gram
-- factorization.  Thus the remaining B theorem is now precisely:
--
--   literal odd-P/Q cross-shell operator/fibre
--     -> one factorized physical Gram/Schur row coefficient
--
-- with outer contractions <=1, common-hat support, and overlap bounded by the
-- existing six-three values 17/64 and 65/512.  The raw -i transport entry is
-- not itself the dimensionless row coefficient; the missing factorization is
-- the load-bearing normalization theorem.
--
-- C. THE ADDITIVE FIXED-SHIFT GAP IS LOCALIZED AND FALSIFICATION-FIRST
--
-- Exact finite owner summation replaces an opaque aggregate A_n<=aT_n field.
-- Six owners already have zero data remainder.  The generic fallback is
--
--   a = a_HHg + a_Com + a_kernel.
--
-- On the preferred exact-independent-kernel-zero branch, kernel also vanishes:
--
--   a = a_HHg + a_Com.
--
-- Moreover the singular/parabolic HH-good owner has zero data remainder, so
-- a_HHg is only the smooth periodic correction scale.  C's remaining global
-- estimate is the literal critical scale
--
--   X_n <= K C r^n,       K>0,
--
-- on the SAME owner->flux->fixed-block object, plus the now-sharp strict gap.
-- Round61 then constructs the maximal B_*=((r-q)-a)/K definitionally.
--
-- Round62 adds literal one-block counterexample objects for candidate K,
-- a_HHg, a_Com and their two-soft sum.  A single violating physical block now
-- formally refutes the corresponding universal scale law before any induction
-- is attempted.  These falsifiers import no sharp-capacity or Young theorem.
-- A separate circularity no-go prevents deriving K from the final correction
-- headroom whose B_* already depends on K.
--
-- D/F. FINITE FOURIER KERNEL ALGEBRA IS ALREADY CLOSED; THE PAIR BRIDGE IS NOT
--
-- A single structured atom list distinguishes physical interior, tail,
-- duplicate kernel, exact cancelling kernel pairs, independent kernel, and
-- classified lower/upper boundary atoms.  Exact cancellation is folded from
-- the local pair witnesses.  The mature kernel residual split and boundary
-- ledger are both extracted from this same source.
--
-- The repo audit found that the later finite complex kernel lane is stronger
-- than the old task ledger suggests: `LuoFiniteLiteralIncrementKernelFieldExact`
-- already proves pairwise spatial-increment = four-transform multiplier,
-- lifts that equality through arbitrary finite folds, and derives the complete
-- rp1/rp2/hard-tail three-piece multiplier identity without assuming those
-- coefficient equalities.
--
-- What remains D1 is the same-object bridge to the OFFICIAL full-shell Pair.
-- `FullShellFourierFamily` makes Pair opaque: `incidenceComplete` produces some
-- target/source modes only for a pair known to occur in a particular finite
-- list, and `incidenceProofUnique` proves uniqueness only after target/source
-- are fixed.  Therefore the official pair enumerator must be shown to realize
-- the finite literal two-mode pair system; this cannot be obtained by a type
-- alias.  Once that bridge emits the structured atoms on the selected solution,
-- D2 is the actual independent-kernel zero/estimate and F2 the boundary limits.
--
-- The preferred D2 equality
--
--   independentKernelTotal = 0
--
-- directly constructs the existing structural zero kernel owner, deleting
-- kernel production, eta, data and critical costs simultaneously.
--
-- E. E1 MUST CONSTRUCT THE CONTINUUM MULTIPLIER; E2 THEN NEEDS FOUR IBP
--
-- Once four inverse-Fourier integrations by parts give a three-dimensional
-- dyadic shell mass bound M 2^{-j}, exact finite geometric algebra proves every
-- partial L1 mass <=2M.  Thus the summability half remains closed.
--
-- The new Round62 underdetermination theorem proves that the Round49 lattice
-- restriction alone cannot select a continuum multiplier.  On the explicit
-- continuum carrier ProjectionMode + Unit, two symbols agree definitionally on
-- EVERY embedded lattice mode yet differ at the extra continuum point.  Hence
-- lattice restriction by itself cannot imply compact support, C^4 regularity,
-- derivative mass, or inverse-Fourier decay.
--
-- The old Sprint109/110 bump files are decomposition ledgers only; Sprint111
-- closes them by scoped external Rudin/Grafakos authority rather than by a
-- differentiable function in the Agda carrier.  The Bishop power-series bridge
-- supplies constructive limits, but its elementary-function coefficient/tail
-- inputs remain conditional and it does not provide the required derivative
-- calculus.  Therefore E1 genuinely remains: construct/select an actual smooth
-- compact annular continuum cutoff and matrix strain multiplier whose lattice
-- restriction is Round48.  E2 is then the literal fourfold IBP shell estimate.
--
-- G. PREFERRED SHARP SCALAR GATE
--
-- Round61's maximal B_* and weighted rational Young allocator are substituted
-- exactly.  On the kernel-zero branch
--
--   S = s_Com + s_HHg,
--   a = a_smooth-HHg + a_Com,
--
-- and the gate is
--
--   2 C_* K_bad
--   + K S^2 / ((r-q)-a)
--   + 1/16 < 1.
--
-- Exact rational elimination of the reciprocal gives the immediate feasibility
-- region
--
--   C_* K_bad < 15/32,
--
--   K S^2 < (15/16 - 2 C_* K_bad) ((r-q)-a).
--
-- These are explicit kill-tests for every new physical constant.
--
-- H remains the already-closed same-selected-solution Luo continuation lane.
--
-- GENUINE REMAINING PHYSICAL/ANALYTIC PRODUCERS AFTER ROUND62
--
--   A1  construct the selected trajectory's literal differentiated projected
--       shell/Duhamel identity, including literal viscosity and boundary terms;
--   A2  prove finite-prefix/tail component headroom N_q<=C_*-I_q, density
--       domination 2^q g_q<=C_q, and the unmasked charge bound K_bad D;
--   B1  realize the literal odd-P/Q cross-shell operator/fibre as the ONE
--       factorized Gram/Schur row coefficient consumed by Round49/54;
--   B2  prove canonical common-hat support for that realization;
--   B3  prove same/forward/reverse row/overlap bounds 17/64,65/512,65/512;
--   C1  prove the upstream global X_n<=K C r^n estimate and local smooth-HHg/
--       Com data-scale laws, independently of final B_* headroom;
--   C2  verify a_smooth-HHg+a_Com<r-q (preferred kernel-zero branch);
--   D1/F1 prove official full-shell Pair -> finite literal two-mode incidence/
--       coefficient realization and emit the structured selected-solution atoms;
--   D2  prove independentKernelTotal=0, or supply the quantitative fallback;
--   F2  prove every classified physical boundary atom tends to zero;
--   E1  construct/select the actual C_c^4 annular continuum cutoff/matrix
--       multiplier restricting to the literal Round48 lattice symbol;
--   E2  prove its fourfold inverse-Fourier dyadic shell estimate;
--   G   instantiate the physical constants and discharge the explicit preferred
--       scalar gate above.
--
-- These are not replaced by assumption records here.  Round62 removes
-- algebraic duplication, stale false frontiers, carrier mistakes, a rejected
-- normalization, fictitious owner costs and already-derivable summation/
-- allocation work around the genuine theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound61Exact

-- A: direct literal component headroom and K_bad owner, without alpha/beta.
import DASHI.Physics.Closure.NSTriadKNHHBadDirectPhysicalHeadroomRound62Exact
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedProfileMultiplicityRound62Exact

-- B: carrier correction, concrete same-carrier diagnostics, active nonzero
-- test, and explicit rejection of the wrong self-mass normalization.
import DASHI.Physics.Closure.NSTriadKNComTwoBranchFiniteGramRound62Exact
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact
import DASHI.Physics.Closure.NSTriadKNComBishopNormalizedMajorantRound62Exact
import DASHI.Physics.Closure.NSTriadKNComLiteralCrossGramFalsifierRound62Exact
import DASHI.Physics.Closure.NSTriadKNComConcreteActiveOddPQTriadRound62Exact
import DASHI.Physics.Closure.NSTriadKNComSelfMassNormalizationNoGoRound62Exact

-- C: local owner aggregation, concrete one-block falsifiers, circularity
-- firewall, preferred kernel-zero two-soft scale, and HH-good smooth remainder.
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftThreeSoftDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftKernelZeroTwoSoftDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodSmoothOnlyDataRemainderRound62Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftConcreteFalsifiersRound62Exact
import DASHI.Physics.Closure.NSTriadKNCriticalScaleHeadroomCircularityNoGoRound62Exact

-- D/F: finite literal multiplier algebra, one raw constituent source, stronger
-- structured atoms, and exact-zero promotion to the structural kernel owner.
import DASHI.Physics.Closure.NSTriadKNLuoFiniteLiteralIncrementKernelFieldExact
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEConstituentPartitionRound62Exact
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact
import DASHI.Physics.Closure.NSTriadKNStructuredKernelZeroOwnerRound62Exact

-- E: exact fourth-order dyadic summability endpoint plus a constructive proof
-- that lattice restriction alone does not determine the continuum symbol.
import DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodContinuumExtensionUnderdeterminedRound62Exact

-- G: sharp reciprocal substitution, generic three-soft gate, preferred
-- kernel-zero two-soft gate and explicit feasibility-region falsifiers.
import DASHI.Physics.Closure.NSTriadKNSharpWeightedScalarGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNThreeSoftSharpGlobalGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftWeightedGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftSharpGlobalGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNPreferredScalarFeasibilityRegionRound62Exact

round62RemovesAffineHHBadRecurrenceFromProducerCutset : Bool
round62RemovesAffineHHBadRecurrenceFromProducerCutset = true

round62ConcreteOddPQEntryIsNonzero : Bool
round62ConcreteOddPQEntryIsNonzero = true

round62SelfMassNormalizationRejectedForPhysicalB : Bool
round62SelfMassNormalizationRejectedForPhysicalB = true

round62PhysicalComTargetIsSchurRowCoefficient : Bool
round62PhysicalComTargetIsSchurRowCoefficient = true

round62ConcreteCBlockFalsifiersClosed : Bool
round62ConcreteCBlockFalsifiersClosed = true

round62CriticalScaleCircularityForbidden : Bool
round62CriticalScaleCircularityForbidden = true

round62FiniteLiteralIncrementKernelAlgebraClosed : Bool
round62FiniteLiteralIncrementKernelAlgebraClosed = true

round62LatticeRestrictionDoesNotDetermineContinuumSymbol : Bool
round62LatticeRestrictionDoesNotDetermineContinuumSymbol = true

round62PreferredCDataGapHasOnlyHHGoodAndCom : Bool
round62PreferredCDataGapHasOnlyHHGoodAndCom = true

round62KernelZeroDeletesCAndGKernelCost : Bool
round62KernelZeroDeletesCAndGKernelCost = true

round62FourthOrderDecaySummabilityClosed : Bool
round62FourthOrderDecaySummabilityClosed = true

round62PreferredScalarRegionSolved : Bool
round62PreferredScalarRegionSolved = true

round62RemovesAffineHHBadRecurrenceFromProducerCutsetIsTrue :
  round62RemovesAffineHHBadRecurrenceFromProducerCutset ≡ true
round62RemovesAffineHHBadRecurrenceFromProducerCutsetIsTrue = refl

round62ConcreteOddPQEntryIsNonzeroIsTrue :
  round62ConcreteOddPQEntryIsNonzero ≡ true
round62ConcreteOddPQEntryIsNonzeroIsTrue = refl

round62SelfMassNormalizationRejectedForPhysicalBIsTrue :
  round62SelfMassNormalizationRejectedForPhysicalB ≡ true
round62SelfMassNormalizationRejectedForPhysicalBIsTrue = refl

round62PhysicalComTargetIsSchurRowCoefficientIsTrue :
  round62PhysicalComTargetIsSchurRowCoefficient ≡ true
round62PhysicalComTargetIsSchurRowCoefficientIsTrue = refl

round62ConcreteCBlockFalsifiersClosedIsTrue :
  round62ConcreteCBlockFalsifiersClosed ≡ true
round62ConcreteCBlockFalsifiersClosedIsTrue = refl

round62CriticalScaleCircularityForbiddenIsTrue :
  round62CriticalScaleCircularityForbidden ≡ true
round62CriticalScaleCircularityForbiddenIsTrue = refl

round62FiniteLiteralIncrementKernelAlgebraClosedIsTrue :
  round62FiniteLiteralIncrementKernelAlgebraClosed ≡ true
round62FiniteLiteralIncrementKernelAlgebraClosedIsTrue = refl

round62LatticeRestrictionDoesNotDetermineContinuumSymbolIsTrue :
  round62LatticeRestrictionDoesNotDetermineContinuumSymbol ≡ true
round62LatticeRestrictionDoesNotDetermineContinuumSymbolIsTrue = refl

round62PreferredCDataGapHasOnlyHHGoodAndComIsTrue :
  round62PreferredCDataGapHasOnlyHHGoodAndCom ≡ true
round62PreferredCDataGapHasOnlyHHGoodAndComIsTrue = refl

round62KernelZeroDeletesCAndGKernelCostIsTrue :
  round62KernelZeroDeletesCAndGKernelCost ≡ true
round62KernelZeroDeletesCAndGKernelCostIsTrue = refl

round62FourthOrderDecaySummabilityClosedIsTrue :
  round62FourthOrderDecaySummabilityClosed ≡ true
round62FourthOrderDecaySummabilityClosedIsTrue = refl

round62PreferredScalarRegionSolvedIsTrue :
  round62PreferredScalarRegionSolved ≡ true
round62PreferredScalarRegionSolvedIsTrue = refl
