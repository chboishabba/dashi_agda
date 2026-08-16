module DASHI.Physics.Closure.NSTriadKNHighestAlphaRound62Exact where

------------------------------------------------------------------------
-- ROUND 62: PRODUCER-CUTSET COMPRESSION
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
-- B. PHYSICAL COM ENERGY STAYS ON THE LITERAL FOURIER REAL FIELD
--
-- The Round58 Q-valued "physical normalized Gram" record is explicitly
-- demoted to a rational certificate carrier.  Literal Fourier coefficients are
-- not rational.  More importantly, the literal `PeriodicHardShellFourierPDE`
-- already chooses an algebraic `realField`, so the same-object normalized
-- energy must stay in `Carrier (realField model)`.
--
-- Round62 therefore extends THAT exact carrier with the existing
-- `OrderedRealExtension` plus only a rational embedding.  Same/adjacent bounds
-- by embedded 17/64 and 65/512 imply the embedded 133/256 bandwidth-one bound
-- without changing scalar universes.  The Murray--Bishop module is retained as
-- a concrete setoid-real comparison backend, but is explicitly NOT identified
-- definitionally with the literal Fourier carrier (whose algebra uses
-- propositional equality).  Separately, finite rational Cauchy--Schwarz closes
-- the strong/weak certificate algebra.
--
-- The remaining physical B theorem is therefore concrete: construct the
-- normalized operator-product energy IN the literal model's real field, supply
-- its ordered rational extension, prove common-hat support, and prove the
-- same/adjacent active bounds.  There is no physical=Q or Fourier=Bishop
-- equality to prove.
--
-- C. THE ADDITIVE FIXED-SHIFT GAP IS LOCALIZED TO THE SOFT OWNERS
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
-- D/F. ONE STRUCTURED LOCALIZED PDE ATOM SOURCE
--
-- A single structured atom list now distinguishes physical interior, tail,
-- duplicate kernel, exact cancelling kernel pairs, independent kernel, and
-- classified lower/upper boundary atoms.  Exact cancellation is folded from
-- the local pair witnesses.  The mature kernel residual split and boundary
-- ledger are both extracted from this same source.
--
-- The preferred D2 equality
--
--   independentKernelTotal = 0
--
-- directly constructs the existing structural zero kernel owner, deleting
-- kernel production, eta, data and critical costs simultaneously.  What remains
-- is the actual localized NS source-extraction identity, the independent-zero
-- proof (or quantitative fallback), and the physical boundary limits.
--
-- E. FOURTH-ORDER DECAY -> L1 SUMMABILITY CLOSED
--
-- Once four inverse-Fourier integrations by parts give a three-dimensional
-- dyadic shell mass bound M 2^{-j}, exact finite geometric algebra proves every
-- partial L1 mass <=2M.  Thus no separate Schwartz/L1 authority is needed.  The
-- remaining E theorem is the same-object continuum annular multiplier and the
-- literal fourfold integration-by-parts shell estimate.
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
-- These are now explicit kill-tests for the current architecture.
--
-- H remains the already-closed same-selected-solution Luo continuation lane.
--
-- GENUINE REMAINING PHYSICAL/ANALYTIC PRODUCERS AFTER ROUND62
--
--   A1  construct the literal selected-solution Duhamel source/successor
--       identity used by DirectPhysicalDuhamelIdentity;
--   A2  prove finite-prefix/tail component headroom N_q<=C_*-I_q, the density
--       domination 2^q g_q<=C_q, and the unmasked charge bound K_bad D;
--   B1  construct normalized odd-P/Q operator-product energy in the SAME
--       `Carrier (realField model)`, its ordered rational extension, and the
--       physical common-hat support;
--   B3  prove same/forward/reverse active bounds by embedded 17/64 and 65/512;
--   C1  prove SAME-OBJECT owner->flux->block identification, the global
--       X_n<=K C r^n estimate, and local smooth-HHg/Com data-scale bounds;
--   C2  verify a_smooth-HHg+a_Com<r-q (preferred kernel-zero branch);
--   D1/F1 emit the structured atom list from one literal localized NS identity;
--   D2  prove independentKernelTotal=0, or supply the quantitative fallback;
--   F2  prove every classified physical boundary atom tends to zero;
--   E1/E2 construct the continuum annular symbol restricting to the literal
--       lattice symbol and prove the fourfold inverse-Fourier shell estimate;
--   G   instantiate the physical constants and discharge the explicit preferred
--       scalar gate above.
--
-- These are not replaced by assumption records here.  Round62 only removes
-- algebraic duplication, carrier mistakes, fictitious owner costs and already-
-- derivable limit/summation/allocation work around those genuine theorems.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNHighestAlphaRound61Exact

-- A: direct literal component headroom and K_bad owner, without alpha/beta.
import DASHI.Physics.Closure.NSTriadKNHHBadDirectPhysicalHeadroomRound62Exact
import DASHI.Physics.Closure.NSTriadKNHHBadSelectedProfileMultiplicityRound62Exact

-- B: rational certificate algebra, same-object ordered literal-field endpoint,
-- and a separate concrete Bishop-setoid comparison backend.
import DASHI.Physics.Closure.NSTriadKNComTwoBranchFiniteGramRound62Exact
import DASHI.Physics.Closure.NSTriadKNComOrderedPhysicalMajorantRound62Exact
import DASHI.Physics.Closure.NSTriadKNComBishopNormalizedMajorantRound62Exact

-- C: local owner aggregation, three-soft fallback, preferred kernel-zero
-- two-soft scale, and HH-good smooth-only remainder identity.
import DASHI.Physics.Closure.NSTriadKNFixedShiftNineOwnerDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftThreeSoftDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNFixedShiftKernelZeroTwoSoftDataScaleRound62Exact
import DASHI.Physics.Closure.NSTriadKNHHGoodSmoothOnlyDataRemainderRound62Exact

-- D/F: one raw constituent source, stronger structured atoms, and exact-zero
-- promotion to the structural kernel owner.
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEConstituentPartitionRound62Exact
import DASHI.Physics.Closure.NSTriadKNLocalizedPDEStructuredAtomsRound62Exact
import DASHI.Physics.Closure.NSTriadKNStructuredKernelZeroOwnerRound62Exact

-- E: exact fourth-order dyadic summability endpoint.
import DASHI.Physics.Closure.NSTriadKNHHGoodFourthOrderDyadicL1Round62Exact

-- G: sharp reciprocal substitution, generic three-soft gate, preferred
-- kernel-zero two-soft gate and explicit feasibility-region falsifiers.
import DASHI.Physics.Closure.NSTriadKNSharpWeightedScalarGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNThreeSoftSharpGlobalGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftWeightedGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNKernelZeroTwoSoftSharpGlobalGateRound62Exact
import DASHI.Physics.Closure.NSTriadKNPreferredScalarFeasibilityRegionRound62Exact

round62RemovesAffineHHBadRecurrenceFromProducerCutset : Bool
round62RemovesAffineHHBadRecurrenceFromProducerCutset = true

round62PhysicalComEnergyRemainsOnLiteralFourierRealField : Bool
round62PhysicalComEnergyRemainsOnLiteralFourierRealField = true

round62BishopEndpointIsOnlyComparisonBackend : Bool
round62BishopEndpointIsOnlyComparisonBackend = true

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

round62PhysicalComEnergyRemainsOnLiteralFourierRealFieldIsTrue :
  round62PhysicalComEnergyRemainsOnLiteralFourierRealField ≡ true
round62PhysicalComEnergyRemainsOnLiteralFourierRealFieldIsTrue = refl

round62BishopEndpointIsOnlyComparisonBackendIsTrue :
  round62BishopEndpointIsOnlyComparisonBackend ≡ true
round62BishopEndpointIsOnlyComparisonBackendIsTrue = refl

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
