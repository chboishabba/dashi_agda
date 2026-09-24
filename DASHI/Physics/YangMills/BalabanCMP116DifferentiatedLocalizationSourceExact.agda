{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact where

------------------------------------------------------------------------
-- ROUND84: CMP116 ANALYTIC LOCALIZATION SURVIVES SOURCE/FIELD DIFFERENTIATION
--
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. II.
-- Cluster Expansions", Communications in Mathematical Physics 116(1) (1988),
-- 1--22. DOI: 10.1007/BF01239022.
--
-- SOURCE LOCATOR
--
-- Sect. 1 begins with localized functions E(X,U,J,A) analytic in U,J,A and
-- constructs decoupled propagators/backgrounds analytic in the complex
-- parameters s(Y).  Around (1.18)--(1.21) the substituted background remains
-- analytic with bounds uniform on the declared U,J domain.  The source then
-- states explicitly that it differentiates the localized expansion and
-- represents derivatives by the Cauchy formula, leading to (1.23).  The summed
-- bound (1.29) retains a positive exponential tree-distance factor.  Lemma 1,
-- (1.33)--(1.36), packages localized analytic terms with the exponential bound.
--
-- MATHEMATICAL CONSEQUENCE
--
-- On the source's common complex domain, taking a finite number of declared
-- field/source derivatives does not require a NEW localization theorem.  Cauchy
-- estimates cost inverse powers of the available analytic radii, while the
-- already-produced spatial/tree exponential survives.  The radii/constants must
-- of course be uniform on the physical cutoff family used by the Clay route.
--
-- IMPORTANT AUTHORITY REPAIR
--
-- Historically this owner exposed only `ProofLevel = standardImported`.  The
-- proof-search route now needs a proof-bearing SOURCE STATEMENT surface so that
-- source theorem possession and selected-T5 applicability cannot be conflated.
-- The record below is deliberately weaker than a DASHI rooted-shell theorem:
-- it retains an abstract source envelope.  Identifying/calibrating that envelope
-- with the selected physical shell remains an application/same-object payment.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.List.Base using (List)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanDecoupledActivityHessian
import DASHI.Physics.YangMills.BalabanSharedMarkedAnalyticShellExact

------------------------------------------------------------------------
-- Proof-bearing source theorem shape.
------------------------------------------------------------------------

record PublishedCMP116DifferentiatedLocalization
    (Scale Volume Root SourceDirection Bound : Set) : Set₁ where
  field
    LessEqual : Bound → Bound → Set

    -- Source-native declared common analytic domain for the selected pair.
    AdmissibleSourcePair :
      Scale → Volume → SourceDirection → SourceDirection → Set

    -- The differentiated localized response and its source-native geometry.
    differentiatedMagnitude :
      Scale → Volume → SourceDirection → SourceDirection → Bound
    sourceRoot :
      Scale → Volume → SourceDirection → SourceDirection → Root
    sourceDistance : SourceDirection → SourceDirection → Nat

    -- The source theorem supplies an independently spatial/tree-decaying
    -- envelope.  It is intentionally NOT definitionally identified with the
    -- repository's configured rooted-shell function.
    sourceEnvelope : Scale → Volume → Root → Nat → Bound

    SourceEnvelopeHasPositiveExponentialTreeDecay : Set
    sourceEnvelopeHasPositiveExponentialTreeDecay :
      SourceEnvelopeHasPositiveExponentialTreeDecay

    -- Source theorem on the declared common analytic domain.  An inhabitant is
    -- an imported/source-aligned theorem payment, not a citation string.
    differentiatedLocalization :
      ∀ scale volume left right →
      AdmissibleSourcePair scale volume left right →
      LessEqual
        (differentiatedMagnitude scale volume left right)
        (sourceEnvelope scale volume
          (sourceRoot scale volume left right)
          (sourceDistance left right))

open PublishedCMP116DifferentiatedLocalization public

-- This projection is intentionally trivial: it demonstrates that downstream
-- consumers can demand the actual source theorem term rather than a ProofLevel
-- label or bibliographic coordinate.
sourceDifferentiatedLocalization :
  ∀ {Scale Volume Root SourceDirection Bound}
    (source : PublishedCMP116DifferentiatedLocalization
      Scale Volume Root SourceDirection Bound) →
  ∀ scale volume left right →
  AdmissibleSourcePair source scale volume left right →
  LessEqual source
    (differentiatedMagnitude source scale volume left right)
    (sourceEnvelope source scale volume
      (sourceRoot source scale volume left right)
      (sourceDistance source left right))
sourceDifferentiatedLocalization source = differentiatedLocalization source

------------------------------------------------------------------------
-- Proof-bearing CMP116 (1.26)--(1.29) fixed-Y/counting theorem shape.
--
-- (1.26) is the localization-domain tree-length summability estimate.
-- (1.28) absorbs the D_0 multiplicity by a polynomial-in-d_k(Y) factor.
-- (1.29) is the resulting fixed-Y differentiated sum with a still-positive
-- exp(-kappa_1 d_k(Y)/2) factor.  We expose the mathematically relevant
-- rate-split consequence rather than OCR-dependent constants.
------------------------------------------------------------------------

record PublishedCMP116Equation126129RateSplit
    (Domain : Set) : Set₁ where
  field
    localizedDomains : List Domain
    sourceTreeDistance : Domain → Nat

    sourcePrefactor : ℝ
    sourcePrefactorNonnegative : 0ℝ ≤ℝ sourcePrefactor

    -- Entropy/counting share of the retained localization decay and the
    -- residual physical share.  CMP116's displayed 1/2 in (1.29) permits a
    -- further positive split; the precise numerical split is application data.
    entropyHalfWeight residualDecayWeight : Nat → ℝ
    entropyHalfWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ entropyHalfWeight depth
    residualDecayWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ residualDecayWeight depth
    residualDecayWeightAntitone :
      ∀ {smaller larger} →
      Nat._≤_ smaller larger →
      residualDecayWeight larger ≤ℝ residualDecayWeight smaller

    entropyAllowance : ℝ

    -- Literal fixed-Y content of (1.29), after the source's counting losses
    -- (1.26)--(1.28) and a positive decay split.
    fixedYShell : Domain → ℝ
    fixedYEquation129RateSplit :
      ∀ domain →
      fixedYShell domain
      ≤ℝ
      sourcePrefactor *ℝ
        (entropyHalfWeight (sourceTreeDistance domain)
         *ℝ residualDecayWeight (sourceTreeDistance domain))

    -- Literal outer tree/fibre content supplied by the (1.26)--(1.28)
    -- cluster-expansion counting step, on the same localization-domain family.
    equation126128WeightedFibreBudget :
      Resum.sumℝ
        (λ domain → entropyHalfWeight (sourceTreeDistance domain))
        localizedDomains
      ≤ℝ entropyAllowance

open PublishedCMP116Equation126129RateSplit public

cmp116Equation126129RateSplitAuthorityLevel : ProofLevel
cmp116Equation126129RateSplitAuthorityLevel = standardImported

------------------------------------------------------------------------
-- Source/status boundary.
------------------------------------------------------------------------

-- CMP116 Sect. 1 / (1.23)--(1.36): differentiated decoupled local activities
-- retain an exponentially localized analytic representation.
cmp116DifferentiatedActivityLocalizationLevel : ProofLevel
cmp116DifferentiatedActivityLocalizationLevel = standardImported

-- The proof-bearing record is the source theorem ABI.  This status records the
-- external/source authority of an inhabitant; defining the ABI does not create
-- such an inhabitant.
cmp116DifferentiatedLocalizationAuthorityLevel : ProofLevel
cmp116DifferentiatedLocalizationAuthorityLevel = standardImported

-- Standard several-complex-variable Cauchy estimate: a k-th derivative on a
-- smaller polydisc costs only the appropriate inverse-radius factor; it does not
-- erase an independent spatial/tree exponential majorant.
finitePolydiscCauchyDerivativePreservesExternalMajorantLevel : ProofLevel
finitePolydiscCauchyDerivativePreservesExternalMajorantLevel = standardImported

-- In-repo `BalabanDecoupledActivityHessian` already performs the exact generic
-- lift from a marked boundary comparison to the Cauchy coefficient/Hessian.
markedBoundaryToHessianCauchyLiftLevel : ProofLevel
markedBoundaryToHessianCauchyLiftLevel = machineChecked

-- The remaining physical L2 seam is narrower than "prove three decay theorems":
-- identify the literal beta-irrelevant-memory, physical-spatial Hessian and
-- composite-source marks with the source analytic coordinates, and prove the
-- required analytic radii/constants are positive and cutoff/volume/scale uniform
-- on the SAME admissible YM trajectory.
physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel : ProofLevel
physicalCMP116MarkedCoordinateAndUniformRadiusIdentificationLevel = conditional
