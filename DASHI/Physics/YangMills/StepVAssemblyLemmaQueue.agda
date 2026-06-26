module DASHI.Physics.YangMills.StepVAssemblyLemmaQueue where

-- ── StepVAssemblyLemmaQueue ──────────────────────────────────────────
-- Proof-replacement lemma queue for Sprints 5 and 7.
-- Sprint 5: Step V KP assembly (Lemmas V.1, V.2, V.3).
-- Sprint 7: DLR-LSI / RG-Cauchy decomposition (Lemmas RG.1–RG.8).
--
-- These lemmas show the logical STRUCTURE of the proof, making clear
-- which inputs are postulated (analytic, external) and which are composed.
-- Internal composition lemmas that can be proved from the postulated inputs
-- are given explicit Agda term-level proofs; purely analytic/external facts
-- remain as named postulates with source annotations.
--
-- Dependency DAG (simplified):
--   P33a (link ellipticity, external)
--     └─► P33b (diameter domination, internal graph consequence)
--           └─► weightedActivityDecayBound (analytic, external Eriksson §8)
--                 └─► lemmaV-1 (admissible diameter decay, composed here)
--                       └─► lemmaV-2 (all-diameter KP, via counting + margin)
--                             └─► lemmaV-3 (Step V certificate)
--                                   ├─► lemmaRG-DLRLSIBranch (RG.1–RG.5)
--                                   └─► lemmaRG-CauchyBranch  (RG.6–RG.8)
--
-- clayYangMillsPromoted = false (invariant; see SUNPrimitives).

open import Agda.Builtin.Bool   using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base       using (ℕ)

open import DASHI.Geometry.Gauge.SUNPrimitives
  using (clayYangMillsPromoted)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.ArithmeticLemmaQueue as ArithmeticQueue
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as ADC

-- ── Step V abstract real-analysis helpers ────────────────────────────
--
-- expℝ-SV is a local alias for the real exponential, used only within
-- this file.  ≤ℝ-trans-SV and expDecayMonotone encapsulate the two
-- real-analysis moves in Lemma V.1.

postulate
  expℝ-SV    : ℝ → ℝ
  ≤ℝ-trans-SV : ∀ {a b c : ℝ} → a ≤ℝ b → b ≤ℝ c → a ≤ℝ c

-- ── Step V activity bounding ─────────────────────────────────────────

postulate
  -- Activity of a polymer X at RG scale k (the quantity |z_aniso(X)|).
  zAniso : ℕ → ADC.Polymer → ℝ

  -- Bounding constant C appearing in the weighted decay estimate.
  stepVConstant : ℝ

  -- (P33a re-import) Uniform link ellipticity: every edge in every
  -- polymer at every scale satisfies m_link ≤ w_weight.
  -- Source: Balaban/Eriksson small-field regularity (external analytic claim).
  uniformLinkEllipticityHolds
    : ∀ (k : ℕ) (X : ADC.Polymer) (e : ADC.Edge)
    → ADC.isEdgeOf e k X
    → ADC.m-link ≤ℝ ADC.w-weight k e

  -- (P33a re-import) m_link ≥ 1.
  -- Source: DASHI A2 convention (external normalisation).
  mLinkGeOne : 1ℝ ≤ℝ ADC.m-link

  -- (P33b, internal graph consequence, re-imported here for module
  -- independence) Diameter domination from link ellipticity.
  -- Proof pattern: P01/P02/P03 + P33a → diam ≤ d-weighted.
  -- See BalabanAnisotropicDiameterCompatibility for the full derivation.
  diameterDominationFromEllipticity
    : ∀ (k : ℕ) (X : ADC.Polymer)
    → (∀ (e : ADC.Edge) → ADC.isEdgeOf e k X → ADC.m-link ≤ℝ ADC.w-weight k e)
    → 1ℝ ≤ℝ ADC.m-link
    → ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X

  -- (External, Eriksson Step V Thm 8.5)
  -- Weighted activity decay: |z_aniso(X)| ≤ C * exp(-d_k^w(X)).
  weightedActivityDecayBound
    : ∀ (k : ℕ) (X : ADC.Polymer)
    → zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ ADC.d-weighted k X))

  -- (External, real-analysis monotonicity)
  -- exp is antitone and multiplication by a nonneg constant is monotone:
  -- diam ≤ d-weighted → C*exp(-d-weighted) ≤ C*exp(-diam).
  expDecayMonotone
    : ∀ (k : ℕ) (X : ADC.Polymer)
    → ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X
    → (stepVConstant *ℝ expℝ-SV (-ℝ ADC.d-weighted k X))
      ≤ℝ
      (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X))

-- ── Lemma V.1: P33b gives admissible ordinary-diameter decay ─────────
--
-- Given P33b (diameter domination: diam ≤ d-weighted) and the external
-- weighted decay bound, compose via ≤ℝ-transitivity to obtain:
--
--   |z_aniso(X)| ≤ C * exp(-diam_k(X))
--
-- This is the key step that passes from the *weighted* distance (on
-- which the analytic bound is established) to the *ordinary* diameter
-- (which drives the KP counting argument).
--
-- Source: Eriksson 2602.0091 §2, combining Thm 8.5 of 2602.0056
-- with the P33b graph consequence.

lemmaV-1-P33bGivesAdmissibleDiameterDecay
  : ∀ (k : ℕ) (X : ADC.Polymer)
  → ADC.diam-ordinary k X ≤ℝ ADC.d-weighted k X
  → zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X))
lemmaV-1-P33bGivesAdmissibleDiameterDecay k X diamDom =
  ≤ℝ-trans-SV
    (weightedActivityDecayBound k X)
    (expDecayMonotone k X diamDom)

-- ── Step V spatial KP certificate (abstract) ─────────────────────────

stepVArithmeticQueue : ArithmeticQueue.ArithmeticLemmaQueueBundle
stepVArithmeticQueue = ArithmeticQueue.currentArithmeticLemmaQueueBundle

stepVKPSummability :
  ArithmeticQueue.ArithmeticLemmaQueueBundle.kpSummable stepVArithmeticQueue
stepVKPSummability =
  ArithmeticQueue.ArithmeticLemmaQueueBundle.kpSummable
    stepVArithmeticQueue

stepVMarginClosure :
  ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed stepVArithmeticQueue
stepVMarginClosure =
  ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed
    stepVArithmeticQueue

postulate
  -- Abstract KP certificate type.  The concrete version is assembled
  -- in BalabanStepVSpatialKPCertificate; we use an abstract copy here
  -- to keep this file self-contained and lightweight.
  StepVSpatialKPCertificate : Set

  -- (P06, external) Animal counting bound at scale k.
  -- Source: Eriksson 2602.0056 (polymer animal counting lemma).
  animalCountingBound : ∀ (k : ℕ) → ℝ

  -- Assembler: ordinary-diameter decay + counting + summability margin
  -- → Step V spatial KP certificate.
  -- Source: Eriksson 2602.0091 Thm 1.1 + internal margin arithmetic.
  lemmaV-2-allDiameterKPFromEntropyMargin
    : (∀ (k : ℕ) (X : ADC.Polymer)
       → zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X)))
    → StepVSpatialKPCertificate

-- ── Lemma V.3a: Step V from any ordinary-diameter decay bound ────────
--
-- If we can supply a proof that the activity decays with ordinary
-- diameter, the assembler (Lemma V.2) closes the KP certificate.
-- This is the compositional bridge: any proof of ordinary-diameter
-- decay is sufficient, regardless of how it was obtained.

lemmaV-3a-stepVFromOrdinaryDecayBound
  : (∀ (k : ℕ) (X : ADC.Polymer)
     → zAniso k X ≤ℝ (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X)))
  → StepVSpatialKPCertificate
lemmaV-3a-stepVFromOrdinaryDecayBound ordinaryDecay =
  lemmaV-2-allDiameterKPFromEntropyMargin ordinaryDecay

-- ── Lemma V.3b: Step V from P33a + weighted decay (specific path) ────
--
-- Instantiate the general Lemma V.3a using the specific path:
--   P33a (uniform link ellipticity, external)
--   → P33b (diameter domination, internal)
--   → Lemma V.1 (admissible diameter decay, composed)
--   → Lemma V.2 (KP certificate assembler)
--
-- This is the canonical path to Step V from the source inputs.

lemmaV-3b-fromP33aAndWeightedDecay : StepVSpatialKPCertificate
lemmaV-3b-fromP33aAndWeightedDecay =
  lemmaV-3a-stepVFromOrdinaryDecayBound
    (λ k X →
      lemmaV-1-P33bGivesAdmissibleDiameterDecay k X
        (diameterDominationFromEllipticity k X
          (uniformLinkEllipticityHolds k X)
          mLinkGeOne))

-- ── Sprint 7: DLR-LSI / RG-Cauchy decomposition ─────────────────────
--
-- The RG lane consumes the Step V certificate through two parallel
-- branches sourced from Eriksson 2602.0052 (DLR-LSI) and 2602.0072
-- (RG-Cauchy).
--
-- DLR-LSI branch (RG.1–RG.5):
--   RG.1  polymer decay → δₖ smallness (Lem. 6.3)
--   RG.2  cross-scale influence summable (Lem. 5.7)
--   RG.3  δₖ smallness → uniform LSI (Thm. 7.1)
--   RG.4  uniform LSI → exponential clustering (Thm. 7.1)
--   RG.5  LSI → lattice spectral gap (Cor. 7.3)
--
-- RG-Cauchy branch (RG.6–RG.8):
--   RG.6  Step V KP → Assumption A2 (2602.0072 A2)
--   RG.7  A2 → B6 influence bound (Thm. 1.3)
--   RG.8  B6 → RG-Cauchy summability (Cor. 5.1)

-- ── RG lane abstract types ───────────────────────────────────────────

postulate
  -- DLR interaction matrix coupling at scale k.
  δ-SV    : ℕ → ℝ
  -- Block parameter (α_{blk}/4 bound).
  αblk-SV : ℝ
  -- Log-Sobolev / DLR-LSI constant.
  LSI-ρ   : ℝ
  -- Lattice-level spectral gap.
  Δ-latt  : ℝ
  -- Types for the three intermediate properties.
  HasDLRLSI-SV               : Set
  HasDSCompleteAnalyticity-SV : Set
  HasExponentialClustering-SV : Set
  -- Assumption A2 type.
  AssumptionA2-SV : Set
  -- B6 Efron-Stein influence seminorm bound type.
  B6InfluenceBound-SV : Set
  -- RG-Cauchy convergence type.
  RGCauchySummability-SV : Set
  -- Cross-scale influence summability type.
  CrossScaleInfluenceSummable-SV : Set

-- ── RG.1: Polymer decay implies DLR smallness ────────────────────────
--
-- The Step V KP certificate guarantees that polymer activities decay
-- fast enough that the DLR coupling satisfies δₖ < αblk/4.
-- Source: Eriksson 2602.0052 Lemma 6.3.
postulate
  lemmaRG-1-polymerDecayImpliesDLRSmallness
    : StepVSpatialKPCertificate
    → ∀ (k : ℕ) → δ-SV k <ℝ αblk-SV

-- ── RG.2: Cross-scale influence is summable ──────────────────────────
--
-- The Step V certificate also ensures the cross-scale influence
-- sequence is summable (needed for the DLR-LSI induction).
-- Source: Eriksson 2602.0052 Lemma 5.7.
postulate
  lemmaRG-2-crossScaleInfluenceSummable
    : StepVSpatialKPCertificate
    → CrossScaleInfluenceSummable-SV

-- ── RG.3: DLR smallness implies uniform LSI ──────────────────────────
--
-- Once δₖ < αblk/4 holds uniformly, the DLR-LSI theorem gives a
-- uniform log-Sobolev constant ρ > 0.
-- Source: Eriksson 2602.0052 Theorem 7.1.
postulate
  lemmaRG-3-DLRSmallnessImpliesLSI
    : (∀ (k : ℕ) → δ-SV k <ℝ αblk-SV)
    → 0ℝ <ℝ LSI-ρ

-- ── RG.4: Uniform LSI implies exponential clustering ─────────────────
--
-- The DLR-LSI → DS-complete-analyticity → exponential clustering chain.
-- Source: Eriksson 2602.0052 Theorem 7.1.
postulate
  lemmaRG-4-uniformLSIImpliesExpClustering
    : 0ℝ <ℝ LSI-ρ
    → HasExponentialClustering-SV

-- ── RG.5: LSI implies positive lattice spectral gap ──────────────────
--
-- Exponential clustering (via LSI) gives a positive lattice spectral gap.
-- Source: Eriksson 2602.0052 Corollary 7.3.
postulate
  lemmaRG-5-LSIImpliesLatticeSpectralGap
    : 0ℝ <ℝ LSI-ρ
    → 0ℝ <ℝ Δ-latt

-- ── RG.6: A2 follows from the KP certificate ─────────────────────────
--
-- The per-link oscillation bound (Assumption A2) is guaranteed by the
-- Step V KP certificate with 2^{-2k} decay.
-- Source: Eriksson 2602.0072 Assumption A2.
postulate
  lemmaRG-6-A2FromKPCertificate
    : StepVSpatialKPCertificate
    → AssumptionA2-SV

-- ── RG.7: A2 implies the B6 influence seminorm bound ─────────────────
--
-- The B6 Efron-Stein influence bound follows from A2.
-- Source: Eriksson 2602.0072 Theorem 1.3.
postulate
  lemmaRG-7-A2ImpliesB6InfluenceBound
    : AssumptionA2-SV
    → B6InfluenceBound-SV

-- ── RG.8: B6 implies RG-Cauchy summability ───────────────────────────
--
-- The influence bound gives Σ_k δ_k < ∞, so blocked observables form a
-- Cauchy sequence and converge.
-- Source: Eriksson 2602.0072 Corollary 5.1.
postulate
  lemmaRG-8-B6ImpliesRGCauchy
    : B6InfluenceBound-SV
    → RGCauchySummability-SV

-- ── RG-lane composed branches ────────────────────────────────────────
--
-- Both RG branches are composed from the postulated lemmas above.
-- These compositions are internal Agda term-level proofs (not postulates).

-- DLR-LSI branch: Step V → exponential clustering (RG.1 → RG.2 → RG.3 → RG.4)
lemmaRG-DLRLSIBranch
  : StepVSpatialKPCertificate
  → HasExponentialClustering-SV
lemmaRG-DLRLSIBranch stepV =
  lemmaRG-4-uniformLSIImpliesExpClustering
    (lemmaRG-3-DLRSmallnessImpliesLSI
      (lemmaRG-1-polymerDecayImpliesDLRSmallness stepV))

-- RG-Cauchy branch: Step V → RG-Cauchy summability (RG.6 → RG.7 → RG.8)
lemmaRG-CauchyBranch
  : StepVSpatialKPCertificate
  → RGCauchySummability-SV
lemmaRG-CauchyBranch stepV =
  lemmaRG-8-B6ImpliesRGCauchy
    (lemmaRG-7-A2ImpliesB6InfluenceBound
      (lemmaRG-6-A2FromKPCertificate stepV))

-- Full DLR branch also yields the lattice spectral gap
lemmaRG-DLRLatticeGap
  : StepVSpatialKPCertificate
  → 0ℝ <ℝ Δ-latt
lemmaRG-DLRLatticeGap stepV =
  lemmaRG-5-LSIImpliesLatticeSpectralGap
    (lemmaRG-3-DLRSmallnessImpliesLSI
      (lemmaRG-1-polymerDecayImpliesDLRSmallness stepV))

-- ── Step V + RG assembly bundle ──────────────────────────────────────
--
-- Packages the full Sprint 5 + Sprint 7 output as a single typed record.
-- The record carries:
--   • The Step V certificate (via Lemma V.3b)
--   • Exponential clustering (DLR-LSI branch)
--   • RG-Cauchy summability (RG-Cauchy branch)
--   • Positive lattice spectral gap
--   • A canonical proof-structure string (checked by refl)
--   • The noClayPromotion invariant guard

record StepVRGAssemblyBundle : Set where
  field
    -- Step V certificate, assembled via P33a/P33b + weighted decay.
    stepVCertificate : StepVSpatialKPCertificate
    -- DLR-LSI branch: exponential clustering.
    expClustering    : HasExponentialClustering-SV
    -- RG-Cauchy branch: Cauchy summability.
    rgCauchy         : RGCauchySummability-SV
    -- Lattice spectral gap (positive).
    spectralGap      : 0ℝ <ℝ Δ-latt
    -- Proof-structure annotation (checked by refl below).
    proofStructure   : String
    proofStructureIsCanonical
      : proofStructure
        ≡ "Sprint 5: Step V assembled from P33b (diameter domination) + P06/P10/P11 (external analytic). Sprint 7: RG DLR-LSI branch (RG.1-RG.5) and RG-Cauchy branch (RG.6-RG.8) composed from Step V certificate. Internal composition lemmas are proved; analytic/external inputs remain postulated."
    -- Invariant guard: Clay promotion is not claimed here.
    noClayPromotion  : clayYangMillsPromoted ≡ false

currentStepVRGAssemblyBundle : StepVRGAssemblyBundle
currentStepVRGAssemblyBundle = record
  { stepVCertificate =
      lemmaV-3b-fromP33aAndWeightedDecay
  ; expClustering =
      lemmaRG-DLRLSIBranch lemmaV-3b-fromP33aAndWeightedDecay
  ; rgCauchy =
      lemmaRG-CauchyBranch lemmaV-3b-fromP33aAndWeightedDecay
  ; spectralGap =
      lemmaRG-DLRLatticeGap lemmaV-3b-fromP33aAndWeightedDecay
  ; proofStructure =
      "Sprint 5: Step V assembled from P33b (diameter domination) + P06/P10/P11 (external analytic). Sprint 7: RG DLR-LSI branch (RG.1-RG.5) and RG-Cauchy branch (RG.6-RG.8) composed from Step V certificate. Internal composition lemmas are proved; analytic/external inputs remain postulated."
  ; proofStructureIsCanonical = refl
  ; noClayPromotion = refl
  }
