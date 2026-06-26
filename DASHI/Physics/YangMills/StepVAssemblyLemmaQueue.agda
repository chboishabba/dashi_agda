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
open import Data.List.Base      using (List; length)
open import Data.Nat.Base       using (ℕ; _≤_; _*_)

open import DASHI.Geometry.Gauge.SUNPrimitives
  using (clayYangMillsPromoted)
open import DASHI.Foundations.RealAnalysisAxioms
  using (ℝ; _≤ℝ_; _<ℝ_; 0ℝ; 1ℝ; _+ℝ_; _*ℝ_; -ℝ_)

import DASHI.Physics.YangMills.ArithmeticLemmaQueue as ArithmeticQueue
import DASHI.Physics.YangMills.BalabanAnisotropicDiameterCompatibility as ADC
import DASHI.Physics.YangMills.BalabanLargeFieldSuppression as LargeField
import DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy as Entropy

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

stepVP07Reducer :
  ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin
stepVP07Reducer =
  ArithmeticQueue.ArithmeticLemmaQueueBundle.p07Reducer
    stepVArithmeticQueue

stepVMarginClosure :
  ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed stepVArithmeticQueue
stepVMarginClosure =
  ArithmeticQueue.ArithmeticLemmaQueueBundle.marginClosed
    stepVArithmeticQueue

stepVP09Reducer :
  ArithmeticQueue.EntropyMarginFromDiameterConstant
stepVP09Reducer =
  ArithmeticQueue.ArithmeticLemmaQueueBundle.p09Reducer
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

  stepVAnalyticAssembler
    : (∀ (Polymer : Set)
         (diameter : Polymer → ℕ)
         (root : Polymer)
         (n : ℕ)
         (polymers : List Polymer) →
       length polymers ≤ (n * n))
    → (∀ (k : ℕ) (X-dist : ℝ) (R-val : ℝ)
       → R-val ≤ℝ
          (LargeField.expℝ (-ℝ (LargeField.p0 k))
           *ℝ LargeField.expℝ (-ℝ (LargeField.κ *ℝ X-dist))))
    → (∀ (k : ℕ)
       → (LargeField.d-dim -ℝ 1ℝ) *ℝ LargeField.logℝ LargeField.L-constant
         +ℝ LargeField.C-abs-const
         ≤ℝ (LargeField.c-abs *ℝ LargeField.p0 k))
    → (∀ (k : ℕ) (X : ADC.Polymer)
       → zAniso k X ≤ℝ
          (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X)))
    → ArithmeticQueue.Summable
        (λ n →
          ArithmeticQueue.powℝ ArithmeticQueue.animalCountRate n
          *ℝ
          ArithmeticQueue.powℝ ArithmeticQueue.activityDecayRate n)
    → (∀ (cDiam : ℝ)
       → 0ℝ ≤ℝ cDiam
       → cDiam ≤ℝ 1ℝ
       → (cDiam *ℝ ArithmeticQueue.fourQ-ℝ) <ℝ 1ℝ)
    → StepVSpatialKPCertificate

record StepVSourceAnalyticInputs : Set₁ where
  field
    p06AnimalCounting : Entropy.ImportedPolymerAnimalCountingBound
    p10LargeFieldActivity : LargeField.ImportedLargeFieldActivityBound
    p11AbsorptionCondition : LargeField.ImportedAbsorptionCondition
    p33aUniformLinkEllipticity : ADC.P33aUniformLinkEllipticityWrapper

record StepVInternalReducers : Set₁ where
  field
    p33bDiameterDomination :
      ADC.P33bWeightedTreeDistanceDominatesOrdinaryDiameter
    p07KPSummabilityReducer :
      ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin
    p09EntropyMarginReducer :
      ArithmeticQueue.EntropyMarginFromDiameterConstant

StepVMarginFromP33bAndArithmetic
  : Entropy.ImportedPolymerAnimalCountingBound
  → LargeField.ImportedLargeFieldActivityBound
  → LargeField.ImportedAbsorptionCondition
  → ADC.P33aUniformLinkEllipticityWrapper
  → ADC.P33bWeightedTreeDistanceDominatesOrdinaryDiameter
  → ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin
  → ArithmeticQueue.EntropyMarginFromDiameterConstant
  → StepVSpatialKPCertificate
StepVMarginFromP33bAndArithmetic p06 p10 p11 p33a p33b p07 p09 =
  stepVAnalyticAssembler
    (Entropy.ImportedPolymerAnimalCountingBound.countingBound p06)
    (LargeField.ImportedLargeFieldActivityBound.activityBound p10)
    (LargeField.ImportedAbsorptionCondition.absorptionInequality p11)
    (λ k X →
      lemmaV-1-P33bGivesAdmissibleDiameterDecay k X
        (ADC.P33bWeightedTreeDistanceDominatesOrdinaryDiameter.weightedDistanceDominatesDiameterProof
           p33b
           (ADC.P33aUniformLinkEllipticityWrapper.linkRegularityWitness p33a)
           k X))
    (ArithmeticQueue.KPSummabilityReducerFromAnimalDecayAndMargin.instantiatedReducer p07)
    (ArithmeticQueue.EntropyMarginFromDiameterConstant.marginTheorem p09)

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
-- The named mixed theorem `StepVMarginFromP33bAndArithmetic` is the
-- DASHI-owned reducer:
--   P06 + P10 + P11 + P33a  (analytic/source-side)
--   + P33b + P07 + P09      (internal graph/arithmetic reducers)
--   → StepVSpatialKPCertificate

lemmaV-3b-fromP33aAndWeightedDecay : StepVSpatialKPCertificate
lemmaV-3b-fromP33aAndWeightedDecay =
  StepVMarginFromP33bAndArithmetic
    Entropy.polymerAnimalCountingBoundWitness
    LargeField.postulatedLargeFieldActivityBoundWitness
    LargeField.postulatedAbsorptionConditionWitness
    ADC.currentP33aUniformLinkEllipticityWrapper
    ADC.currentP33bWeightedTreeDistanceDominatesOrdinaryDiameter
    stepVP07Reducer
    stepVP09Reducer

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

record StepVPolymerDecayCertificate : Set where
  field
    stepVCertificate :
      StepVSpatialKPCertificate
    ordinaryDiameterDecay :
      ∀ (k : ℕ) (X : ADC.Polymer)
      → zAniso k X ≤ℝ
          (stepVConstant *ℝ expℝ-SV (-ℝ ADC.diam-ordinary k X))
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "Step V polymer-decay certificate: the mixed Step V reducer exposes ordinary-diameter decay as the consumable interface for RG/DLR handoff."

record StepVToDLRSmallness : Set where
  field
    polymerDecayCertificate : StepVPolymerDecayCertificate
    deltaSmallness :
      ∀ (k : ℕ) → δ-SV k <ℝ αblk-SV
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "StepVToDLRSmallness: StepVSpatialKPCertificate is first re-expressed as a polymer-decay certificate, then consumed by the DLR smallness inequality δ_k < α_blk."

record StepVToA2 : Set where
  field
    stepVCertificate :
      StepVSpatialKPCertificate
    assumptionA2Witness :
      AssumptionA2-SV
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "StepVToA2: the Step V spatial KP certificate is exposed as the exact oscillation/A2 input consumed by the RG-Cauchy lane."

record A2ToB6Influence : Set where
  field
    a2Witness : StepVToA2
    b6InfluenceWitness : B6InfluenceBound-SV
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "A2ToB6Influence: the Step V supplied A2 oscillation witness is consumed as the exact input to the B6 influence-bound theorem."

record B6ToRGCauchy : Set where
  field
    a2ToB6Witness : A2ToB6Influence
    rgCauchyWitness : RGCauchySummability-SV
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "B6ToRGCauchy: once the B6 influence profile is exposed, the RG-Cauchy lane consumes it as the exact summable increment witness."

record DLRSmallnessAndCrossScaleToUniformLSI : Set where
  field
    deltaSmallnessWitness : StepVToDLRSmallness
    crossScaleWitness : CrossScaleInfluenceSummable-SV
    uniformLSIWitness : 0ℝ <ℝ LSI-ρ
    proofBoundary : String
    proofBoundaryIsCanonical :
      proofBoundary
        ≡ "DLRSmallnessAndCrossScaleToUniformLSI: the Step V supplied DLR smallness witness and the cross-scale summability witness are consumed together as the exact inputs to the uniform LSI bridge."

lemmaRG-1a-stepVYieldsPolymerDecayCertificate
  : StepVSpatialKPCertificate
  → StepVPolymerDecayCertificate
lemmaRG-1a-stepVYieldsPolymerDecayCertificate stepV = record
  { stepVCertificate = stepV
  ; ordinaryDiameterDecay =
      λ k X →
        lemmaV-1-P33bGivesAdmissibleDiameterDecay k X
          (diameterDominationFromEllipticity
             k X
             (uniformLinkEllipticityHolds k X)
             mLinkGeOne)
  ; proofBoundary =
      "Step V polymer-decay certificate: the mixed Step V reducer exposes ordinary-diameter decay as the consumable interface for RG/DLR handoff."
  ; proofBoundaryIsCanonical = refl
  }

lemmaRG-1b-polymerDecayCertificateImpliesDLRSmallness
  : StepVPolymerDecayCertificate
  → ∀ (k : ℕ) → δ-SV k <ℝ αblk-SV
lemmaRG-1b-polymerDecayCertificateImpliesDLRSmallness polymerDecay =
  lemmaRG-1-polymerDecayImpliesDLRSmallness
    (StepVPolymerDecayCertificate.stepVCertificate polymerDecay)

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

stepVToDLRSmallness
  : StepVSpatialKPCertificate
  → StepVToDLRSmallness
stepVToDLRSmallness stepV = record
  { polymerDecayCertificate =
      lemmaRG-1a-stepVYieldsPolymerDecayCertificate stepV
  ; deltaSmallness =
      lemmaRG-1b-polymerDecayCertificateImpliesDLRSmallness
        (lemmaRG-1a-stepVYieldsPolymerDecayCertificate stepV)
  ; proofBoundary =
      "StepVToDLRSmallness: StepVSpatialKPCertificate is first re-expressed as a polymer-decay certificate, then consumed by the DLR smallness inequality δ_k < α_blk."
  ; proofBoundaryIsCanonical = refl
  }

stepVToA2
  : StepVSpatialKPCertificate
  → StepVToA2
stepVToA2 stepV = record
  { stepVCertificate = stepV
  ; assumptionA2Witness = lemmaRG-6-A2FromKPCertificate stepV
  ; proofBoundary =
      "StepVToA2: the Step V spatial KP certificate is exposed as the exact oscillation/A2 input consumed by the RG-Cauchy lane."
  ; proofBoundaryIsCanonical = refl
  }

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

a2ToB6Influence
  : StepVSpatialKPCertificate
  → A2ToB6Influence
a2ToB6Influence stepV = record
  { a2Witness = stepVToA2 stepV
  ; b6InfluenceWitness =
      lemmaRG-7-A2ImpliesB6InfluenceBound
        (StepVToA2.assumptionA2Witness (stepVToA2 stepV))
  ; proofBoundary =
      "A2ToB6Influence: the Step V supplied A2 oscillation witness is consumed as the exact input to the B6 influence-bound theorem."
  ; proofBoundaryIsCanonical = refl
  }

b6ToRGCauchy
  : StepVSpatialKPCertificate
  → B6ToRGCauchy
b6ToRGCauchy stepV = record
  { a2ToB6Witness = a2ToB6Influence stepV
  ; rgCauchyWitness =
      lemmaRG-8-B6ImpliesRGCauchy
        (A2ToB6Influence.b6InfluenceWitness (a2ToB6Influence stepV))
  ; proofBoundary =
      "B6ToRGCauchy: once the B6 influence profile is exposed, the RG-Cauchy lane consumes it as the exact summable increment witness."
  ; proofBoundaryIsCanonical = refl
  }

dlrSmallnessAndCrossScaleToUniformLSI
  : StepVSpatialKPCertificate
  → DLRSmallnessAndCrossScaleToUniformLSI
dlrSmallnessAndCrossScaleToUniformLSI stepV = record
  { deltaSmallnessWitness = stepVToDLRSmallness stepV
  ; crossScaleWitness = lemmaRG-2-crossScaleInfluenceSummable stepV
  ; uniformLSIWitness =
      lemmaRG-3-DLRSmallnessImpliesLSI
        (StepVToDLRSmallness.deltaSmallness (stepVToDLRSmallness stepV))
  ; proofBoundary =
      "DLRSmallnessAndCrossScaleToUniformLSI: the Step V supplied DLR smallness witness and the cross-scale summability witness are consumed together as the exact inputs to the uniform LSI bridge."
  ; proofBoundaryIsCanonical = refl
  }

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
    (DLRSmallnessAndCrossScaleToUniformLSI.uniformLSIWitness
      (dlrSmallnessAndCrossScaleToUniformLSI stepV))

-- RG-Cauchy branch: Step V → RG-Cauchy summability (RG.6 → RG.7 → RG.8)
lemmaRG-CauchyBranch
  : StepVSpatialKPCertificate
  → RGCauchySummability-SV
lemmaRG-CauchyBranch stepV =
  B6ToRGCauchy.rgCauchyWitness
    (b6ToRGCauchy stepV)

-- Full DLR branch also yields the lattice spectral gap
lemmaRG-DLRLatticeGap
  : StepVSpatialKPCertificate
  → 0ℝ <ℝ Δ-latt
lemmaRG-DLRLatticeGap stepV =
  lemmaRG-5-LSIImpliesLatticeSpectralGap
    (DLRSmallnessAndCrossScaleToUniformLSI.uniformLSIWitness
      (dlrSmallnessAndCrossScaleToUniformLSI stepV))

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
        ≡ "Sprint 5: Step V assembled by StepVMarginFromP33bAndArithmetic, consuming P06/P10/P11/P33a as source inputs and P33b/P07/P09 as DASHI-owned reducers. Sprint 7: RG DLR-LSI branch factors through StepVToDLRSmallness and RG-Cauchy branch factors through StepVToA2 before the imported analytic lane continues. Internal composition lemmas are proved; analytic/external inputs remain postulated."
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
      "Sprint 5: Step V assembled by StepVMarginFromP33bAndArithmetic, consuming P06/P10/P11/P33a as source inputs and P33b/P07/P09 as DASHI-owned reducers. Sprint 7: RG DLR-LSI branch factors through StepVToDLRSmallness and RG-Cauchy branch factors through StepVToA2 before the imported analytic lane continues. Internal composition lemmas are proved; analytic/external inputs remain postulated."
  ; proofStructureIsCanonical = refl
  ; noClayPromotion = refl
  }

currentStepVToDLRSmallness : StepVToDLRSmallness
currentStepVToDLRSmallness =
  stepVToDLRSmallness lemmaV-3b-fromP33aAndWeightedDecay

currentStepVToA2 : StepVToA2
currentStepVToA2 =
  stepVToA2 lemmaV-3b-fromP33aAndWeightedDecay

currentA2ToB6Influence : A2ToB6Influence
currentA2ToB6Influence =
  a2ToB6Influence lemmaV-3b-fromP33aAndWeightedDecay

currentB6ToRGCauchy : B6ToRGCauchy
currentB6ToRGCauchy =
  b6ToRGCauchy lemmaV-3b-fromP33aAndWeightedDecay

currentDLRSmallnessAndCrossScaleToUniformLSI :
  DLRSmallnessAndCrossScaleToUniformLSI
currentDLRSmallnessAndCrossScaleToUniformLSI =
  dlrSmallnessAndCrossScaleToUniformLSI
    lemmaV-3b-fromP33aAndWeightedDecay
