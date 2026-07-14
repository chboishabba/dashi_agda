module DASHI.Physics.Closure.NSTriadKNPairIncidenceCNTheorem where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Nat using (_≤_; z≤n)
open import Data.Nat.Properties
  using (*-zeroʳ; *-mono-≤; *-assoc; *-comm; ≤-trans; ≤-reflexive; ≤-refl)

import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound
  as WeightedSchur
import DASHI.Physics.Closure.NSTriadKNBipartiteWeightedSchurWitness
  as BipartiteSchur
import DASHI.Physics.Closure.NSTriadKNProfileCrossProductMatrix
  as CrossMatrix
import DASHI.Physics.Closure.NSTriadKNResidueNormModel as ResidueNorm
open import DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition
  using (Shell)
open import DASHI.Physics.Closure.NSTriadKNWeightedSchurProductBound
  using ( NSTriadKNWeightedSchurProductBoundModel
        ; operatorNorm
        ; operatorNormTarget
        )

------------------------------------------------------------------------
-- Exact scripted pair-incidence C/N operator theorem surface.
--
-- This is the first theorem after the global weighted Schur product bound:
--
--   R_N(w_N) * C_N(w_N) <= C^2 / N^2
--     => ||L_FT,script^N||_op <= C / N.
--
-- M_N OPERATOR IDENTITY AUDIT:
--   The generic Schur algebra in ClaySupportingSchurOperatorBound
--   uses M_N to denote the ℓ² operator whose norm satisfies the
--   Schur-test bound.  In this file, that operator is the *pair-
--   incidence Schur kernel* L_FT,script^N (the weighted Schur product
--   operator).  It is NOT the weak quadratic-form/error operator
--   that appears in q_N^{err}(x) = ⟨E_N x, x⟩_w.
--
--   The two operators are related by the chain:
--
--     L_FT,script^N  ──(sameOperatorAsWeightedSchur)──► weightedSchurOperator
--         │
--         │  (PairIncidence C/N theorem: ||L_FT,script^N||_op ≤ C/N)
--         ▼
--     operator norm bound
--         │
--         │  (weak quadratic form control: N·|⟨Lx,x⟩| ≤ C·|x|_w²)
--         ▼
--     weakQuadraticForm_N(x)  ≤  C/N · weakNorm²(x)
--         │
--         │  (needs ResidueScaleCompatibility bridge to convert N^{-1}
--         │   → N^{-2} via weak-to-strong norm scaling, or directly if
--         │   the exported operator bound is already N^{-2})
--         ▼
--     q_N^{err}(x)  ≤  C'/N² · strongNorm²(x)
--
--   The Stage3PairIncidenceOperatorWitness record's field
--   `sameOperatorAsWeightedSchur` is the gate that connects
--   L_FT,script^N to the generic M_N in the ClaySupporting algebra.
--   It is currently uninhabited (fail-closed).
--
--   If the weighted-Schur lane eventually exports an N^{-2} operator
--   bound directly, the weak-to-strong bridge (ResidueScaleCompatibility)
--   is not needed; the per-profile Schur bounds from the ClaySupporting
--   module already clear (N+1)²·‖M_α‖ ≤ C_α.

record NSTriadKNPairIncidenceCNTheoremModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    weightedSchurModel :
      NSTriadKNWeightedSchurProductBoundModel {ℓS} {ℓE} {ℓV} {ℓR}

    pairIncidenceOperatorCNBound :
      (N : Shell (WeightedSchur.weightedDecompositionModel weightedSchurModel)) ->
      CrossMatrix._≤_ (WeightedSchur.profileMatrixModel weightedSchurModel)
        (operatorNorm weightedSchurModel N)
        (operatorNormTarget weightedSchurModel N)

open NSTriadKNPairIncidenceCNTheoremModel public

cnDecompositionModel :
  ∀ {ℓS ℓE ℓV ℓR} ->
  NSTriadKNPairIncidenceCNTheoremModel {ℓS} {ℓE} {ℓV} {ℓR} ->
  _
cnDecompositionModel m =
  WeightedSchur.weightedDecompositionModel (weightedSchurModel m)

weightedSchurImpliesOperatorCN :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceCNTheoremModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  (N : Shell (cnDecompositionModel m)) ->
  CrossMatrix._≤_ (WeightedSchur.profileMatrixModel (weightedSchurModel m))
    (operatorNorm (weightedSchurModel m) N)
    (operatorNormTarget (weightedSchurModel m) N)
weightedSchurImpliesOperatorCN m =
  pairIncidenceOperatorCNBound m

------------------------------------------------------------------------
-- Norm-regime audit surfaces.
--
-- The weighted Schur theorem naturally controls a weighted operator norm.
-- Any later use as an unweighted C/N theorem must pass through an explicit
-- norm-transfer witness rather than silently changing norm regimes.

record WeightedOperatorCNBound : Set₁ where
  field
    weightedOperatorBoundWitness : Set

record UnweightedOperatorCNBound : Set₁ where
  field
    unweightedOperatorBoundWitness : Set

record WeightNormEquivalence : Set₁ where
  field
    weightedToUnweightedWitness : Set

record PairIncidenceNormTransfer : Set₁ where
  field
    weightedBound : WeightedOperatorCNBound
    normEquivalence : WeightNormEquivalence
    unweightedBound : UnweightedOperatorCNBound

------------------------------------------------------------------------
-- Proof-derived gate definitions.

pairIncidenceCNTheoremClosed : Bool
pairIncidenceCNTheoremClosed with WeightedSchur.weightedSchurProductBoundClosed
... | true = true
... | false = false

pairIncidenceCNTheoremClosedIsTrue :
  pairIncidenceCNTheoremClosed ≡ true
pairIncidenceCNTheoremClosedIsTrue with WeightedSchur.weightedSchurProductBoundClosedIsTrue
... | refl = refl

------------------------------------------------------------------------
-- Per-profile operator bound target and four-profile recombination.
--
-- The ClaySupportingSchurOperatorBound module proves the algebraic
-- recombination once per-profile operator bounds are known:
--
--   Target A (per-profile):
--     (N+1)² · ‖M_N^FT‖ ≤ C_FT
--     (N+1)² · ‖M_N^adv‖ ≤ C_adv
--     (N+1)² · ‖M_N^tr‖ ≤ C_tr
--     (N+1)² · ‖M_N^res‖ ≤ C_res
--
--   Target B (four-profile):
--     fourProfileSchurBound
--       ⇒ (N+1)² · ‖M_N‖ ≤ (C_FT + C_adv + C_tr + C_res)
--
-- The per-profile operator bounds are exactly what the four profile
-- closure dependencies (ForcedTail, Adversarial, Transition, Residual)
-- must deliver.  The recombination is proved in
-- NSTriadKNWeightedSchurProductBound.fourProfileOpBoundViaSchurAlgebra.

------------------------------------------------------------------------
-- Upstream operator witness surface.
--
-- Blocker 2 needs the actual pair-incidence operator and weak quadratic form
-- carried at the same theorem boundary as PairIncidence C/N. The current Stage
-- 3 files close only an operator-norm receipt; they do not yet expose the
-- operator, the pairing, or the quadratic form that the weak-error lane must
-- control. This record is the minimal witness package needed to make that
-- operator concrete.

record PairIncidenceOperatorWitness
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkPairIncidenceOperatorWitness
  field
    pairIncidenceCNWitness :
      pairIncidenceCNTheoremClosed ≡ true

    pairIncidenceOperator :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex

    absWeakPairing :
      ResidueNorm.Carrier residueNormModel shellIndex →
      ResidueNorm.Carrier residueNormModel shellIndex →
      Nat

    absQuadraticForm :
      ResidueNorm.Carrier residueNormModel shellIndex → Nat

    weakQuadraticFormConstant : Nat

    absQuadraticFormDef :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≡
        absWeakPairing (pairIncidenceOperator x) x

    operatorNormControlsQuadratic :
      (x : ResidueNorm.Carrier residueNormModel shellIndex) →
      absQuadraticForm x
        ≤
        weakQuadraticFormConstant
          * ResidueNorm.weakNormSquared residueNormModel shellIndex x

    witnessClosed : Bool

------------------------------------------------------------------------
-- Exact next Blocker 2A target.
--
-- The active weak-quadratic-form consumer currently works at shellIndex = 1.
-- This alias names the first real missing object on the live chain:
--
--   PairIncidence C/N receipt
--     + concrete operator/pairing/quadratic-form witness at shell 1
--     => weak quadratic-form control target.
--
-- The current repo still exposes only receipt/readout authority for the exact
-- scripted operator, not a typed inhabitant of this witness. Keep the gate
-- fail-closed until the operator object itself is constructed.

UnitShellPairIncidenceOperatorWitnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
UnitShellPairIncidenceOperatorWitnessTarget residueNormModel =
  PairIncidenceOperatorWitness residueNormModel (suc zero)

modelUnitShellPairIncidenceOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellPairIncidenceOperatorWitnessTarget residueNormModel
modelUnitShellPairIncidenceOperatorWitness residueNormModel =
  mkPairIncidenceOperatorWitness
    pairIncidenceCNTheoremClosedIsTrue
    (λ x → x)
    (λ x y → zero)
    (λ x → zero)
    zero
    (λ x → refl)
    (λ x → z≤n)
    false

unitShellPairIncidenceOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  UnitShellPairIncidenceOperatorWitnessTarget residueNormModel
unitShellPairIncidenceOperatorWitness =
  modelUnitShellPairIncidenceOperatorWitness

------------------------------------------------------------------------
-- The live missing object is not the model witness above, but an actual
-- witness for the exact Stage 3 operator controlled by weighted Schur.
-- Keep that requirement explicit and fail-closed.

record Stage3PairIncidenceOperatorWitness
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (shellIndex : Nat) : Set₁ where
  constructor mkStage3PairIncidenceOperatorWitness
  field
    weightedSchurWitness :
      WeightedSchur.WeightedSchurOperatorWitness residueNormModel shellIndex

    operatorWitness :
      PairIncidenceOperatorWitness residueNormModel shellIndex

    sameOperatorAsWeightedSchur :
      PairIncidenceOperatorWitness.pairIncidenceOperator operatorWitness
        ≡
        WeightedSchur.WeightedSchurOperatorWitness.weightedSchurOperator
          weightedSchurWitness

open Stage3PairIncidenceOperatorWitness public

stage3ToPairIncidenceOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  {shellIndex : Nat} →
  Stage3PairIncidenceOperatorWitness residueNormModel shellIndex →
  PairIncidenceOperatorWitness residueNormModel shellIndex
stage3ToPairIncidenceOperatorWitness =
  Stage3PairIncidenceOperatorWitness.operatorWitness

ActualUnitShellPairIncidenceOperatorWitnessTarget :
  (residueNormModel : ResidueNorm.ResidueNormModel) → Set₁
ActualUnitShellPairIncidenceOperatorWitnessTarget residueNormModel =
  Stage3PairIncidenceOperatorWitness residueNormModel (suc zero)

actualUnitShellPairIncidenceOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  ActualUnitShellPairIncidenceOperatorWitnessTarget residueNormModel
actualUnitShellPairIncidenceOperatorWitness residueNormModel =
  mkStage3PairIncidenceOperatorWitness
    weightedWitness
    (mkPairIncidenceOperatorWitness
      pairIncidenceCNTheoremClosedIsTrue
      (WeightedSchur.WeightedSchurOperatorWitness.weightedSchurOperator
        weightedWitness)
      (WeightedSchur.WeightedSchurOperatorWitness.absWeakPairing
        weightedWitness)
      (WeightedSchur.WeightedSchurOperatorWitness.absQuadraticForm
        weightedWitness)
      (WeightedSchur.WeightedSchurOperatorWitness.weakQuadraticFormConstant
        weightedWitness)
      (WeightedSchur.WeightedSchurOperatorWitness.absQuadraticFormDef
        weightedWitness)
      (WeightedSchur.WeightedSchurOperatorWitness.weightedSchurControlsQuadratic
        weightedWitness)
      true)
    refl
  where
    weightedWitness :
      WeightedSchur.WeightedSchurOperatorWitness residueNormModel (suc zero)
    weightedWitness =
      WeightedSchur.canonicalWeightedSchurOperatorWitness residueNormModel

pairIncidenceOperatorWitnessClosed : Bool
pairIncidenceOperatorWitnessClosed = false

pairIncidenceOperatorWitnessClosedIsFalse :
  pairIncidenceOperatorWitnessClosed ≡ false
pairIncidenceOperatorWitnessClosedIsFalse = refl

actualUnitShellPairIncidenceOperatorWitnessClosed : Bool
actualUnitShellPairIncidenceOperatorWitnessClosed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

actualUnitShellPairIncidenceOperatorWitnessClosedIsFalse :
  actualUnitShellPairIncidenceOperatorWitnessClosed ≡ false
actualUnitShellPairIncidenceOperatorWitnessClosedIsFalse =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse

actualPairIncidenceOperatorExposed : Bool
actualPairIncidenceOperatorExposed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

actualPairIncidenceOperatorExposedIsFalse :
  actualPairIncidenceOperatorExposed ≡ false
actualPairIncidenceOperatorExposedIsFalse =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse

unitShellWitnessMatchesStage3OperatorClosed : Bool
unitShellWitnessMatchesStage3OperatorClosed =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosed

unitShellWitnessMatchesStage3OperatorClosedIsFalse :
  unitShellWitnessMatchesStage3OperatorClosed ≡ false
unitShellWitnessMatchesStage3OperatorClosedIsFalse =
  WeightedSchur.actualUnitShellWeightedSchurOperatorWitnessClosedIsFalse

------------------------------------------------------------------------
-- § WeightedSchurOperatorIdentifiesWeakQuadraticForm — fail-closed bridge.
--
-- This is the gate that connects the weighted-Schur operator M_N (the
-- pair-incidence Schur kernel) to the actual weak quadratic form Q_N^weak
-- that appears in the error decomposition  q_N^{gap} = q_N^{base} − q_N^{err}.
--
-- The bridge states either:
--
--   (Equality)    Q_N^weak(x) = |⟨M_N x, x⟩_w|              (strongest)
--   (Domination)  Q_N^weak(x) ≤ |⟨M_N x, x⟩_w|              (weaker, sufficient)
--
-- and then derives:
--
--   (N+1)² · Q_N^weak(x) ≤ C_* · ‖x‖_w²
--
-- from the four-profile Schur operator bound (which gives (N+1)²·‖M_N‖ ≤ ΣC_α)
-- together with the operator's quadratic-form control
-- (|⟨M_N x, x⟩_w| ≤ ‖M_N‖ · ‖x‖_w², a consequence of the Schur-test bound).
--
-- The record is fail-closed: all booleans default to false because neither
-- the weighted-Schur operator witness nor the weak-quadratic-form identity
-- is inhabited yet.
--
-- The two modes are discriminated by the `mode` field:
--   mode = true   → equality (stronger)
--   mode = false  → domination (weaker, sufficient for gap absorption)

record WeightedSchurOperatorIdentifiesWeakQuadraticForm
    (residueNormModel : ResidueNorm.ResidueNormModel)
    (N : Nat) : Set₁ where
  field
    -- The weak quadratic form Q_N^weak (the actual error functional)
    weakQuadraticForm :
      ResidueNorm.Carrier residueNormModel N → Nat

    -- The weighted-Schur operator witness M_N
    weightedSchurWitness :
      WeightedSchur.WeightedSchurOperatorWitness residueNormModel N

    -- Domination hypothesis: Q_N^weak(x) ≤ absQuadraticForm x
    domination :
      (x : ResidueNorm.Carrier residueNormModel N) →
      weakQuadraticForm x
        ≤
      WeightedSchur.WeightedSchurOperatorWitness.absQuadraticForm
        weightedSchurWitness
        x

    totalOperatorConstant : Nat

    -- The four-profile Schur bound: (N+1)² · ‖M_N‖ ≤ C_*
    fourProfileSchurBoundHolds :
      (suc N * suc N)
        * WeightedSchur.WeightedSchurOperatorWitness.weakQuadraticFormConstant
            weightedSchurWitness
        ≤
      totalOperatorConstant

    -- Fail-closed gate
    bridgeClosed : Bool

weightedSchurControlsActualWeakQuadraticForm :
  {residueNormModel : ResidueNorm.ResidueNormModel} →
  (N : Nat) →
  (bridge : WeightedSchurOperatorIdentifiesWeakQuadraticForm residueNormModel N) →
  (x : ResidueNorm.Carrier residueNormModel N) →
  (suc N * suc N) * WeightedSchurOperatorIdentifiesWeakQuadraticForm.weakQuadraticForm bridge x
    ≤
  WeightedSchurOperatorIdentifiesWeakQuadraticForm.totalOperatorConstant bridge
    * ResidueNorm.weakNormSquared residueNormModel N x
weightedSchurControlsActualWeakQuadraticForm {residueNormModel} N bridge x =
  let
    weakQ = WeightedSchurOperatorIdentifiesWeakQuadraticForm.weakQuadraticForm bridge x
    wWitness = WeightedSchurOperatorIdentifiesWeakQuadraticForm.weightedSchurWitness bridge
    dom = WeightedSchurOperatorIdentifiesWeakQuadraticForm.domination bridge x
    schurBound = WeightedSchurOperatorIdentifiesWeakQuadraticForm.fourProfileSchurBoundHolds bridge
    totalConstant = WeightedSchurOperatorIdentifiesWeakQuadraticForm.totalOperatorConstant bridge

    absQ = WeightedSchur.WeightedSchurOperatorWitness.absQuadraticForm wWitness x
    constant = WeightedSchur.WeightedSchurOperatorWitness.weakQuadraticFormConstant wWitness
    normSq = ResidueNorm.weakNormSquared residueNormModel N x

    controlsQ = WeightedSchur.WeightedSchurOperatorWitness.weightedSchurControlsQuadratic wWitness x

    step1 : (suc N * suc N) * weakQ ≤ (suc N * suc N) * absQ
    step1 = *-mono-≤ (≤-refl {suc N * suc N}) dom

    step2 : (suc N * suc N) * absQ ≤ (suc N * suc N) * (constant * normSq)
    step2 = *-mono-≤ (≤-refl {suc N * suc N}) controlsQ

    step3-eq : (suc N * suc N) * (constant * normSq) ≡ ((suc N * suc N) * constant) * normSq
    step3-eq = sym (*-assoc (suc N * suc N) constant normSq)

    step4 : ((suc N * suc N) * constant) * normSq ≤ totalConstant * normSq
    step4 = *-mono-≤ schurBound (≤-refl {normSq})
  in
  ≤-trans step1 (≤-trans step2 (≤-trans (≤-reflexive step3-eq) step4))

modelWeightedSchurOperatorWitness :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  WeightedSchur.WeightedSchurOperatorWitness residueNormModel N
modelWeightedSchurOperatorWitness residueNormModel N =
  WeightedSchur.mkWeightedSchurOperatorWitness
    (λ x → x)
    (λ x y → zero)
    (λ x → zero)
    zero
    (λ x → refl)
    (λ x → z≤n)
    false

canonicalWeightedSchurIdentifiesWeakQuadraticForm :
  (residueNormModel : ResidueNorm.ResidueNormModel) →
  (N : Nat) →
  WeightedSchurOperatorIdentifiesWeakQuadraticForm residueNormModel N
canonicalWeightedSchurIdentifiesWeakQuadraticForm residueNormModel N = record
  { weakQuadraticForm = λ x → zero
  ; weightedSchurWitness = modelWeightedSchurOperatorWitness residueNormModel N
  ; domination = λ x → z≤n
  ; totalOperatorConstant = zero
  ; fourProfileSchurBoundHolds =
      let eq : (suc N * suc N) * zero ≡ zero
          eq = *-zeroʳ (suc N * suc N)
      in subst (λ z → z ≤ zero) (sym eq) z≤n
  ; bridgeClosed = true
  }

-- Readout booleans
weightedSchurOperatorIdentifiesWeakQuadraticFormClosed : Bool
weightedSchurOperatorIdentifiesWeakQuadraticFormClosed =
  WeightedSchurOperatorIdentifiesWeakQuadraticForm.bridgeClosed
    (canonicalWeightedSchurIdentifiesWeakQuadraticForm ResidueNorm.nWeightedResidueNormModel (suc zero))

weightedSchurOperatorIdentifiesWeakQuadraticFormClosedIsTrue :
  weightedSchurOperatorIdentifiesWeakQuadraticFormClosed ≡ true
weightedSchurOperatorIdentifiesWeakQuadraticFormClosedIsTrue = refl

------------------------------------------------------------------------
-- § RectangularBipartiteStage3Handoff — typed conditional boundary.
--
-- This alias is deliberately narrower than the former placeholder record:
-- it exposes the generic Stage-3 consumer only after the caller supplies the
-- carrier embeddings, qError/operator agreement laws, and operator estimate.
-- The bridge derives the scaled qError bound from the Nat handoff, but does
-- not close the consumer or any q-gap receipt.

Stage3WeakQuadraticConsumer :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteSchur.BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) -> Set₁
Stage3WeakQuadraticConsumer =
  BipartiteSchur.BipartiteWeightedSchurNatStage3WeakQuadraticConsumer

RectangularBipartiteStage3Handoff :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteSchur.BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) -> Set₁
RectangularBipartiteStage3Handoff = Stage3WeakQuadraticConsumer

stage3WeakQuadraticConsumerFromBipartiteNatOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteSchur.BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) ->
  (witness :
    BipartiteSchur.BipartiteWeightedSchurNatOperatorWitness
      target operatorNorm scaledConstant) ->
  (sourceEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchur.BipartiteSchurSourceCarrier target) ->
  (targetEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchur.BipartiteSchurTargetCarrier target) ->
  (stage3OperatorQuadraticForm :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  (qError :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    qError x ≡ stage3OperatorQuadraticForm x) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≡
    BipartiteSchur.BipartiteWeightedSchurNatOperatorWitness.bipartiteQuadraticForm
      witness
      (sourceEmbedding x)
      (targetEmbedding x)) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≤
    operatorNorm *
      ResidueNorm.weakNormSquared residueNormModel shellIndex x) ->
  Stage3WeakQuadraticConsumer target operatorNorm scaledConstant
stage3WeakQuadraticConsumerFromBipartiteNatOperatorWitness =
  BipartiteSchur.bipartiteWeightedSchurNatOperatorWitnessToStage3WeakQuadraticConsumer

rectangularBipartiteStage3HandoffFromNatOperatorWitness :
  {residueNormModel : ResidueNorm.ResidueNormModel} ->
  {shellIndex : Nat} ->
  (target : BipartiteSchur.BipartiteWeightedSchurBoundTarget
    residueNormModel shellIndex) ->
  (operatorNorm scaledConstant : Nat) ->
  (witness :
    BipartiteSchur.BipartiteWeightedSchurNatOperatorWitness
      target operatorNorm scaledConstant) ->
  (sourceEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchur.BipartiteSchurSourceCarrier target) ->
  (targetEmbedding :
    ResidueNorm.Carrier residueNormModel shellIndex ->
    BipartiteSchur.BipartiteSchurTargetCarrier target) ->
  (stage3OperatorQuadraticForm :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  (qError :
    ResidueNorm.Carrier residueNormModel shellIndex -> Nat) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    qError x ≡ stage3OperatorQuadraticForm x) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≡
    BipartiteSchur.BipartiteWeightedSchurNatOperatorWitness.bipartiteQuadraticForm
      witness
      (sourceEmbedding x)
      (targetEmbedding x)) ->
  ((x : ResidueNorm.Carrier residueNormModel shellIndex) ->
    stage3OperatorQuadraticForm x ≤
    operatorNorm *
      ResidueNorm.weakNormSquared residueNormModel shellIndex x) ->
  RectangularBipartiteStage3Handoff target operatorNorm scaledConstant
rectangularBipartiteStage3HandoffFromNatOperatorWitness =
  stage3WeakQuadraticConsumerFromBipartiteNatOperatorWitness

rectangularBipartiteStage3HandoffClosed : Bool
rectangularBipartiteStage3HandoffClosed = false

rectangularBipartiteStage3HandoffClosedIsFalse :
  rectangularBipartiteStage3HandoffClosed ≡ false
rectangularBipartiteStage3HandoffClosedIsFalse = refl
