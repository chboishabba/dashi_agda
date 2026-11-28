module DASHI.Cognition.PNF.X369IndexedRecurrentResidualWeldExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- The full nine-trit hyperfabric is NOT the original floating recurrent state.
-- Retain native recurrent bytes/residual and typed history/time/refinement/
-- Frobenius/consumer version as independently governed indices.
-- Theorems are written to run; Agda kernel deliberately deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
import DASHI.Foundations.Base369Ternary27HypervoxelFabricGeometryExact as Fabric
import DASHI.Core.GovernedIndexedResidualCubeExact as Cube
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

module IndexedSource
  (History Time Depth Frobenius Version Residual : Set) where

  -- Reuse the exact canonical cube index, not an invented index product.
  Index : Set
  Index = Cube.Index History Time Depth Frobenius Version

  historyAt : Index → History
  historyAt = Cube.Index.history
  timeAt : Index → Time
  timeAt = Cube.Index.time
  depthAt : Index → Depth
  depthAt = Cube.Index.depth
  frobeniusAt : Index → Frobenius
  frobeniusAt = Cube.Index.iteration
  versionAt : Index → Version
  versionAt = Cube.Index.version

  Full : Set
  Full = Fabric.TernaryHyperformalPoint

  -- The original machine may have arbitrary recurrent states. The
  -- residual is not assumed finite nor is its byte identity erased.
  State : Set
  State = (Full × Residual) × Index

  chart : State → Full
  chart ((x , r) , k) = x

  residual : State → Residual
  residual ((x , r) , k) = r

  sourceIndex : State → Index
  sourceIndex ((x , r) , k) = k

  reopen : Full → Residual → Index → State
  reopen x r k = (x , r) , k

  reopenBidi : (s : State) →
    reopen (chart s) (residual s) (sourceIndex s) ≡ s
  reopenBidi ((x , r) , k) = refl

  splitBidi : (x : Full) (r : Residual) (k : Index) →
    chart (reopen x r k) ≡ x
  splitBidi x r k = refl

  residualBidi : (x : Full) (r : Residual) (k : Index) →
    residual (reopen x r k) ≡ r
  residualBidi x r k = refl

  indexBidi : (x : Full) (r : Residual) (k : Index) →
    sourceIndex (reopen x r k) ≡ k
  indexBidi x r k = refl

  -- For *any* proposed producer/consumer and any chart, the exact
  -- actual source-specific commuting squares are the only premises
  -- needed to derive all finite future-word observations.
  module FutureWeld {Input Code Output : Set}
    (step : Input → State → State)
    (observe : Input → State → Output)
    (project : State → Code)
    (codedStep : Input → Code → Code)
    (codedObserve : Input → Code → Output)
    (transitionSquare : (u : Input) (s : State) →
      project (step u s) ≡ codedStep u (project s))
    (observationSquare : (u : Input) (s : State) →
      observe u s ≡ codedObserve u (project s)) where

    sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
    sym refl = refl

    trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
    trans refl p = p

    outputStable : (u : Input) (s t : State) →
      project s ≡ project t → observe u s ≡ observe u t
    outputStable u s t eq =
      trans (observationSquare u s)
        (trans (Future.cong (codedObserve u) eq)
          (sym (observationSquare u t)))

    successorStable : (u : Input) (s t : State) →
      project s ≡ project t →
      project (step u s) ≡ project (step u t)
    successorStable u s t eq =
      trans (transitionSquare u s)
        (trans (Future.cong (codedStep u) eq)
          (sym (transitionSquare u t)))

    allWords : (inputs : List Input) (s t : State) →
      project s ≡ project t →
      Future.trace step observe inputs s ≡
      Future.trace step observe inputs t
    allWords inputs s t eq =
      Future.inputIndexedTraceDescent step observe project
        outputStable successorStable inputs s t eq

  -- Retaining the exact source index is a separate consumer decision:
  -- history, physical time, refinement, Frobenius and version cannot be
  -- removed merely by showing a chart on the nine-trit spatial carrier.
  module IndexNecessity
    {Output : Set}
    (readIndex : Index → Output)
    (k0 k1 : Index)
    (distinct : readIndex k0 ≡ readIndex k1 → ⊥)
    (x : Full)
    (r : Residual) where

    sameSpatialChart :
      chart (reopen x r k0) ≡ chart (reopen x r k1)
    sameSpatialChart = refl

    noSpatialOnlyIndexReader :
      (read : Full → Output) →
      ((s : State) → read (chart s) ≡ readIndex (sourceIndex s)) → ⊥
    noSpatialOnlyIndexReader read exact =
      distinct (trans (sym (exact (reopen x r k0)))
        (exact (reopen x r k1)))
      where
        sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
        sym refl = refl
        trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
        trans refl p = p

  -- Deliberately not instantiated to source neural bytes: source-specific
  -- chart and state splitting, plus native observation/transition squares,
  -- are required before a quotient can be asserted. Indexed six-face data
  -- come from GovernedIndexedResidualCubeExact; BIDI alone is insufficient.

  module ResidualNecessity
    {Output : Set}
    (readResidual : Residual → Output)
    (r0 r1 : Residual)
    (distinct : readResidual r0 ≡ readResidual r1 → ⊥)
    (x : Full)
    (k : Index) where

    sameSpatialChart :
      chart (reopen x r0 k) ≡ chart (reopen x r1 k)
    sameSpatialChart = refl

    noSpatialOnlyResidualReader :
      (read : Full → Output) →
      ((s : State) → read (chart s) ≡ readResidual (residual s)) → ⊥
    noSpatialOnlyResidualReader read exact =
      distinct (trans (sym (exact (reopen x r0 k)))
        (exact (reopen x r1 k)))
      where
        sym : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
        sym refl = refl
        trans : ∀ {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
        trans refl p = p
