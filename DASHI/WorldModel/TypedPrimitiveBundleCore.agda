module DASHI.WorldModel.TypedPrimitiveBundleCore where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.String using (String)

import DASHI.Core.DependencyPullbackCore as Pullback
import DASHI.Core.ReplayArtifactCore as Replay

------------------------------------------------------------------------
-- Explicit, namespace-bound primitive bundles for agents.
--
-- This replaces semantic magic such as "import physics" with a typed bundle
-- whose exports, dependencies, validity witness, and replay receipts are
-- inspectable.  Bundle opening is downstream of the symbol/index graph.
------------------------------------------------------------------------

record TypedPrimitiveBundle : Set₁ where
  constructor typedPrimitiveBundle
  field
    Export      : Set
    Dependency  : Set
    Validity    : Set

    bundleName  : String
    exports     : List Export
    dependencies : List Dependency
    validityDomain : Validity
    dependencyStatus : Dependency → Pullback.DependencyStatus
    replayReceipt : Replay.ReplayArtifactCore

open TypedPrimitiveBundle public

record BundleUseWitness
  (bundle : TypedPrimitiveBundle)
  (dependency : Dependency bundle) : Set where
  constructor bundleUseWitness
  field
    dependencyLive :
      dependencyStatus bundle dependency ≡ Pullback.live
    replayLive : Replay.replayable (replayReceipt bundle) ≡ true

open BundleUseWitness public

record OpenedBundle (bundle : TypedPrimitiveBundle) : Set where
  constructor openedBundle
  field
    selectedDependency : Dependency bundle
    useWitness : BundleUseWitness bundle selectedDependency

open OpenedBundle public

openedBundleDependencyIsLive :
  (bundle : TypedPrimitiveBundle) →
  (opened : OpenedBundle bundle) →
  dependencyStatus bundle (selectedDependency opened) ≡ Pullback.live
openedBundleDependencyIsLive bundle opened =
  dependencyLive (useWitness opened)
