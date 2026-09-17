module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBCVScriptManifestValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinasePDBCVScriptManifestExact as Script

boundary = Script.canonicalAdKPDBCVScriptManifestBoundary

_ : Script.deterministicArtifactSchemaDefined boundary ≡ true
_ = refl

_ : Script.sourceBytesSha256Required boundary ≡ true
_ = refl

_ : Script.modelChainAltlocPolicyExplicit boundary ≡ true
_ = refl

_ : Script.selectionManifestHashesRequired boundary ≡ true
_ = refl

_ : Script.dLnSourceAtomSubsetResolvedByScript boundary ≡ false
_ = refl

_ : Script.scriptExecutionCreatesScientificAuthority boundary ≡ false
_ = refl

_ : Script.real4AKE1AKEExecutionPaidHere boundary ≡ false
_ = refl
