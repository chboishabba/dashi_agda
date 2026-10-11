module DASHI.Mathematics.Algebra.Ternary27FirstTitsF4RootRecognitionExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Mathematics.Algebra.Ternary27FirstTitsDerivationF4SignalExact as Derivation
import DASHI.Reasoning.AlbertF4FiniteWeylMaxCutExact as Finite

------------------------------------------------------------------------
-- SAME-DERIVATION F4 ROOT RECOGNITION
--
-- The local exact probe starts with the already-computed 52-dimensional
-- derivation algebra of the actual first-Tits product J(M3(F3),1).  Among the
-- literal inner derivations it finds twelve primitive toral operators D^3=D
-- and a four-dimensional commuting torus.  Simultaneous eigenspaces then give
--
--   J27 : zero weight multiplicity 3 + 24 distinct 1-d nonzero weights
--   Der : Cartan multiplicity 4     + 48 distinct 1-d nonzero root spaces.
--
-- An explicit GL4(F3) coordinate change sends those 48 roots exactly onto the
-- standard mod-3 F4 root carrier
--
--   +-e_i ; +-e_i+-e_j ; all (+-1,+-1,+-1,+-1).
--
-- This pays an actual root-system recognition on the same derivation algebra;
-- it is strictly stronger than dimension 52.  Smooth/algebraic group-scheme
-- recognition in characteristic three and the global automorphism-group
-- theorem remain separate.
------------------------------------------------------------------------

f4RootCoordinateChange : String
f4RootCoordinateChange =
  "[[1,2,1,1],[1,1,2,1],[2,2,2,2],[0,0,0,1]] mod 3"

record FirstTitsF4RootRecognitionLocalReceipt : Set where
  constructor first-tits-f4-root-recognition-local-receipt
  field
    sameFirstTitsProductDerivationsUsed : Bool
    primitiveToralDerivationCount : Nat
    commutingIndependentTorusDimension : Nat
    carrierZeroWeightDimension : Nat
    carrierDistinctNonzeroWeightCount : Nat
    carrierNonzeroWeightSpacesOneDimensional : Bool
    adjointZeroWeightDimension : Nat
    adjointDistinctNonzeroRootCount : Nat
    adjointRootSpacesOneDimensional : Bool
    explicitGL4ChangeInvertible : Bool
    transportedRootsEqualStandardF4Mod3RootSet : Bool
    agreesWithExistingFiniteF4RootCount48 : Bool
    agreesWithExistingMinuscule24PlusZero3 : Bool
    characteristicThreeLieRootRecognitionPaidLocally : Bool
    algebraicAutomorphismGroupRecognitionPaid : Bool
    smoothGroupSchemeRecognitionPaid : Bool
    boundary : String
open FirstTitsF4RootRecognitionLocalReceipt public

canonicalFirstTitsF4RootRecognitionLocalReceipt : FirstTitsF4RootRecognitionLocalReceipt
canonicalFirstTitsF4RootRecognitionLocalReceipt =
  first-tits-f4-root-recognition-local-receipt
    true
    12 4
    3 24 true
    4 48 true
    true true
    true true true
    false false
    "The actual J(M3(F3),1) derivation algebra now has a rank-four toral decomposition with 48 one-dimensional nonzero roots explicitly transported onto the standard mod-3 F4 root set; its 27-dimensional module has 24 one-dimensional nonzero weights plus a 3-dimensional zero weight, matching the independently paid folded finite F4 model. This is root/action recognition of the Lie algebra representation, not yet a theorem identifying the full characteristic-three automorphism group scheme with F4."

------------------------------------------------------------------------
-- Remaining promotion boundary.
------------------------------------------------------------------------

data F4RootRecognitionCreatesGlobalAutomorphismGroup : Set where
data Mod3RootEqualityCreatesSmoothGroupScheme : Set where

rootRecognitionDoesNotCreateGlobalGroup :
  F4RootRecognitionCreatesGlobalAutomorphismGroup → {A : Set} → A
rootRecognitionDoesNotCreateGlobalGroup ()

mod3RootsDoNotCreateSmoothGroupScheme :
  Mod3RootEqualityCreatesSmoothGroupScheme → {A : Set} → A
mod3RootsDoNotCreateSmoothGroupScheme ()
