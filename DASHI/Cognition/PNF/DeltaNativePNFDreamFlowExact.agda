module DASHI.Cognition.PNF.DeltaNativePNFDreamFlowExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)

------------------------------------------------------------------------
-- Delta-native semantic execution.
--
-- The canonical compiler does not have a privileged "initial full state" mode.
-- Every input emits a semantic delta.  First ingestion is the same fold from the
-- neutral authority state that later ingestion uses.  A bulk tranche is merely
-- an associatively fused delta stream.
------------------------------------------------------------------------

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl

trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

record DeltaAlgebra (Authority Delta : Set) : Set₁ where
  field
    neutralDelta : Delta
    composeDelta : Delta → Delta → Delta
    emptyAuthority : Authority
    applyDelta : Authority → Delta → Authority

    composeLeftIdentity : ∀ delta → composeDelta neutralDelta delta ≡ delta
    composeRightIdentity : ∀ delta → composeDelta delta neutralDelta ≡ delta
    composeAssociative : ∀ a b c →
      composeDelta (composeDelta a b) c
        ≡ composeDelta a (composeDelta b c)

    applyNeutral : ∀ authority →
      applyDelta authority neutralDelta ≡ authority

    applyComposition : ∀ authority first second →
      applyDelta (applyDelta authority first) second
        ≡ applyDelta authority (composeDelta first second)

open DeltaAlgebra public

record DeltaNativeCompiler
    (Input Authority Delta : Set) : Set₁ where
  field
    algebra : DeltaAlgebra Authority Delta
    emitDelta : Input → Delta

open DeltaNativeCompiler public

compileDeltas :
  ∀ {Input Authority Delta : Set} →
  DeltaNativeCompiler Input Authority Delta →
  List Input → Delta
compileDeltas compiler [] = neutralDelta (algebra compiler)
compileDeltas compiler (input ∷ rest) =
  composeDelta
    (algebra compiler)
    (emitDelta compiler input)
    (compileDeltas compiler rest)

materialize :
  ∀ {Input Authority Delta : Set} →
  DeltaNativeCompiler Input Authority Delta →
  List Input → Authority
materialize compiler inputs =
  applyDelta
    (algebra compiler)
    (emptyAuthority (algebra compiler))
    (compileDeltas compiler inputs)

------------------------------------------------------------------------
-- There is no separate bootstrap semantics.
------------------------------------------------------------------------

firstInputIsOrdinaryDelta :
  ∀ {Input Authority Delta : Set}
    (compiler : DeltaNativeCompiler Input Authority Delta)
    (input : Input) →
  compileDeltas compiler (input ∷ [])
    ≡ composeDelta
        (algebra compiler)
        (emitDelta compiler input)
        (neutralDelta (algebra compiler))
firstInputIsOrdinaryDelta compiler input = refl

firstInputNormalizesToEmittedDelta :
  ∀ {Input Authority Delta : Set}
    (compiler : DeltaNativeCompiler Input Authority Delta)
    (input : Input) →
  compileDeltas compiler (input ∷ []) ≡ emitDelta compiler input
firstInputNormalizesToEmittedDelta compiler input =
  composeRightIdentity (algebra compiler) (emitDelta compiler input)

------------------------------------------------------------------------
-- Partition/fusion law.
--
-- Physical batching is free to choose its partition.  The semantic delta is
-- determined only by ordered composition of the same input stream.
------------------------------------------------------------------------

append : ∀ {A : Set} → List A → List A → List A
append [] right = right
append (x ∷ xs) right = x ∷ append xs right

compileAppend :
  ∀ {Input Authority Delta : Set}
    (compiler : DeltaNativeCompiler Input Authority Delta)
    (left right : List Input) →
  compileDeltas compiler (append left right)
    ≡ composeDelta
        (algebra compiler)
        (compileDeltas compiler left)
        (compileDeltas compiler right)
compileAppend compiler [] right =
  sym
    (composeLeftIdentity
      (algebra compiler)
      (compileDeltas compiler right))
compileAppend compiler (x ∷ xs) right =
  trans
    (cong
      (composeDelta (algebra compiler) (emitDelta compiler x))
      (compileAppend compiler xs right))
    (sym
      (composeAssociative
        (algebra compiler)
        (emitDelta compiler x)
        (compileDeltas compiler xs)
        (compileDeltas compiler right)))

materializeAppend :
  ∀ {Input Authority Delta : Set}
    (compiler : DeltaNativeCompiler Input Authority Delta)
    (left right : List Input) →
  materialize compiler (append left right)
    ≡ applyDelta
        (algebra compiler)
        (materialize compiler left)
        (compileDeltas compiler right)
materializeAppend compiler left right =
  trans
    (cong
      (applyDelta
        (algebra compiler)
        (emptyAuthority (algebra compiler)))
      (compileAppend compiler left right))
    (sym
      (applyComposition
        (algebra compiler)
        (emptyAuthority (algebra compiler))
        (compileDeltas compiler left)
        (compileDeltas compiler right)))

------------------------------------------------------------------------
-- Process boundary.
------------------------------------------------------------------------

data InitialFullBuildSemanticPrivilege : Set where

data StateRescanRequiredForNextDelta : Set where

initialFullBuildHasNoDefaultSemanticPrivilege :
  InitialFullBuildSemanticPrivilege → ∀ {A : Set} → A
initialFullBuildHasNoDefaultSemanticPrivilege ()

stateRescanIsNotRequiredByDeltaAlgebra :
  StateRescanRequiredForNextDelta → ∀ {A : Set} → A
stateRescanIsNotRequiredByDeltaAlgebra ()
