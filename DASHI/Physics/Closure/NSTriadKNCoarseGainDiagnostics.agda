module DASHI.Physics.Closure.NSTriadKNCoarseGainDiagnostics where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false; if_then_else_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation as Allocation

------------------------------------------------------------------------
-- Exact finite diagnostics for a proposed classification and norm.
--
-- These computations may falsify a class/norm proposal.  They do not promote
-- finite evidence to a cutoff-uniform theorem.
------------------------------------------------------------------------

sumNat : List Nat → Nat
sumNat [] = zero
sumNat (x ∷ xs) = x + sumNat xs

maxNat : Nat → Nat → Nat
maxNat zero n = n
maxNat (suc m) zero = suc m
maxNat (suc m) (suc n) = suc (maxNat m n)

maximumNat : List Nat → Nat
maximumNat [] = zero
maximumNat (x ∷ xs) = maxNat x (maximumNat xs)

record CoarseGainDiagnosticInputs {i p : Level} : Set (lsuc (i Agda.Primitive.⊔ p)) where
  field
    Index : Set i
    PhysicalIncidence : Set p

    indices : List Index
    physicalIncidences : List PhysicalIncidence

    source target : PhysicalIncidence → Index
    classOf : PhysicalIncidence → Allocation.Stage3Class

    indexEqual : Index → Index → Bool

    -- Magnitude of the exact signed coefficient after the chosen test and
    -- polarisation data have been fixed.
    coefficientMagnitude : PhysicalIncidence → Nat

    -- The two terms are kept explicit so diagnostics can test different
    -- Schur/energy weights without changing physical enumeration.
    rowWeightFactor : Index → Index → Nat
    columnWeightFactor : Index → Index → Nat

open CoarseGainDiagnosticInputs public

sameClass : Allocation.Stage3Class → Allocation.Stage3Class → Bool
sameClass Allocation.forcedTail Allocation.forcedTail = true
sameClass Allocation.transition Allocation.transition = true
sameClass Allocation.adversarial Allocation.adversarial = true
sameClass Allocation.residual Allocation.residual = true
sameClass _ _ = false

rowTerm :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → PhysicalIncidence D → Nat
rowTerm D class row τ =
  if indexEqual D (source D τ) row then
    if sameClass (classOf D τ) class then
      coefficientMagnitude D τ *
      rowWeightFactor D (source D τ) (target D τ)
    else zero
  else zero

columnTerm :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → PhysicalIncidence D → Nat
columnTerm D class column τ =
  if indexEqual D (target D τ) column then
    if sameClass (classOf D τ) class then
      coefficientMagnitude D τ *
      columnWeightFactor D (source D τ) (target D τ)
    else zero
  else zero

mapRowTerms :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → List (PhysicalIncidence D) → List Nat
mapRowTerms D class row [] = []
mapRowTerms D class row (τ ∷ rest) =
  rowTerm D class row τ ∷ mapRowTerms D class row rest

mapColumnTerms :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → List (PhysicalIncidence D) → List Nat
mapColumnTerms D class column [] = []
mapColumnTerms D class column (τ ∷ rest) =
  columnTerm D class column τ ∷ mapColumnTerms D class column rest

classRowSum :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → Nat
classRowSum D class row =
  sumNat (mapRowTerms D class row (physicalIncidences D))

classColumnSum :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Index D → Nat
classColumnSum D class column =
  sumNat (mapColumnTerms D class column (physicalIncidences D))

mapClassRows :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → List (Index D) → List Nat
mapClassRows D class [] = []
mapClassRows D class (row ∷ rows) =
  classRowSum D class row ∷ mapClassRows D class rows

mapClassColumns :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → List (Index D) → List Nat
mapClassColumns D class [] = []
mapClassColumns D class (column ∷ columns) =
  classColumnSum D class column ∷ mapClassColumns D class columns

maximumClassRow :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Nat
maximumClassRow D class = maximumNat (mapClassRows D class (indices D))

maximumClassColumn :
  ∀ {i p} (D : CoarseGainDiagnosticInputs {i} {p}) →
  Allocation.Stage3Class → Nat
maximumClassColumn D class = maximumNat (mapClassColumns D class (indices D))

record CutoffDiagnosticResult : Set where
  constructor cutoff-diagnostic
  field
    cutoff : Nat
    forcedTailMaxRow forcedTailMaxColumn : Nat
    transitionMaxRow transitionMaxColumn : Nat
    adversarialMaxRow adversarialMaxColumn : Nat
    residualMaxRow residualMaxColumn : Nat

open CutoffDiagnosticResult public

runCutoffDiagnostic :
  ∀ {i p} → Nat → CoarseGainDiagnosticInputs {i} {p} → CutoffDiagnosticResult
runCutoffDiagnostic N D = cutoff-diagnostic
  N
  (maximumClassRow D Allocation.forcedTail)
  (maximumClassColumn D Allocation.forcedTail)
  (maximumClassRow D Allocation.transition)
  (maximumClassColumn D Allocation.transition)
  (maximumClassRow D Allocation.adversarial)
  (maximumClassColumn D Allocation.adversarial)
  (maximumClassRow D Allocation.residual)
  (maximumClassColumn D Allocation.residual)

scaledMaximum : Nat → Nat → Nat
scaledMaximum N diagnostic = (N * N) * diagnostic

record CoarseClassSurvivesUniformTest
    (results : List CutoffDiagnosticResult) : Set₁ where
  field
    uniformBound : Nat

    forcedTailRowsBounded : Set
    forcedTailColumnsBounded : Set
    transitionRowsBounded : Set
    transitionColumnsBounded : Set
    adversarialRowsBounded : Set
    adversarialColumnsBounded : Set
    residualRowsBounded : Set
    residualColumnsBounded : Set

open CoarseClassSurvivesUniformTest public

coarseFiniteDiagnosticsExecutable : Bool
coarseFiniteDiagnosticsExecutable = true

coarseFiniteDiagnosticsExecutableIsTrue :
  coarseFiniteDiagnosticsExecutable ≡ true
coarseFiniteDiagnosticsExecutableIsTrue = refl

coarseClassesProvedUniformlySufficient : Bool
coarseClassesProvedUniformlySufficient = false

coarseClassesProvedUniformlySufficientIsFalse :
  coarseClassesProvedUniformlySufficient ≡ false
coarseClassesProvedUniformlySufficientIsFalse = refl
