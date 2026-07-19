module DASHI.Core.NonlinearExplodedSparsity where

open import DASHI.Core.Prelude
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)
open import DASHI.Core.MinimalKernelAlgebra
  using (SupportSign; encodeSupportSign; decodeSupportSign; decodeEncodeSupportSign)
open import Relation.Nullary using (Dec; yes; no)

------------------------------------------------------------------------
-- Logical equivalence
------------------------------------------------------------------------

record _↔_ (A B : Set) : Set where
  constructor iff
  field
    forward  : A → B
    backward : B → A

open _↔_ public

------------------------------------------------------------------------
-- Atomic ternary states and exact exploded atoms
------------------------------------------------------------------------

State : Set → Set
State X = X → Trit

record ExplodedAtom : Set where
  constructor exploded
  field
    source      : Trit
    supportSign : SupportSign
    exact       : decodeSupportSign supportSign ≡ source

explodeAtom : Trit → ExplodedAtom
explodeAtom t = exploded t (encodeSupportSign t) (decodeEncodeSupportSign t)

ExplodedState : Set → Set
ExplodedState X = X → ExplodedAtom

explodeState : {X : Set} → State X → ExplodedState X
explodeState s x = explodeAtom (s x)

ActiveAtom : {X : Set} → State X → Set
ActiveAtom {X} s = Σ X (λ x → ¬ (s x ≡ zer))

NeutralAtom : {X : Set} → State X → Set
NeutralAtom {X} s = Σ X (λ x → s x ≡ zer)

PositiveAtom : {X : Set} → State X → Set
PositiveAtom {X} s = Σ X (λ x → s x ≡ pos)

NegativeAtom : {X : Set} → State X → Set
NegativeAtom {X} s = Σ X (λ x → s x ≡ neg)

------------------------------------------------------------------------
-- Affine/local carrier followed by a nonlinear ternary classifier
------------------------------------------------------------------------

record TritPartition (L : Set) : Set₁ where
  field
    classify : L → Trit

    NegativeRegion : L → Set
    NeutralRegion  : L → Set
    PositiveRegion : L → Set

    negativeExact : (ℓ : L) → classify ℓ ≡ neg ↔ NegativeRegion ℓ
    neutralExact  : (ℓ : L) → classify ℓ ≡ zer ↔ NeutralRegion ℓ
    positiveExact : (ℓ : L) → classify ℓ ≡ pos ↔ PositiveRegion ℓ

record ThresholdKernel (X L : Set) : Set₁ where
  field
    localField : State X → X → L
    partition  : TritPartition L

applyKernel :
  {X L : Set} → ThresholdKernel X L → State X → State X
applyKernel K s x =
  TritPartition.classify (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)

KernelClosed :
  {X L : Set} → ThresholdKernel X L → State X → Set
KernelClosed {X} K s = (x : X) → applyKernel K s x ≡ s x

LocalConstraint :
  {X L : Set} → ThresholdKernel X L → State X → X → Set
LocalConstraint K s x = applyKernel K s x ≡ s x

KernelDefect :
  {X L : Set} → ThresholdKernel X L → State X → X → Set
KernelDefect K s x = ¬ LocalConstraint K s x

TransitionDefect :
  {X L : Set} → ThresholdKernel X L → State X → X → Set
TransitionDefect K s x = ¬ (s x ≡ applyKernel K s x)

------------------------------------------------------------------------
-- Exact nonlinear sparsification theorem
--
-- Projection creates an exact neutral support: a projected atom is zero
-- exactly when its local field lies in the declared neutral region.
------------------------------------------------------------------------

nonlinearSparsityExact :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) (x : X) →
  applyKernel K s x ≡ zer ↔
  TritPartition.NeutralRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
nonlinearSparsityExact K s x =
  TritPartition.neutralExact (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)

nonlinearPositiveExact :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) (x : X) →
  applyKernel K s x ≡ pos ↔
  TritPartition.PositiveRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
nonlinearPositiveExact K s x =
  TritPartition.positiveExact (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)

nonlinearNegativeExact :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) (x : X) →
  applyKernel K s x ≡ neg ↔
  TritPartition.NegativeRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
nonlinearNegativeExact K s x =
  TritPartition.negativeExact (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)

------------------------------------------------------------------------
-- Fixed-point margin characterization
------------------------------------------------------------------------

closedNeutralHasNeutralMargin :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) →
  KernelClosed K s →
  (x : X) → s x ≡ zer →
  TritPartition.NeutralRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
closedNeutralHasNeutralMargin K s closed x sx=0 =
  forward (nonlinearSparsityExact K s x)
    (trans (closed x) sx=0)

closedPositiveHasPositiveMargin :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) →
  KernelClosed K s →
  (x : X) → s x ≡ pos →
  TritPartition.PositiveRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
closedPositiveHasPositiveMargin K s closed x sx=+ =
  forward (nonlinearPositiveExact K s x)
    (trans (closed x) sx=+)

closedNegativeHasNegativeMargin :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) →
  KernelClosed K s →
  (x : X) → s x ≡ neg →
  TritPartition.NegativeRegion (ThresholdKernel.partition K)
    (ThresholdKernel.localField K s x)
closedNegativeHasNegativeMargin K s closed x sx=- =
  forward (nonlinearNegativeExact K s x)
    (trans (closed x) sx=-)

------------------------------------------------------------------------
-- Conditional localization of defects to a sparse/low-margin carrier
--
-- Sparse defect support is not a theorem of arbitrary threshold systems.
-- It follows from an explicit stability law outside a chosen low-margin set.
------------------------------------------------------------------------

record MarginControl
  {X L : Set}
  (K : ThresholdKernel X L)
  (s : State X)
  (LowMargin : X → Set) : Set₁ where
  field
    stableOutside : (x : X) → ¬ LowMargin x → LocalConstraint K s x

open MarginControl public

defectConfinedDoubleNegation :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {LowMargin : X → Set} →
  MarginControl K s LowMargin →
  (x : X) → KernelDefect K s x → ¬ ¬ LowMargin x
defectConfinedDoubleNegation control x defect outside =
  defect (stableOutside control x outside)

defectConfined :
  {X L : Set} {K : ThresholdKernel X L} {s : State X}
  {LowMargin : X → Set} →
  MarginControl K s LowMargin →
  ((x : X) → Dec (LowMargin x)) →
  (x : X) → KernelDefect K s x → LowMargin x
defectConfined control decideLow x defect with decideLow x
... | yes low = low
... | no outside = ⊥-elim (defectConfinedDoubleNegation control x defect outside)

------------------------------------------------------------------------
-- Weighted threshold CSP correspondence
------------------------------------------------------------------------

SatisfiesAllLocalConstraints :
  {X L : Set} → ThresholdKernel X L → State X → Set
SatisfiesAllLocalConstraints {X} K s =
  (x : X) → LocalConstraint K s x

kernelClosed→CSP :
  {X L : Set} {K : ThresholdKernel X L} {s : State X} →
  KernelClosed K s → SatisfiesAllLocalConstraints K s
kernelClosed→CSP closed = closed

CSP→kernelClosed :
  {X L : Set} {K : ThresholdKernel X L} {s : State X} →
  SatisfiesAllLocalConstraints K s → KernelClosed K s
CSP→kernelClosed satisfies = satisfies

kernelClosureIffCSP :
  {X L : Set} (K : ThresholdKernel X L) (s : State X) →
  KernelClosed K s ↔ SatisfiesAllLocalConstraints K s
kernelClosureIffCSP K s = iff kernelClosed→CSP CSP→kernelClosed

kernelDefect→transitionDefect :
  {X L : Set} {K : ThresholdKernel X L} {s : State X} {x : X} →
  KernelDefect K s x → TransitionDefect K s x
kernelDefect→transitionDefect defect same = defect (sym same)

transitionDefect→kernelDefect :
  {X L : Set} {K : ThresholdKernel X L} {s : State X} {x : X} →
  TransitionDefect K s x → KernelDefect K s x
transitionDefect→kernelDefect defect same = defect (sym same)

------------------------------------------------------------------------
-- Explicit separation from coordinate-wise ℓ1/ReLU-style sparsifiers
------------------------------------------------------------------------

CoordinateRule : Set → Set
CoordinateRule X = Trit → Trit

coordinateLift :
  {X : Set} → CoordinateRule X → State X → State X
coordinateLift f s x = f (s x)

coordinateRuleIsPointwise :
  {X : Set} (f : CoordinateRule X) (s t : State X) (x : X) →
  s x ≡ t x → coordinateLift f s x ≡ coordinateLift f t x
coordinateRuleIsPointwise f s t x same = cong f same

record CoordinateRepresentation
  {X L : Set}
  (K : ThresholdKernel X L) : Set₁ where
  field
    coordinateRule : Trit → Trit
    represents : (s : State X) (x : X) →
      applyKernel K s x ≡ coordinateRule (s x)

record NonCoordinateWitness
  {X L : Set}
  (K : ThresholdKernel X L) : Set₁ where
  field
    leftState   : State X
    rightState  : State X
    witnessNode : X
    sameAtom : leftState witnessNode ≡ rightState witnessNode
    differentOutput : ¬
      (applyKernel K leftState witnessNode ≡
       applyKernel K rightState witnessNode)

nonCoordinateWitnessRulesOutCoordinateRepresentation :
  {X L : Set} {K : ThresholdKernel X L} →
  NonCoordinateWitness K → ¬ CoordinateRepresentation K
nonCoordinateWitnessRulesOutCoordinateRepresentation witness representation =
  NonCoordinateWitness.differentOutput witness
    (trans
      (CoordinateRepresentation.represents representation
        (NonCoordinateWitness.leftState witness)
        (NonCoordinateWitness.witnessNode witness))
      (trans
        (cong (CoordinateRepresentation.coordinateRule representation)
          (NonCoordinateWitness.sameAtom witness))
        (sym
          (CoordinateRepresentation.represents representation
            (NonCoordinateWitness.rightState witness)
            (NonCoordinateWitness.witnessNode witness)))))

------------------------------------------------------------------------
-- Exact exploded/CSP reading
--
-- ActiveAtom is the sparse support carrier.  KernelDefect is the set of
-- violated local threshold clauses.  No claim that defects are minimal
-- unsatisfiable cores is made without an additional minimality theorem.
------------------------------------------------------------------------

ExplodedConstraintGeometry :
  {X L : Set} → ThresholdKernel X L → State X → Set₁
ExplodedConstraintGeometry {X} K s =
  ActiveAtom s ×
  (NeutralAtom s ×
   ((x : X) → KernelDefect K s x → Set))
