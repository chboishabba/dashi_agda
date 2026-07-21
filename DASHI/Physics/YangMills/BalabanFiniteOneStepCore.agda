module DASHI.Physics.YangMills.BalabanFiniteOneStepCore where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; suc) renaming (zero to natZero)
open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Data.Product.Base using (_×_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

infixr 9 _∘_
infixr 5 _++_

_∘_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (B → C) → (A → B) → A → C
(f ∘ g) x = f (g x)

id : ∀ {a} {A : Set a} → A → A
id x = x

_≈_ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → (A → B) → Set (a ⊔ b)
f ≈ g = ∀ x → f x ≡ g x

_++_ : ∀ {a} {A : Set a} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

fold : ∀ {a} {A : Set a} → (A → A → A) → A → List A → A
fold combine unit [] = unit
fold combine unit (x ∷ xs) = combine x (fold combine unit xs)

data EvidenceStatus : Set where
  exactProof rationalCertificate intervalCertificate floatingExperiment conjecture counterexample : EvidenceStatus

record EvidenceEnvelope {a : Level} (Claim : Set a) : Set (lsuc a) where
  field
    status : EvidenceStatus
    payload : Set a
    validates : payload → Claim

record FiniteFamily {a : Level} (A : Set a) : Set (lsuc a) where
  field enumerate : List A
open FiniteFamily public

Matrix : ∀ {r c s} → Set r → Set c → Set s → Set (r ⊔ c ⊔ s)
Matrix Row Col Scalar = Row → Col → Scalar

transpose : ∀ {r c s} {Row : Set r} {Col : Set c} {Scalar : Set s} → Matrix Row Col Scalar → Matrix Col Row Scalar
transpose A j i = A i j

record FiniteSumSocket {i s : Level} (Index : Set i) (Scalar : Set s) : Set (lsuc (i ⊔ s)) where
  field
    indices : List Index
    zero : Scalar
    add : Scalar → Scalar → Scalar
open FiniteSumSocket public

sumWith : ∀ {i s} {Index : Set i} {Scalar : Set s} → FiniteSumSocket Index Scalar → (Index → Scalar) → Scalar
sumWith socket f = fold (add socket) (zero socket) (map f (indices socket))

matrixCompose : ∀ {r m c s} {Row : Set r} {Middle : Set m} {Col : Set c} {Scalar : Set s} →
  FiniteSumSocket Middle Scalar → (Scalar → Scalar → Scalar) →
  Matrix Row Middle Scalar → Matrix Middle Col Scalar → Matrix Row Col Scalar
matrixCompose socket multiply A B i k = sumWith socket (λ j → multiply (A i j) (B j k))

record FiniteInverseCertificate {a : Level} (A : Set a) : Set (lsuc a) where
  field
    operator inverse : A → A
    inverseLeft : (inverse ∘ operator) ≈ (λ x → x)
    inverseRight : (operator ∘ inverse) ≈ (λ x → x)
open FiniteInverseCertificate public

record ConstrainedMinimizerData {f c : Level} (Fine : Set f) (Coarse : Set c) : Set (lsuc (f ⊔ c)) where
  field
    covariance : Fine → Fine
    average : Fine → Coarse
    averageStar : Coarse → Fine
    middleInverse : Coarse → Coarse
    middleInverseLeft : ∀ coarse → average (covariance (averageStar (middleInverse coarse))) ≡ coarse
open ConstrainedMinimizerData public

constrainedMinimizer : ∀ {f c} {Fine : Set f} {Coarse : Set c} → ConstrainedMinimizerData Fine Coarse → Coarse → Fine
constrainedMinimizer bundle coarse = covariance bundle (averageStar bundle (middleInverse bundle coarse))

constrainedMinimizerHasAverage : ∀ {f c} {Fine : Set f} {Coarse : Set c}
  (bundle : ConstrainedMinimizerData Fine Coarse) →
  ∀ coarse → average bundle (constrainedMinimizer bundle coarse) ≡ coarse
constrainedMinimizerHasAverage bundle = middleInverseLeft bundle

record KernelProjectionData {f c : Level} (Fine : Set f) (Coarse : Set c) : Set (lsuc (f ⊔ c)) where
  field
    minimizerData : ConstrainedMinimizerData Fine Coarse
    fineSubtract : Fine → Fine → Fine
    coarseSubtract : Coarse → Coarse → Coarse
    coarseZero : Coarse
    averageSubtract : ∀ left right →
      average minimizerData (fineSubtract left right) ≡
      coarseSubtract (average minimizerData left) (average minimizerData right)
    coarseSubtractSelf : ∀ coarse → coarseSubtract coarse coarse ≡ coarseZero
open KernelProjectionData public

kernelProjection : ∀ {f c} {Fine : Set f} {Coarse : Set c} → KernelProjectionData Fine Coarse → Fine → Fine
kernelProjection bundle fine =
  fineSubtract bundle fine
    (constrainedMinimizer (minimizerData bundle) (average (minimizerData bundle) fine))

kernelProjectionHasZeroAverage : ∀ {f c} {Fine : Set f} {Coarse : Set c}
  (bundle : KernelProjectionData Fine Coarse) → ∀ fine →
  average (minimizerData bundle) (kernelProjection bundle fine) ≡ coarseZero bundle
kernelProjectionHasZeroAverage bundle fine =
  trans
    (averageSubtract bundle fine
      (constrainedMinimizer (minimizerData bundle) (average (minimizerData bundle) fine)))
    (trans
      (cong (coarseSubtract bundle (average (minimizerData bundle) fine))
        (constrainedMinimizerHasAverage (minimizerData bundle) (average (minimizerData bundle) fine)))
      (coarseSubtractSelf bundle (average (minimizerData bundle) fine)))

record FiniteWilsonActionData {p l s : Level} (Plaquette : Set p) (Link : Set l) (Scalar : Set s) : Set (lsuc (p ⊔ l ⊔ s)) where
  field
    plaquettes : List Plaquette
    plaquetteHolonomy : Plaquette → Link
    normalizedRealTrace : Link → Scalar
    scalarZero scalarOne : Scalar
    scalarAdd scalarSubtract : Scalar → Scalar → Scalar
open FiniteWilsonActionData public

wilsonPlaquetteTerm : ∀ {p l s} {Plaquette : Set p} {Link : Set l} {Scalar : Set s} →
  FiniteWilsonActionData Plaquette Link Scalar → Plaquette → Scalar
wilsonPlaquetteTerm bundle plaquette =
  scalarSubtract bundle (scalarOne bundle)
    (normalizedRealTrace bundle (plaquetteHolonomy bundle plaquette))

finiteWilsonAction : ∀ {p l s} {Plaquette : Set p} {Link : Set l} {Scalar : Set s} →
  FiniteWilsonActionData Plaquette Link Scalar → Scalar
finiteWilsonAction bundle =
  fold (scalarAdd bundle) (scalarZero bundle)
    (map (wilsonPlaquetteTerm bundle) (plaquettes bundle))

record FiniteVariationData {b d s : Level} (Background : Set b) (Direction : Set d) (Scalar : Set s) : Set (lsuc (b ⊔ d ⊔ s)) where
  field
    action : Background → Scalar
    shift : Background → Direction → Background
    addDirection : Direction → Direction → Direction
    negateDirection : Direction → Direction
    scalarAdd scalarSubtract : Scalar → Scalar → Scalar
open FiniteVariationData public

firstVariationNumerator : ∀ {b d s} {Background : Set b} {Direction : Set d} {Scalar : Set s} →
  FiniteVariationData Background Direction Scalar → Background → Direction → Scalar
firstVariationNumerator bundle background direction =
  scalarSubtract bundle
    (action bundle (shift bundle background direction))
    (action bundle background)

secondMixedVariationNumerator : ∀ {b d s} {Background : Set b} {Direction : Set d} {Scalar : Set s} →
  FiniteVariationData Background Direction Scalar → Background → Direction → Direction → Scalar
secondMixedVariationNumerator bundle background left right =
  scalarAdd bundle
    (scalarSubtract bundle
      (action bundle (shift bundle background (addDirection bundle left right)))
      (action bundle (shift bundle background left)))
    (scalarSubtract bundle
      (action bundle background)
      (action bundle (shift bundle background right)))

record FiniteHessianCertificate {v s : Level} (Vector : Set v) (Scalar : Set s) : Set (lsuc (v ⊔ s)) where
  field
    hessian : Vector → Vector
    inner : Vector → Vector → Scalar
    symmetric : ∀ left right → inner left (hessian right) ≡ inner (hessian left) right
    Positive : Scalar → Set s
    positive : ∀ vector → Positive (inner vector (hessian vector))
open FiniteHessianCertificate public

record FiniteCovarianceCertificate {v s : Level} {Vector : Set v} {Scalar : Set s}
  (hessianData : FiniteHessianCertificate Vector Scalar) : Set (lsuc (v ⊔ s)) where
  field
    covariance : Vector → Vector
    covarianceLeft : (covariance ∘ hessian hessianData) ≈ (λ x → x)
    covarianceRight : (hessian hessianData ∘ covariance) ≈ (λ x → x)
open FiniteCovarianceCertificate public

record BlockSchurData {a s : Level} (A : Set a) (Scalar : Set s) : Set (lsuc (a ⊔ s)) where
  field
    aBlock bBlock cBlock dBlock : A → A
    aInverse : A → A
    add subtract compose : (A → A) → (A → A) → A → A
    schurComplement : A → A
    schurDefinition : schurComplement ≡ subtract dBlock (compose cBlock (compose aInverse bBlock))
    determinant : (A → A) → Scalar
    scalarMultiply : Scalar → Scalar → Scalar
    determinantFactorization :
      determinant (add aBlock (add bBlock (add cBlock dBlock))) ≡
      scalarMultiply (determinant aBlock) (determinant schurComplement)
open BlockSchurData public

record FinitePolarizationData {b d s : Level} (Background : Set b) (Direction : Set d) (Scalar : Set s) : Set (lsuc (b ⊔ d ⊔ s)) where
  field
    zeroBackground : Background
    effectiveAction : Background → Scalar
    polarization : Direction → Direction → Scalar
    scalarZero : Scalar
    symmetric : ∀ left right → polarization left right ≡ polarization right left
    divergence : Direction → Direction
    wardLeft : ∀ left right → polarization (divergence left) right ≡ scalarZero
    wardRight : ∀ left right → polarization left (divergence right) ≡ scalarZero
open FinitePolarizationData public

data Walk {a : Level} (Step : Set a) : Set a where
  emptyWalk : Walk Step
  _then_ : Step → Walk Step → Walk Step

walkLength : ∀ {a} {Step : Set a} → Walk Step → Nat
walkLength emptyWalk = natZero
walkLength (_ then rest) = suc (walkLength rest)

record RandomWalkExpansion {t s : Level} (Term : Set t) (Scalar : Set s) : Set (lsuc (t ⊔ s)) where
  field
    termsAtLength : Nat → List Term
    evaluate : Term → Scalar
    scalarZero : Scalar
    scalarAdd : Scalar → Scalar → Scalar
    exactValue : Scalar
    truncation remainder : Nat → Scalar
    exactSplit : ∀ depth → exactValue ≡ scalarAdd (truncation depth) (remainder depth)
open RandomWalkExpansion public

record FiniteContractionCertificate {x d : Level} (State : Set x) (Distance : Set d) : Set (lsuc (x ⊔ d)) where
  field
    step : State → State
    distance : State → State → Distance
    StrictlySmaller : Distance → Distance → Set d
    fixedPoint : State
    fixed : step fixedPoint ≡ fixedPoint
    contractive : ∀ left right → StrictlySmaller (distance (step left) (step right)) (distance left right)
open FiniteContractionCertificate public

record BetaUniformityConjecture {j b h s : Level} (Scale : Set j) (Background : Set b)
  (History : Set h) (Scalar : Set s) : Set (lsuc (j ⊔ b ⊔ h ⊔ s)) where
  field
    beta : Scale → Background → History → Scalar
    admissible : Scale → Background → History → Set (j ⊔ b ⊔ h)
    lower upper : Scalar
    LessEqual : Scalar → Scalar → Set s
    StrictlyPositive : Scalar → Set s
    positiveLower : StrictlyPositive lower
    uniformBounds : ∀ scale background history → admissible scale background history →
      LessEqual lower (beta scale background history) ×
      LessEqual (beta scale background history) upper
open BetaUniformityConjecture public
