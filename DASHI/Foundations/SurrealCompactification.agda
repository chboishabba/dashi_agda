module DASHI.Foundations.SurrealCompactification where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

data Empty : Set where

Not : Set → Set
Not A = A → Empty

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
cong f refl = refl

one two three four five six seven eight nine : Nat
one =
  suc zero
two =
  suc one
three =
  suc two
four =
  suc three
five =
  suc four
six =
  suc five
seven =
  suc six
eight =
  suc seven
nine =
  suc eight

data FiniteTritTower : Nat → Set where
  emptyTower :
    FiniteTritTower zero

  extendTower :
    {depth : Nat} →
    FiniteTritTower depth →
    Trit →
    FiniteTritTower (suc depth)

oneStepNegative :
  FiniteTritTower (suc zero)
oneStepNegative =
  extendTower emptyTower neg

oneStepZero :
  FiniteTritTower (suc zero)
oneStepZero =
  extendTower emptyTower zer

oneStepPositive :
  FiniteTritTower (suc zero)
oneStepPositive =
  extendTower emptyTower pos

infixr 5 _∷_

data Vec (A : Set) : Nat → Set where
  [] :
    Vec A zero

  _∷_ :
    {length : Nat} →
    A →
    Vec A length →
    Vec A (suc length)

vecLength :
  {A : Set} →
  {length : Nat} →
  Vec A length →
  Nat
vecLength [] =
  zero
vecLength (_ ∷ xs) =
  suc (vecLength xs)

vecLength-indexed :
  {A : Set} →
  {length : Nat} →
  (xs : Vec A length) →
  vecLength xs ≡ length
vecLength-indexed [] =
  refl
vecLength-indexed (_ ∷ xs) =
  cong suc (vecLength-indexed xs)

towerDepthValue :
  {depth : Nat} →
  FiniteTritTower depth →
  Nat
towerDepthValue emptyTower =
  zero
towerDepthValue (extendTower tower _) =
  suc (towerDepthValue tower)

towerDepthValue-indexed :
  {depth : Nat} →
  (tower : FiniteTritTower depth) →
  towerDepthValue tower ≡ depth
towerDepthValue-indexed emptyTower =
  refl
towerDepthValue-indexed (extendTower tower _) =
  cong suc (towerDepthValue-indexed tower)

towerToVec :
  {depth : Nat} →
  FiniteTritTower depth →
  Vec Trit depth
towerToVec emptyTower =
  []
towerToVec (extendTower tower trit) =
  trit ∷ towerToVec tower

vecToTower :
  {depth : Nat} →
  Vec Trit depth →
  FiniteTritTower depth
vecToTower [] =
  emptyTower
vecToTower (trit ∷ trits) =
  extendTower (vecToTower trits) trit

towerToVec-length :
  {depth : Nat} →
  (tower : FiniteTritTower depth) →
  vecLength (towerToVec tower) ≡ depth
towerToVec-length tower =
  vecLength-indexed (towerToVec tower)

vecToTower-depth :
  {depth : Nat} →
  (trits : Vec Trit depth) →
  towerDepthValue (vecToTower trits) ≡ depth
vecToTower-depth trits =
  towerDepthValue-indexed (vecToTower trits)

vecToTower∘towerToVec :
  {depth : Nat} →
  (tower : FiniteTritTower depth) →
  vecToTower (towerToVec tower) ≡ tower
vecToTower∘towerToVec emptyTower =
  refl
vecToTower∘towerToVec (extendTower tower trit) =
  cong
    (λ lowerTower → extendTower lowerTower trit)
    (vecToTower∘towerToVec tower)

towerToVec∘vecToTower :
  {depth : Nat} →
  (trits : Vec Trit depth) →
  towerToVec (vecToTower trits) ≡ trits
towerToVec∘vecToTower [] =
  refl
towerToVec∘vecToTower (trit ∷ trits) =
  cong
    (λ lowerTrits → trit ∷ lowerTrits)
    (towerToVec∘vecToTower trits)

infix 4 _≤_

data _≤_ : Nat → Nat → Set where
  z≤n :
    {n : Nat} →
    zero ≤ n

  s≤s :
    {m n : Nat} →
    m ≤ n →
    suc m ≤ suc n

≤-refl :
  (n : Nat) →
  n ≤ n
≤-refl zero =
  z≤n
≤-refl (suc n) =
  s≤s (≤-refl n)

≤-trans :
  {a b c : Nat} →
  a ≤ b →
  b ≤ c →
  a ≤ c
≤-trans z≤n _ =
  z≤n
≤-trans (s≤s a≤b) (s≤s b≤c) =
  s≤s (≤-trans a≤b b≤c)

≤-step :
  {m n : Nat} →
  m ≤ n →
  m ≤ suc n
≤-step z≤n =
  z≤n
≤-step (s≤s m≤n) =
  s≤s (≤-step m≤n)

≤-suc :
  (n : Nat) →
  n ≤ suc n
≤-suc n =
  ≤-step (≤-refl n)

truncateTower :
  {target source : Nat} →
  target ≤ source →
  FiniteTritTower source →
  FiniteTritTower target
truncateTower z≤n _ =
  emptyTower
truncateTower (s≤s target≤source) (extendTower tower trit) =
  extendTower (truncateTower target≤source tower) trit

truncateVec :
  {target source : Nat} →
  target ≤ source →
  Vec Trit source →
  Vec Trit target
truncateVec z≤n _ =
  []
truncateVec (s≤s target≤source) (trit ∷ trits) =
  trit ∷ truncateVec target≤source trits

truncateTower-depth :
  {target source : Nat} →
  (target≤source : target ≤ source) →
  (tower : FiniteTritTower source) →
  towerDepthValue (truncateTower target≤source tower) ≡ target
truncateTower-depth target≤source tower =
  towerDepthValue-indexed (truncateTower target≤source tower)

truncateVec-length :
  {target source : Nat} →
  (target≤source : target ≤ source) →
  (trits : Vec Trit source) →
  vecLength (truncateVec target≤source trits) ≡ target
truncateVec-length target≤source trits =
  vecLength-indexed (truncateVec target≤source trits)

truncateTower-vec-compatible :
  {target source : Nat} →
  (target≤source : target ≤ source) →
  (tower : FiniteTritTower source) →
  towerToVec (truncateTower target≤source tower)
  ≡
  truncateVec target≤source (towerToVec tower)
truncateTower-vec-compatible z≤n _ =
  refl
truncateTower-vec-compatible (s≤s target≤source) (extendTower tower trit) =
  cong
    (λ lowerTrits → trit ∷ lowerTrits)
    (truncateTower-vec-compatible target≤source tower)

truncateTower-id :
  {depth : Nat} →
  (tower : FiniteTritTower depth) →
  truncateTower (≤-refl depth) tower ≡ tower
truncateTower-id emptyTower =
  refl
truncateTower-id (extendTower tower trit) =
  cong
    (λ lowerTower → extendTower lowerTower trit)
    (truncateTower-id tower)

truncateVec-id :
  {depth : Nat} →
  (trits : Vec Trit depth) →
  truncateVec (≤-refl depth) trits ≡ trits
truncateVec-id [] =
  refl
truncateVec-id (trit ∷ trits) =
  cong
    (λ lowerTrits → trit ∷ lowerTrits)
    (truncateVec-id trits)

truncateTower-compose :
  {lower middle upper : Nat} →
  (lower≤middle : lower ≤ middle) →
  (middle≤upper : middle ≤ upper) →
  (tower : FiniteTritTower upper) →
  truncateTower lower≤middle (truncateTower middle≤upper tower)
  ≡
  truncateTower (≤-trans lower≤middle middle≤upper) tower
truncateTower-compose z≤n _ _ =
  refl
truncateTower-compose (s≤s lower≤middle) (s≤s middle≤upper) (extendTower tower trit) =
  cong
    (λ lowerTower → extendTower lowerTower trit)
    (truncateTower-compose lower≤middle middle≤upper tower)

truncateVec-compose :
  {lower middle upper : Nat} →
  (lower≤middle : lower ≤ middle) →
  (middle≤upper : middle ≤ upper) →
  (trits : Vec Trit upper) →
  truncateVec lower≤middle (truncateVec middle≤upper trits)
  ≡
  truncateVec (≤-trans lower≤middle middle≤upper) trits
truncateVec-compose z≤n _ _ =
  refl
truncateVec-compose (s≤s lower≤middle) (s≤s middle≤upper) (trit ∷ trits) =
  cong
    (λ lowerTrits → trit ∷ lowerTrits)
    (truncateVec-compose lower≤middle middle≤upper trits)

record BoundedFiniteTritTower (bound : Nat) : Set where
  constructor boundedFiniteTritTower
  field
    actualDepth :
      Nat

    actualWithinBound :
      actualDepth ≤ bound

    boundedTower :
      FiniteTritTower actualDepth

open BoundedFiniteTritTower public

truncateBoundedTower :
  {target bound : Nat} →
  (bounded : BoundedFiniteTritTower bound) →
  target ≤ actualDepth bounded →
  FiniteTritTower target
truncateBoundedTower bounded target≤actual =
  truncateTower target≤actual (boundedTower bounded)

truncateBoundedTower-within-bound :
  {target bound : Nat} →
  (bounded : BoundedFiniteTritTower bound) →
  (target≤actual : target ≤ actualDepth bounded) →
  target ≤ bound
truncateBoundedTower-within-bound bounded target≤actual =
  ≤-trans target≤actual (actualWithinBound bounded)

truncateBoundedTower-as-bounded :
  {target bound : Nat} →
  (bounded : BoundedFiniteTritTower bound) →
  (target≤actual : target ≤ actualDepth bounded) →
  BoundedFiniteTritTower bound
truncateBoundedTower-as-bounded {target} bounded target≤actual =
  boundedFiniteTritTower
    target
    (truncateBoundedTower-within-bound bounded target≤actual)
    (truncateBoundedTower bounded target≤actual)

truncateBoundedTower-depth :
  {target bound : Nat} →
  (bounded : BoundedFiniteTritTower bound) →
  (target≤actual : target ≤ actualDepth bounded) →
  towerDepthValue (truncateBoundedTower bounded target≤actual) ≡ target
truncateBoundedTower-depth bounded target≤actual =
  truncateTower-depth target≤actual (boundedTower bounded)

Depth9FiniteTritTower : Set
Depth9FiniteTritTower =
  FiniteTritTower nine

depth9≤depth9 :
  nine ≤ nine
depth9≤depth9 =
  ≤-refl nine

kappaToDepth9Tower :
  {kappaDepth : Nat} →
  nine ≤ kappaDepth →
  FiniteTritTower kappaDepth →
  Depth9FiniteTritTower
kappaToDepth9Tower nine≤kappa tower =
  truncateTower nine≤kappa tower

kappaToDepth9Vec :
  {kappaDepth : Nat} →
  nine ≤ kappaDepth →
  Vec Trit kappaDepth →
  Vec Trit nine
kappaToDepth9Vec nine≤kappa trits =
  truncateVec nine≤kappa trits

kappaToDepth9-depth :
  {kappaDepth : Nat} →
  (nine≤kappa : nine ≤ kappaDepth) →
  (tower : FiniteTritTower kappaDepth) →
  towerDepthValue (kappaToDepth9Tower nine≤kappa tower) ≡ nine
kappaToDepth9-depth nine≤kappa tower =
  truncateTower-depth nine≤kappa tower

kappaToDepth9-vec-compatible :
  {kappaDepth : Nat} →
  (nine≤kappa : nine ≤ kappaDepth) →
  (tower : FiniteTritTower kappaDepth) →
  towerToVec (kappaToDepth9Tower nine≤kappa tower)
  ≡
  kappaToDepth9Vec nine≤kappa (towerToVec tower)
kappaToDepth9-vec-compatible nine≤kappa tower =
  truncateTower-vec-compatible nine≤kappa tower

kappaToDepth9-id :
  (tower : Depth9FiniteTritTower) →
  kappaToDepth9Tower depth9≤depth9 tower ≡ tower
kappaToDepth9-id tower =
  truncateTower-id tower

record KappaToDepth9Receipt : Set₁ where
  constructor kappaToDepth9Receipt
  field
    kappaDepth :
      Nat

    depth9WithinKappa :
      nine ≤ kappaDepth

    kappaTower :
      FiniteTritTower kappaDepth

    depth9Tower :
      Depth9FiniteTritTower

    depth9Tower-is-truncation :
      depth9Tower ≡ kappaToDepth9Tower depth9WithinKappa kappaTower

    depth9Tower-depth :
      towerDepthValue depth9Tower ≡ nine

    depth9Tower-vec-compatible :
      towerToVec depth9Tower
      ≡
      kappaToDepth9Vec depth9WithinKappa (towerToVec kappaTower)

    boundedAtKappa :
      BoundedFiniteTritTower kappaDepth

    boundedAtKappa-is-source :
      actualDepth boundedAtKappa ≡ kappaDepth

    boundedAtNine :
      BoundedFiniteTritTower kappaDepth

    boundedAtNine-depth :
      towerDepthValue (boundedTower boundedAtNine) ≡ nine

    requiresExternalSurrealAuthority :
      Bool

    requiresExternalSurrealAuthority-is-false :
      requiresExternalSurrealAuthority ≡ false

    promotesTransfiniteBoundary :
      Bool

    promotesTransfiniteBoundary-is-false :
      promotesTransfiniteBoundary ≡ false

open KappaToDepth9Receipt public

canonicalKappaToDepth9Receipt :
  {kappaDepth : Nat} →
  (nine≤kappa : nine ≤ kappaDepth) →
  (tower : FiniteTritTower kappaDepth) →
  KappaToDepth9Receipt
canonicalKappaToDepth9Receipt nine≤kappa tower =
  record
    { kappaDepth =
        _
    ; depth9WithinKappa =
        nine≤kappa
    ; kappaTower =
        tower
    ; depth9Tower =
        kappaToDepth9Tower nine≤kappa tower
    ; depth9Tower-is-truncation =
        refl
    ; depth9Tower-depth =
        kappaToDepth9-depth nine≤kappa tower
    ; depth9Tower-vec-compatible =
        kappaToDepth9-vec-compatible nine≤kappa tower
    ; boundedAtKappa =
        boundedFiniteTritTower _ (≤-refl _) tower
    ; boundedAtKappa-is-source =
        refl
    ; boundedAtNine =
        boundedFiniteTritTower
          nine
          nine≤kappa
          (kappaToDepth9Tower nine≤kappa tower)
    ; boundedAtNine-depth =
        kappaToDepth9-depth nine≤kappa tower
    ; requiresExternalSurrealAuthority =
        false
    ; requiresExternalSurrealAuthority-is-false =
        refl
    ; promotesTransfiniteBoundary =
        false
    ; promotesTransfiniteBoundary-is-false =
        refl
    }

record InternalBoundedTruncationSurface : Set₁ where
  field
    Bound :
      Nat →
      Nat →
      Set

    boundImplies≤ :
      {target source : Nat} →
      Bound target source →
      target ≤ source

    boundedTruncateTower :
      {target source : Nat} →
      Bound target source →
      FiniteTritTower source →
      FiniteTritTower target

    boundedTruncateTower-is-internal :
      {target source : Nat} →
      (bound : Bound target source) →
      (tower : FiniteTritTower source) →
      boundedTruncateTower bound tower
      ≡
      truncateTower (boundImplies≤ bound) tower

    boundedTruncateVec :
      {target source : Nat} →
      Bound target source →
      Vec Trit source →
      Vec Trit target

    boundedTruncateVec-is-internal :
      {target source : Nat} →
      (bound : Bound target source) →
      (trits : Vec Trit source) →
      boundedTruncateVec bound trits
      ≡
      truncateVec (boundImplies≤ bound) trits

    requiresExternalSurrealAuthority :
      Bool

    requiresExternalSurrealAuthority-is-false :
      requiresExternalSurrealAuthority ≡ false

    promotesTransfiniteBoundary :
      Bool

    promotesTransfiniteBoundary-is-false :
      promotesTransfiniteBoundary ≡ false

open InternalBoundedTruncationSurface public

canonicalInternalBoundedTruncationSurface :
  InternalBoundedTruncationSurface
canonicalInternalBoundedTruncationSurface =
  record
    { Bound = _≤_
    ; boundImplies≤ = λ bound → bound
    ; boundedTruncateTower = λ bound tower →
        truncateTower bound tower
    ; boundedTruncateTower-is-internal = λ bound tower →
        refl
    ; boundedTruncateVec = λ bound trits →
        truncateVec bound trits
    ; boundedTruncateVec-is-internal = λ bound trits →
        refl
    ; requiresExternalSurrealAuthority = false
    ; requiresExternalSurrealAuthority-is-false = refl
    ; promotesTransfiniteBoundary = false
    ; promotesTransfiniteBoundary-is-false = refl
    }

record NoBoundary (Carrier : Set) : Set₁ where
  field
    BoundaryPredicate :
      Carrier → Set

    rejectsBoundary :
      (x : Carrier) →
      Not (BoundaryPredicate x)

open NoBoundary public

record SurrealApproximant : Set₁ where
  field
    towerDepth :
      Nat

    tower :
      FiniteTritTower towerDepth

    noBoundary :
      NoBoundary (FiniteTritTower towerDepth)

open SurrealApproximant public

record CompactificationErrorAuthoritySlot : Set₁ where
  field
    ErrorCarrier :
      Set

    zeroError :
      ErrorCarrier

    errorOrder :
      ErrorCarrier →
      ErrorCarrier →
      Set

    finiteApproximationErrorBound :
      {depth : Nat} →
      FiniteTritTower depth →
      ErrorCarrier

    compactificationRemainderBound :
      SurrealApproximant →
      ErrorCarrier

open CompactificationErrorAuthoritySlot public

record SurrealEmbeddingAuthoritySlot : Set₁ where
  field
    EmbeddedCarrier :
      Set

    embedFiniteTower :
      {depth : Nat} →
      FiniteTritTower depth →
      EmbeddedCarrier

    embeddingError :
      CompactificationErrorAuthoritySlot

    embeddingSoundnessAuthority :
      Set

open SurrealEmbeddingAuthoritySlot public

record TruncationAuthoritySlot : Set₁ where
  field
    TruncatedCarrier :
      Nat →
      Set

    truncateFiniteTower :
      (targetDepth sourceDepth : Nat) →
      FiniteTritTower sourceDepth →
      TruncatedCarrier targetDepth

    truncationError :
      CompactificationErrorAuthoritySlot

    truncationSoundnessAuthority :
      Set

open TruncationAuthoritySlot public

record CompactificationAuthoritySlot : Set₁ where
  field
    CompactifiedCarrier :
      Set

    compactifyApproximant :
      SurrealApproximant →
      CompactifiedCarrier

    compactificationError :
      CompactificationErrorAuthoritySlot

    compactificationSoundnessAuthority :
      Set

open CompactificationAuthoritySlot public

record SurrealMonsterPromotionFlags : Set where
  field
    surrealCompletionPromoted :
      Bool

    surrealCompletionPromoted-is-false :
      surrealCompletionPromoted ≡ false

    surrealArithmeticPromoted :
      Bool

    surrealArithmeticPromoted-is-false :
      surrealArithmeticPromoted ≡ false

    surrealOrderPromoted :
      Bool

    surrealOrderPromoted-is-false :
      surrealOrderPromoted ≡ false

    transfiniteLimitPromoted :
      Bool

    transfiniteLimitPromoted-is-false :
      transfiniteLimitPromoted ≡ false

    compactificationTheoremPromoted :
      Bool

    compactificationTheoremPromoted-is-false :
      compactificationTheoremPromoted ≡ false

    monsterIsomorphismPromoted :
      Bool

    monsterIsomorphismPromoted-is-false :
      monsterIsomorphismPromoted ≡ false

    monsterAutomorphismPromoted :
      Bool

    monsterAutomorphismPromoted-is-false :
      monsterAutomorphismPromoted ≡ false

    monsterMoonshineBridgePromoted :
      Bool

    monsterMoonshineBridgePromoted-is-false :
      monsterMoonshineBridgePromoted ≡ false

open SurrealMonsterPromotionFlags public

allSurrealMonsterPromotionFlagsFalse :
  SurrealMonsterPromotionFlags
allSurrealMonsterPromotionFlagsFalse =
  record
    { surrealCompletionPromoted = false
    ; surrealCompletionPromoted-is-false = refl
    ; surrealArithmeticPromoted = false
    ; surrealArithmeticPromoted-is-false = refl
    ; surrealOrderPromoted = false
    ; surrealOrderPromoted-is-false = refl
    ; transfiniteLimitPromoted = false
    ; transfiniteLimitPromoted-is-false = refl
    ; compactificationTheoremPromoted = false
    ; compactificationTheoremPromoted-is-false = refl
    ; monsterIsomorphismPromoted = false
    ; monsterIsomorphismPromoted-is-false = refl
    ; monsterAutomorphismPromoted = false
    ; monsterAutomorphismPromoted-is-false = refl
    ; monsterMoonshineBridgePromoted = false
    ; monsterMoonshineBridgePromoted-is-false = refl
    }

record SurrealCompactificationBoundarySurface : Set₂ where
  field
    ApproximantCarrier :
      Set₁

    approximantCarrier-is-surrealApproximant :
      ApproximantCarrier ≡ SurrealApproximant

    embeddingAuthority :
      SurrealEmbeddingAuthoritySlot

    truncationAuthority :
      TruncationAuthoritySlot

    internalBoundedTruncationSurface :
      InternalBoundedTruncationSurface

    compactificationAuthority :
      CompactificationAuthoritySlot

    promotionFlags :
      SurrealMonsterPromotionFlags

    promotionFlags-are-fail-closed :
      promotionFlags ≡ allSurrealMonsterPromotionFlagsFalse

open SurrealCompactificationBoundarySurface public

record FailClosedSurrealBoundaryAssumptions : Set₂ where
  field
    approximantsAreFiniteTritTowers :
      Set

    noBoundaryRequiredForApproximants :
      Set

    embeddingRequiresAuthority :
      Set

    truncationRequiresAuthority :
      Set

    compactificationErrorRequiresAuthority :
      Set

    promotionSurface :
      SurrealCompactificationBoundarySurface

open FailClosedSurrealBoundaryAssumptions public
