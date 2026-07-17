module DASHI.Physics.YangMills.BalabanEndpointDeterminantPrefixBridge where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Nat.Base using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Empty using (⊥)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _-ℝ_ ; _≤ℝ_ ; ≤ℝ-trans ; +-mono-≤ ; +-comm ; +-assoc ; subSelf ; subAddCancelMiddle ; trans ; cong ; +-identityˡ )
open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId ; VerificationStatus ; openTarget )
open import DASHI.Physics.YangMills.BalabanInverseSquareCouplingBudget using
  ( InverseSquareThresholdControlsCoupling
  ; BalabanBetaPrefixBound
  ; betaPrefixSum
  )
open import DASHI.Physics.YangMills.BalabanEffectiveCouplingTrajectory using
  ( BalabanInverseSquareCouplingStep
  ; betaCorrection
  ; inverseSquaredCoupling
  )

sumShells : (ℕ → ℝ) → ℕ → ℝ
sumShells f zero = 0ℝ
sumShells f (suc k) = sumShells f k +ℝ f (suc k)

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

sumShells≡betaPrefixSum :
  (step : BalabanInverseSquareCouplingStep) →
  ∀ k →
  sumShells (betaCorrection step) k ≡ betaPrefixSum step k
sumShells≡betaPrefixSum step zero = refl
sumShells≡betaPrefixSum step (suc k) =
  cong (λ x → x +ℝ betaCorrection step (suc k)) (sumShells≡betaPrefixSum step k)

≤-step : ∀ {m n} → suc m ≤ n → m ≤ n
≤-step {zero} {zero} ()
≤-step {zero} {suc n} p = z≤n
≤-step {suc m} {zero} ()
≤-step {suc m} {suc n} (s≤s p) = s≤s (≤-step p)

record EndpointDeterminantPrefixData
    (K : ℕ)
    (step : BalabanInverseSquareCouplingStep) : Set₁ where
  field
    gaussianShell : ℕ → ℝ
    interactionShell : ℕ → ℝ
    correctionShell : ℕ → ℝ
    endpointDeterminant : ℕ → ℝ

    -- Shell decomposition: betaCorrection j = gaussianShell j + interactionShell j
    totalBeta :
      ∀ j →
      suc j ≤ K →
      betaCorrection step (suc j)
        ≡ gaussianShell (suc j) +ℝ interactionShell (suc j)

    -- Verified shell identity: gaussianShell (suc j) = (endpointDeterminant (suc j) - endpointDeterminant j) + correctionShell (suc j)
    shellDecomposition :
      ∀ j →
      suc j ≤ K →
      gaussianShell (suc j)
        ≡ (endpointDeterminant (suc j) -ℝ endpointDeterminant j)
            +ℝ correctionShell (suc j)

open EndpointDeterminantPrefixData public

rearrangeAdd4 : ∀ a b c d → (a +ℝ b) +ℝ (c +ℝ d) ≡ (a +ℝ c) +ℝ (b +ℝ d)
rearrangeAdd4 a b c d =
  let
    p1 = +-assoc a b (c +ℝ d)
    p2 = sym (+-assoc b c d)
    p3 = +-comm b c
    p4 = +-assoc c b d
    p5 = trans p2 (trans (cong (λ x → x +ℝ d) p3) p4)
    p6 = cong (λ x → a +ℝ x) p5
    p7 = sym (+-assoc a c (b +ℝ d))
  in
    trans p1 (trans p6 p7)

rearrangeTelescope : ∀ a b d c k → ((a -ℝ d) +ℝ c) +ℝ ((b -ℝ a) +ℝ k) ≡ (b -ℝ d) +ℝ (c +ℝ k)
rearrangeTelescope a b d c k =
  let
    p1 = +-assoc (a -ℝ d) c ((b -ℝ a) +ℝ k)
    p2 = +-comm c ((b -ℝ a) +ℝ k)
    p3 = +-assoc (b -ℝ a) k c
    p4 = +-comm k c
    p5 = cong (λ x → (b -ℝ a) +ℝ x) p4
    p6 = trans p2 (trans p3 p5)
    p7 = cong (λ x → (a -ℝ d) +ℝ x) p6
    p8 = sym (+-assoc (a -ℝ d) (b -ℝ a) (c +ℝ k))
    p9 = +-comm (a -ℝ d) (b -ℝ a)
    p10 = subAddCancelMiddle b a d
    p11 = trans p9 p10
    p12 = cong (λ x → x +ℝ (c +ℝ k)) p11
  in
    trans p1 (trans p7 (trans p8 p12))

sumShellsTotalBeta :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (prefixData : EndpointDeterminantPrefixData K step) →
  ∀ k → k ≤ K →
  sumShells (betaCorrection step) k
    ≡ sumShells (gaussianShell prefixData) k
        +ℝ sumShells (interactionShell prefixData) k
sumShellsTotalBeta K step prefixData zero k≤K =
  let
    p1 = +-identityˡ 0ℝ
  in
    sym p1
sumShellsTotalBeta K step prefixData (suc k) k≤K =
  let
    gS = gaussianShell prefixData
    iS = interactionShell prefixData
    tB = totalBeta prefixData k k≤K
    ih = sumShellsTotalBeta K step prefixData k (≤-step k≤K)
    p1 = cong (λ x → sumShells (betaCorrection step) k +ℝ x) tB
    p2 = cong (λ x → x +ℝ (gS (suc k) +ℝ iS (suc k))) ih
    p3 = rearrangeAdd4 (sumShells gS k) (sumShells iS k) (gS (suc k)) (iS (suc k))
  in
    trans p1 (trans p2 p3)

gaussianPrefixTelescopes :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (prefixData : EndpointDeterminantPrefixData K step) →
  ∀ k → k ≤ K →
  sumShells (gaussianShell prefixData) k
    ≡ (endpointDeterminant prefixData k
        -ℝ endpointDeterminant prefixData zero)
        +ℝ sumShells (correctionShell prefixData) k
gaussianPrefixTelescopes K step prefixData zero k≤K =
  let
    eD = endpointDeterminant prefixData
    p1 = subSelf (eD zero)
    p2 = +-identityˡ 0ℝ
  in
    sym (trans (cong (λ x → x +ℝ 0ℝ) p1) p2)
gaussianPrefixTelescopes K step prefixData (suc k) k≤K =
  let
    gS = gaussianShell prefixData
    cS = correctionShell prefixData
    eD = endpointDeterminant prefixData
    sD = shellDecomposition prefixData k k≤K
    ih = gaussianPrefixTelescopes K step prefixData k (≤-step k≤K)
    p1 = cong (λ x → ((eD k -ℝ eD zero) +ℝ sumShells cS k) +ℝ x) sD
    p2 = cong (λ x → x +ℝ gS (suc k)) ih
    p3 = rearrangeTelescope (eD k) (eD (suc k)) (eD zero) (sumShells cS k) (cS (suc k))
  in
    trans p2 (trans p1 p3)

betaSumEquality :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (prefixData : EndpointDeterminantPrefixData K step) →
  ∀ k → k ≤ K →
  betaPrefixSum step k
    ≡ ((endpointDeterminant prefixData k
        -ℝ endpointDeterminant prefixData zero)
        +ℝ sumShells (correctionShell prefixData) k)
        +ℝ sumShells (interactionShell prefixData) k
betaSumEquality K step prefixData k k≤K =
  let
    iS = interactionShell prefixData
    p0 = sym (sumShells≡betaPrefixSum step k)
    p1 = sumShellsTotalBeta K step prefixData k k≤K
    p2 = gaussianPrefixTelescopes K step prefixData k k≤K
    p3 = cong (λ x → x +ℝ sumShells iS k) p2
  in
    trans p0 (trans p1 p3)

combineBounds :
  ∀ {a b c x y z} →
  a ≤ℝ x →
  b ≤ℝ y →
  c ≤ℝ z →
  (a +ℝ b) +ℝ c ≤ℝ (x +ℝ y) +ℝ z
combineBounds {a} {b} {c} {x} {y} {z} ab bc cd =
  +-mono-≤ (+-mono-≤ ab bc) cd

≤-replace-left : ∀ {a b c : ℝ} → a ≡ b → b ≤ℝ c → a ≤ℝ c
≤-replace-left refl bc = bc

endpointDeterminantToBetaPrefix :
  (K : ℕ) →
  (step : BalabanInverseSquareCouplingStep) →
  (prefixData : EndpointDeterminantPrefixData K step) →
  {γ : ℝ} →
  (threshold : InverseSquareThresholdControlsCoupling K γ step) →
  (endpointUpper : ℕ → ℝ) →
  (correctionUpper : ℕ → ℝ) →
  (interactionUpper : ℕ → ℝ) →
  (endpointPrefixUpper :
    ∀ k → k ≤ K →
    (endpointDeterminant prefixData k
      -ℝ endpointDeterminant prefixData zero)
      ≤ℝ endpointUpper k) →
  (correctionPrefixBound :
    ∀ k → k ≤ K →
    sumShells (correctionShell prefixData) k
      ≤ℝ correctionUpper k) →
  (interactionPrefixBound :
    ∀ k → k ≤ K →
    sumShells (interactionShell prefixData) k
      ≤ℝ interactionUpper k) →
  (bareCouplingBudgetHypothesis :
    ∀ k → k ≤ K →
    InverseSquareThresholdControlsCoupling.gammaInverseSquare threshold
      +ℝ ((endpointUpper k +ℝ correctionUpper k) +ℝ interactionUpper k)
      ≤ℝ inverseSquaredCoupling step zero) →
  (sourceAuthorityId : SourceAuthorityId) →
  (theoremLocator : String) →
  (status : VerificationStatus) →
  (noClayPromotion : clayYangMillsPromoted ≡ false) →
  BalabanBetaPrefixBound K step threshold
endpointDeterminantToBetaPrefix K step prefixData threshold endpointUpper correctionUpper interactionUpper endpointPrefixUpper correctionPrefixBound interactionPrefixBound bareCouplingBudgetHypothesis sourceAuth loc stat noClay =
  record
    { prefixMajorant = λ k → (endpointUpper k +ℝ correctionUpper k) +ℝ interactionUpper k
    ; betaPrefixControlled = λ k k≤K →
        let
          eq = betaSumEquality K step prefixData k k≤K
          ineq = combineBounds (endpointPrefixUpper k k≤K) (correctionPrefixBound k k≤K) (interactionPrefixBound k k≤K)
        in
          ≤-replace-left eq ineq
    ; bareCouplingBudget = bareCouplingBudgetHypothesis
    ; sourceAuthorityId = sourceAuth
    ; theoremLocator = loc
    ; status = stat
    ; noClayPromotion = noClay
    }
