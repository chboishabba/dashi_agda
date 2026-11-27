module DASHI.Analysis.BishopOriginalMachinCayleyEndpointExact where

-- Original K05 endpoint: the normalized actual phase has O(h^2)
-- increments, hence is constant on the existing clipped equal mesh.
-- No derivative-of-limit, mean-value theorem or ODE uniqueness axiom.
open import Agda.Builtin.Nat as N using (Nat; zero; suc; _+_)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised as Q using (_/_; 0ℚᵘ; 1ℚᵘ)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Data.Rational.Unnormalised.Properties as QP
import ExtraProperties as Extra
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopOriginalMachinAtanSmallPhaseExact as S
import DASHI.Analysis.BishopOriginalMachinAtanSecondOrderExact as Atan2
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineTermParityExact as Sign
open S using (Point; point; x; nn; inside; atan; d; denom; two; half; absNN)
import DASHI.Analysis.BishopOriginalMachinCayleyConservedPhaseExact as H
open H using (Box; boxCong; boxAdd; scale)
import DASHI.Analysis.BishopSetoidComplexExact as C
open C using (_≈C_; _*C_; _+C_; _-C_)
import DASHI.Foundations.BishopMachinArctanConstructionExact as A
import DASHI.Analysis.BishopOriginalMachinAtanFiniteDerivativeExact as AD
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Exponents
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Analysis.BishopOriginalClippedEqualMeshExact as Clip
import DASHI.Analysis.BishopOriginalClippedMeshDefectRemainderExact as ClipSum
import DASHI.Analysis.BishopOriginalNegativeLogFiniteWeightedMeshRecurrenceExact as Mesh
import DASHI.Analysis.BishopOriginalFactorIncrementFiniteTelescopeExact as Walk
import DASHI.Analysis.BishopNaturalScaleEmbeddingBridgeExact as Scale
import DASHI.Analysis.BishopSetoidPowerDerivativeNormalisationExact as NS
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NatReal
import DASHI.Foundations.BishopNatRealReciprocalSquareBaselExact as Recip
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq
import DASHI.Analysis.BishopSquareZeroReflectsSetoidZeroExact as Zero
import DASHI.Foundations.BishopTrigAtZeroExact as Origin
import DASHI.Foundations.BishopSineCosineSetoidCongruenceExact as Trig
import DASHI.Foundations.BishopMachinExistingCayleyReuseExact as Cayley
import DASHI.Analysis.BishopMachinRationalCayleyToOriginalComplexExact as Bridge
import DASHI.Analysis.BishopMachinTwoPointCayleyCompositionExact as Two
import DASHI.Analysis.BishopMachinFirstPositiveSineZeroFromNativePhaseExact as First
import DASHI.Analysis.BishopMachinCayleyHalfPhaseToFirstZeroExact as HalfPhase
import DASHI.Analysis.BishopMachinCayleyNativeProductFirstZeroExact as Native
import DASHI.Analysis.BishopMachinQuarterPhaseQuadruplicationAlgebraExact as Quad
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
import DASHI.Moonshine.BishopMachinSetoidComplexInstanceExact as Route

atanPartialCong : ∀ a b → a ≃ b → ∀ n →
  Seq.SeriesOf (A.atanSignedTerm a) n ≃ Seq.SeriesOf (A.atanSignedTerm b) n
atanPartialCong a b eq zero = P.≃-refl
atanPartialCong a b eq (suc n) = P.+-cong (atanPartialCong a b eq n)
  (P.*-congˡ (P.*-congˡ (P.pow-cong (Exponents.oddExponent n) eq)))

atanValueCong : ∀ a b ai bi → a ≃ b →
  A.bishopAtanHalfBall a ai ≃ A.bishopAtanHalfBall b bi
atanValueCong a b ai bi eq = Seq.uniqueness-of-limits
  (Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀ (λ {(suc n) → atanPartialCong a b eq (suc n)})
    (A.bishopAtanHalfBall a ai , A.bishopAtanHalfBallConverges a ai))
  (A.bishopAtanHalfBallConverges b bi)

atanCong : ∀ p q → x p ≃ x q → atan p ≃ atan q
atanCong p q = atanValueCong (x p) (x q) (S.asHalf p) (S.asHalf q)

-- Inverse uniqueness by cancellation on the actual derivative values.
dCandidate : ∀ p v → denom (x p) * v ≃ R.1ℝ → d p ≃ v
dCandidate p v cancels =
  let i = d p
      a = denom (x p)
      open P.ℝ-Solver
  in P.≃-trans (P.≃-symm (P.*-identityʳ i))
    (P.≃-trans (P.*-congˡ (P.≃-symm cancels))
      (P.≃-trans
        (solve 3 (λ i a v → i ⊗ (a ⊗ v) ⊜ (a ⊗ i) ⊗ v) P.≃-refl i a v)
        (P.≃-trans (P.*-congʳ (S.dCancels p)) (P.*-identityˡ v))))

denomCong : ∀ a b → a ≃ b → denom a ≃ denom b
denomCong a b eq = P.+-cong P.≃-refl (P.*-cong eq eq)

dCong : ∀ p q → x p ≃ x q → d p ≃ d q
dCong p q eq = dCandidate p (d q)
  (P.≃-trans (P.*-congʳ (denomCong (x p) (x q) eq)) (S.dCancels q))

zeroPoint : Point
zeroPoint = point R.0ℝ P.nonNeg0 (P.nonNegx⇒0≤x Atan2.halfNN)

zeroPower : ∀ n → R.pow R.0ℝ (suc n) ≃ R.0ℝ
zeroPower n = let open P.ℝ-Solver in
  solve 1 (λ p → p ⊗ Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl (R.pow R.0ℝ n)

atanZeroTerm : ∀ n → A.atanSignedTerm R.0ℝ n ≃ R.0ℝ
atanZeroTerm n rewrite AD.oddExponentIsSuccessorEven n =
  P.≃-trans (P.*-congˡ (P.*-congˡ (zeroPower (Exponents.evenExponent n))))
    (let open P.ℝ-Solver in solve 2
      (λ a b → a ⊗ (b ⊗ Κ Q.0ℚᵘ) ⊜ Κ Q.0ℚᵘ) P.≃-refl
      (Sign.alternatingSign n) ((A.inverseOddRational n) ⋆))

atanZeroPartial : ∀ n → Seq.SeriesOf (A.atanSignedTerm R.0ℝ) n ≃ R.0ℝ
atanZeroPartial zero = P.≃-refl
atanZeroPartial (suc n) = P.≃-trans
  (P.+-cong (atanZeroPartial n) (atanZeroTerm n)) (P.+-identityˡ R.0ℝ)

atanZero : atan zeroPoint ≃ R.0ℝ
atanZero = Seq.uniqueness-of-limits (A.bishopAtanHalfBallConverges R.0ℝ (S.asHalf zeroPoint))
  (Seq.xₙ≃c⇒xₙ→c (λ {(suc n) → atanZeroPartial (suc n)}))

dZero : d zeroPoint ≃ R.1ℝ
dZero = dCandidate zeroPoint R.1ℝ
  (let open P.ℝ-Solver in solve 0
    ((Κ Q.1ℚᵘ ⊕ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊗ Κ Q.1ℚᵘ ⊜ Κ Q.1ℚᵘ) P.≃-refl)

constantBoundZero : ∀ a → (b : Nat → ℝ) →
  Seq._ConvergesTo_ b R.0ℝ → (∀ n → ∣ a ∣ ≤ b n) → a ≃ R.0ℝ
constantBoundZero a b conv bound = Zero.nativeAbsoluteZeroImpliesZero a
  (P.≤-antisym
    (Seq.xₙ≤yₙ⇒limxₙ≤limyₙ bound (∣ a ∣ , Power.constantConverges (∣ a ∣)) (R.0ℝ , conv))
    (P.nonNegx⇒0≤x (P.nonNeg∣x∣ a)))

differenceZero : ∀ a b → (a - b) ≃ R.0ℝ → a ≃ b
differenceZero a b eq = P.≃-trans
  (let open P.ℝ-Solver in solve 2 (λ a b → a ⊜ (a ⊖ b) ⊕ b) P.≃-refl a b)
  (P.≃-trans (P.+-cong eq P.≃-refl) (P.+-identityˡ b))

clippedBelow : ∀ cells h → R.NonNegative h → ∀ j →
  Clip.sourceClippedConstantSteps cells h j ≤ h
clippedBelow zero h hn j = P.nonNegx⇒0≤x hn
clippedBelow (suc cells) h hn zero = P.≤-refl
clippedBelow (suc cells) h hn (suc j) = clippedBelow cells h hn j

refinement : Nat → Nat
refinement n = 15 N.+ n

recipSmall : ∀ n → (Recip.reciprocalNatRational (refinement n) ⋆) ≤ S.tiny
recipSmall n = P.p≤q⇒p⋆≤q⋆ (Recip.reciprocalNatRational (refinement n)) (+ 1 / 16)
  (Extra.q≤r⇒+p/r≤+p/q 1 16 (suc (refinement n)) (NP.m≤m+n 16 n))

stepSmall : ∀ p n → Clip.sourceEqualStep (x p) (refinement n) ≤ S.tiny
stepSmall p n = P.≤-trans
  (P.≤-respʳ-≃ (P.*-identityˡ (Recip.reciprocalNatRational (refinement n) ⋆))
    (P.*-monoʳ-≤-nonNeg (H.xOne p) (Recip.reciprocalNonnegative (refinement n))))
  (recipSmall n)

constant204 : ℝ
constant204 = (+ 204 / 1) ⋆

budgetTerm : ℝ → ℝ
budgetTerm h = constant204 * (h * h)

-- Original clipped finite sum, not a mesh convergence assumption.
meshBudgetRead : ∀ p n →
  Walk.sumFinite (λ j → budgetTerm (Clip.sourceClippedEqualSteps (x p) n j)) (suc n)
  ≃ constant204 * (x p * Clip.sourceEqualStep (x p) n)
meshBudgetRead p n =
  let h = Clip.sourceEqualStep (x p) n
      c = NatReal.natReal (suc n)
      cTimesH = P.≃-trans (P.≃-symm (Scale.recursiveScaleIsEmbeddedNaturalMultiply (suc n) h))
        (P.≃-trans (P.≃-symm (Clip.originalClippedMeshEndpointIsNatScale h (suc n)))
          (Clip.originalClippedEqualMeshEndpointIsX (x p) n))
      open P.ℝ-Solver
  in P.≃-trans (ClipSum.originalClippedFiniteSumIsNatScale budgetTerm h (suc n))
    (P.≃-trans (Scale.recursiveScaleIsEmbeddedNaturalMultiply (suc n) (budgetTerm h))
      (P.≃-trans
        (solve 2 (λ c h → c ⊗ (Κ (+ 204 / 1) ⊗ (h ⊗ h))
          ⊜ Κ (+ 204 / 1) ⊗ ((c ⊗ h) ⊗ h)) P.≃-refl c h)
        (P.*-congˡ (P.*-congʳ cTimesH))))

refinedStepConverges : ∀ p →
  Seq._ConvergesTo_ (λ n → Clip.sourceEqualStep (x p) (refinement n)) R.0ℝ
refinedStepConverges p = Seq.xₙ⊆yₙ∧yₙ→y⇒xₙ→y
  (Seq.subseq* (refinement , (λ n → P.≃-refl) , (λ n → NP.n<1+n (refinement n))))
  (R.0ℝ , ClipSum.originalEqualStepConvergesToZero (x p))

meshBudget : Point → Nat → ℝ
meshBudget p n = constant204 * (x p * Clip.sourceEqualStep (x p) (refinement n))

meshBudgetConverges : ∀ p → Seq._ConvergesTo_ (meshBudget p) R.0ℝ
meshBudgetConverges p =
  Seq.xₙ→x∧x≃y⇒xₙ→y
    (Seq.xₙyₙ→x₀y₀ (constant204 , Power.constantConverges constant204)
      (x p * R.0ℝ , Seq.xₙyₙ→x₀y₀ (x p , Power.constantConverges (x p))
        (R.0ℝ , refinedStepConverges p)))
    (let open P.ℝ-Solver in solve 1
      (λ x → Κ (+ 204 / 1) ⊗ (x ⊗ Κ Q.0ℚᵘ) ⊜ Κ Q.0ℚᵘ) P.≃-refl (x p))

module At (inputs : Round11.BishopCutset) where
  module Phase = H.At inputs
  T = Route.machinTranscendentals inputs

  phaseCong : ∀ p q → x p ≃ x q → Phase.phase p ≈C Phase.phase q
  phaseCong p q eq =
    let a = P.*-congˡ (atanCong p q eq) in
    C.complex-equivalent (Trig.bishopCosCongruent (Round11.concreteTermIdentification inputs) a)
      (Trig.bishopSinCongruent (Round11.concreteTermIdentification inputs) a)

  HC : ∀ p q → x p ≃ x q → Phase.H p ≈C Phase.H q
  HC p q eq = C.mulCongruent (phaseCong p q eq)
    (C.complex-equivalent
      (P.*-cong (dCong p q eq) (P.+-cong P.≃-refl (P.-‿cong (P.*-cong eq eq))))
      (P.*-cong (dCong p q eq) (P.-‿cong (P.*-congˡ eq))))

  phaseZero : Phase.phase zeroPoint ≈C C.oneC
  phaseZero =
    let eq = P.≃-trans (P.*-congˡ atanZero)
          (let open P.ℝ-Solver in solve 0 (Κ (+ 2 / 1) ⊗ Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl)
        ident = Round11.concreteTermIdentification inputs
    in C.complex-equivalent
      (P.≃-trans (Trig.bishopCosCongruent ident eq) (Origin.round11CosineAtZero inputs))
      (P.≃-trans (Trig.bishopSinCongruent ident eq) (Origin.round11SineAtZero inputs))

  HZero : Phase.H zeroPoint ≈C C.oneC
  HZero = C.≈C-trans
    (C.mulCongruent phaseZero
      (C.complex-equivalent
        (P.≃-trans (P.*-congʳ dZero)
          (let open P.ℝ-Solver in solve 0
            (Κ Q.1ℚᵘ ⊗ (Κ Q.1ℚᵘ ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊜ Κ Q.1ℚᵘ) P.≃-refl))
        (P.≃-trans (P.*-congʳ dZero)
          (let open P.ℝ-Solver in solve 0
            (Κ Q.1ℚᵘ ⊗ (⊝ (Κ (+ 2 / 1) ⊗ Κ Q.0ℚᵘ)) ⊜ Κ Q.0ℚᵘ) P.≃-refl))))
    (C.complex-equivalent
      (let open P.ℝ-Solver in solve 0
        (Κ Q.1ℚᵘ ⊗ Κ Q.1ℚᵘ ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ ⊜ Κ Q.1ℚᵘ) P.≃-refl)
      (let open P.ℝ-Solver in solve 0
        (Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.0ℚᵘ ⊗ Κ Q.1ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl))

  zeroBox : ∀ z → Box (z -C z) R.0ℝ
  zeroBox z = boxCong
    (C.complex-equivalent
      (let open P.ℝ-Solver in solve 1 (λ a → a ⊖ a ⊜ Κ Q.0ℚᵘ) P.≃-refl (C.re z))
      (let open P.ℝ-Solver in solve 1 (λ a → a ⊖ a ⊜ Κ Q.0ℚᵘ) P.≃-refl (C.im z)))
    (P.≤-reflexive (absNN P.nonNeg0) , P.≤-reflexive (absNN P.nonNeg0))

  telescope : ∀ a b c → (c -C a) ≈C ((b -C a) +C (c -C b))
  telescope a b c = C.complex-equivalent
    (let open P.ℝ-Solver in solve 3
      (λ a b c → c ⊖ a ⊜ (b ⊖ a) ⊕ (c ⊖ b)) P.≃-refl (C.re a) (C.re b) (C.re c))
    (let open P.ℝ-Solver in solve 3
      (λ a b c → c ⊖ a ⊜ (b ⊖ a) ⊕ (c ⊖ b)) P.≃-refl (C.im a) (C.im b) (C.im c))

  module MeshAt (p : Point) (n : Nat) where
    k = refinement n
    steps = Clip.sourceClippedEqualSteps (x p) k
    v : Nat → Point
    v j = point (Mesh.sourceVertex steps j)
      (Clip.originalClippedEqualMeshVertexNonnegative (x p) k (nn p) j)
      (P.≤-trans (Clip.originalClippedEqualMeshVertexBelowX (x p) k (nn p) j) (inside p))

    stepNN : ∀ j → R.NonNegative (steps j)
    stepNN = Clip.originalClippedEqualMeshStepNonnegative (x p) k (nn p)

    stepTiny : ∀ j → steps j ≤ S.tiny
    stepTiny j = P.≤-trans
      (clippedBelow (suc k) (Clip.sourceEqualStep (x p) k)
        (P.nonNegx,y⇒nonNegx*y (nn p) (Recip.reciprocalNonnegative k)) j)
      (stepSmall p n)

    cellBound : ∀ j →
      Box (Phase.H (v (suc j)) -C Phase.H (v j)) (budgetTerm (steps j))
    cellBound j =
      let module Cell = Phase.Step (v j) (steps j) (stepNN j) (stepTiny j)
            (nn (v (suc j))) (inside (v (suc j)))
      in Cell.quadraticIncrement

    walkBound : ∀ j →
      Box (Phase.H (v j) -C Phase.H (v zero)) (Walk.sumFinite (λ i → budgetTerm (steps i)) j)
    walkBound zero = zeroBox (Phase.H (v zero))
    walkBound (suc j) = boxCong
      (telescope (Phase.H (v zero)) (Phase.H (v j)) (Phase.H (v (suc j))))
      (boxAdd (walkBound j) (cellBound j))

    endpointBound : Box (Phase.H p -C Phase.H zeroPoint) (meshBudget p n)
    endpointBound = H.boxBudgetCong (meshBudgetRead p k)
      (boxCong (C.subCongruent
        (HC p (v (suc k)) (P.≃-symm (Clip.originalClippedEqualMeshEndpointIsX (x p) k)))
        (HC zeroPoint (v zero) P.≃-refl))
        (walkBound (suc k)))

  conserved : ∀ p → Phase.H p ≈C C.oneC
  conserved p =
    let z = Phase.H p
        o = Phase.H zeroPoint
        real = constantBoundZero (C.re z - C.re o) (meshBudget p) (meshBudgetConverges p)
          (λ n → proj₁ (MeshAt.endpointBound p n))
        imag = constantBoundZero (C.im z - C.im o) (meshBudget p) (meshBudgetConverges p)
          (λ n → proj₂ (MeshAt.endpointBound p n))
    in C.≈C-trans (C.complex-equivalent
      (differenceZero (C.re z) (C.re o) real) (differenceZero (C.im z) (C.im o) imag)) HZero

  cayley : Point → C.BishopComplex
  cayley p = C.complex (d p * (R.1ℝ - x p * x p)) (d p * (two * x p))

  cayleyUnit : ∀ p → C.re (cayley p) * C.re (cayley p) + C.im (cayley p) * C.im (cayley p) ≃ R.1ℝ
  cayleyUnit p =
    P.≃-trans (let open P.ℝ-Solver in solve 2
      (λ d x → (d ⊗ (Κ Q.1ℚᵘ ⊖ x ⊗ x)) ⊗ (d ⊗ (Κ Q.1ℚᵘ ⊖ x ⊗ x))
        ⊕ (d ⊗ (Κ (+ 2 / 1) ⊗ x)) ⊗ (d ⊗ (Κ (+ 2 / 1) ⊗ x))
        ⊜ ((Κ Q.1ℚᵘ ⊕ x ⊗ x) ⊗ d) ⊗ ((Κ Q.1ℚᵘ ⊕ x ⊗ x) ⊗ d))
      P.≃-refl (d p) (x p))
      (P.≃-trans (P.*-cong (S.dCancels p) (S.dCancels p)) (P.*-identityˡ R.1ℝ))

  HRead : ∀ p → Phase.H p ≈C (Phase.phase p *C C.conjugate (cayley p))
  HRead p = C.mulCongruent (C.≈C-refl _)
    (C.complex-equivalent P.≃-refl
      (let open P.ℝ-Solver in solve 2
        (λ d x → d ⊗ (⊝ (Κ (+ 2 / 1) ⊗ x)) ⊜ ⊝ (d ⊗ (Κ (+ 2 / 1) ⊗ x)))
        P.≃-refl (d p) (x p)))

  recover : ∀ z w →
    (C.re w * C.re w + C.im w * C.im w) ≃ R.1ℝ →
    (z *C C.conjugate w) ≈C C.oneC → z ≈C w
  recover (C.complex c s) (C.complex a b) unit h =
    C.complex-equivalent
      (P.≃-trans (P.≃-symm (P.*-identityʳ c))
        (P.≃-trans (P.*-congˡ (P.≃-symm unit))
          (P.≃-trans
            (let open P.ℝ-Solver in solve 4
              (λ c s a b → c ⊗ (a ⊗ a ⊕ b ⊗ b) ⊜
                a ⊗ (c ⊗ a ⊖ s ⊗ (⊝ b)) ⊖ b ⊗ (c ⊗ (⊝ b) ⊕ s ⊗ a))
              P.≃-refl c s a b)
            (P.≃-trans
              (P.+-cong (P.*-congˡ (C.reEquivalent h)) (P.-‿cong (P.*-congˡ (C.imEquivalent h))))
              (let open P.ℝ-Solver in solve 2
                (λ a b → a ⊗ Κ Q.1ℚᵘ ⊖ b ⊗ Κ Q.0ℚᵘ ⊜ a) P.≃-refl a b)))))
      (P.≃-trans (P.≃-symm (P.*-identityʳ s))
        (P.≃-trans (P.*-congˡ (P.≃-symm unit))
          (P.≃-trans
            (let open P.ℝ-Solver in solve 4
              (λ c s a b → s ⊗ (a ⊗ a ⊕ b ⊗ b) ⊜
                b ⊗ (c ⊗ a ⊖ s ⊗ (⊝ b)) ⊕ a ⊗ (c ⊗ (⊝ b) ⊕ s ⊗ a))
              P.≃-refl c s a b)
            (P.≃-trans
              (P.+-cong (P.*-congˡ (C.reEquivalent h)) (P.*-congˡ (C.imEquivalent h)))
              (let open P.ℝ-Solver in solve 2
                (λ a b → b ⊗ Κ Q.1ℚᵘ ⊕ a ⊗ Κ Q.0ℚᵘ ⊜ b) P.≃-refl a b)))))

  actualCayley : ∀ p → Phase.phase p ≈C cayley p
  actualCayley p = recover (Phase.phase p) (cayley p) (cayleyUnit p)
    (C.≈C-trans (C.≈C-sym (HRead p)) (conserved p))

fivePoint point239 : Point
fivePoint = point A.bishopOneFifth A.oneFifthNonnegative
  (P.p≤q⇒p⋆≤q⋆ A.oneFifth (+ 1 / 2) A.oneFifthBelowHalfRational)
point239 = point A.bishopOneTwoHundredThirtyNinth A.oneTwoHundredThirtyNinthNonnegative
  (P.p≤q⇒p⋆≤q⋆ A.oneTwoHundredThirtyNinth (+ 1 / 2) A.oneTwoHundredThirtyNineBelowHalfRational)

-- Same limit even when the half-ball witness is built by a different path.
fiveAtanRead : A.bishopAtanOneFifth ≃ atan fivePoint
fiveAtanRead = atanValueCong A.bishopOneFifth A.bishopOneFifth
  A.bishopOneFifthInsideHalf (S.asHalf fivePoint) P.≃-refl

atan239Read : A.bishopAtanOneTwoHundredThirtyNinth ≃ atan point239
atan239Read = atanValueCong A.bishopOneTwoHundredThirtyNinth A.bishopOneTwoHundredThirtyNinth
  A.bishopOneTwoHundredThirtyNinthInsideHalf (S.asHalf point239) P.≃-refl

fiveD : d fivePoint ≃ ((+ 25 / 26) ⋆)
fiveD = dCandidate fivePoint ((+ 25 / 26) ⋆)
  (let open P.ℝ-Solver in solve 0
    ((Κ Q.1ℚᵘ ⊕ Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 25 / 26) ⊜ Κ Q.1ℚᵘ) P.≃-refl)

d239 : d point239 ≃ ((+ 57121 / 57122) ⋆)
d239 = dCandidate point239 ((+ 57121 / 57122) ⋆)
  (let open P.ℝ-Solver in solve 0
    ((Κ Q.1ℚᵘ ⊕ Κ (+ 1 / 239) ⊗ Κ (+ 1 / 239)) ⊗ Κ (+ 57121 / 57122) ⊜ Κ Q.1ℚᵘ) P.≃-refl)

originalFive : (inputs : Round11.BishopCutset) → Two.OriginalAtanFiveCayleyEvaluation inputs
originalFive inputs =
  let module M = At inputs
      a = A.bishopAtanOneFifth
      angle = P.≃-trans
        (let open P.ℝ-Solver in solve 1 (λ a → a ⊕ a ⊜ Κ (+ 2 / 1) ⊗ a) P.≃-refl a)
        (P.*-congˡ fiveAtanRead)
  in C.≈C-trans (C.expCongruent M.T (C.complex-equivalent P.≃-refl angle))
    (C.≈C-trans (C.expImaginaryIsTrigPair M.T (two * atan fivePoint))
      (C.≈C-trans (M.actualCayley fivePoint)
        (C.complex-equivalent
          (P.≃-trans (P.*-congʳ fiveD)
            (let open P.ℝ-Solver in solve 0
              (Κ (+ 25 / 26) ⊗ (Κ Q.1ℚᵘ ⊖ Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊜ Κ (+ 12 / 13)) P.≃-refl))
          (P.≃-trans (P.*-congʳ fiveD)
            (let open P.ℝ-Solver in solve 0
              (Κ (+ 25 / 26) ⊗ (Κ (+ 2 / 1) ⊗ Κ (+ 1 / 5)) ⊜ Κ (+ 5 / 13)) P.≃-refl)))))

original239 : (inputs : Round11.BishopCutset) → Two.OriginalAtan239CayleyEvaluation inputs
original239 inputs =
  let module M = At inputs
      a = A.bishopAtanOneTwoHundredThirtyNinth
      angle = P.≃-trans
        (let open P.ℝ-Solver in solve 1 (λ a → a ⊕ a ⊜ Κ (+ 2 / 1) ⊗ a) P.≃-refl a)
        (P.*-congˡ atan239Read)
  in C.≈C-trans (C.expCongruent M.T (C.complex-equivalent P.≃-refl angle))
    (C.≈C-trans (C.expImaginaryIsTrigPair M.T (two * atan point239))
      (C.≈C-trans (M.actualCayley point239)
        (C.complex-equivalent
          (P.≃-trans (P.*-congʳ d239)
            (let open P.ℝ-Solver in solve 0
              (Κ (+ 57121 / 57122) ⊗ (Κ Q.1ℚᵘ ⊖ Κ (+ 1 / 239) ⊗ Κ (+ 1 / 239)) ⊜ Κ (+ 28560 / 28561)) P.≃-refl))
          (P.≃-trans (P.*-congʳ d239)
            (let open P.ℝ-Solver in solve 0
              (Κ (+ 57121 / 57122) ⊗ (Κ (+ 2 / 1) ⊗ Κ (+ 1 / 239)) ⊜ Κ (+ 239 / 28561)) P.≃-refl)))))

originalQuarterEquality : ∀ inputs → Quad.quarterCos inputs ≃ Quad.quarterSin inputs
originalQuarterEquality inputs = HalfPhase.sourceMachinQuarterEqualityFromCayley inputs
  (Native.originalNativeImaginaryExpProduct inputs)
  (C.≈C-trans (Two.nativeCombinedCayleyFromTwoOriginalAtanValues inputs (originalFive inputs) (original239 inputs))
    Bridge.originalMachinRationalCayleyIsBishopImaginaryUnit)

originalFirstZero : ∀ inputs → First.SourceMachinFirstPositiveSineZero inputs
originalFirstZero inputs = Two.originalMachinFirstPositiveSineZeroFromTwoAtanCayleyValues inputs
  (originalFive inputs) (original239 inputs)
