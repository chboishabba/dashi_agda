module DASHI.Physics.YangMills.BalabanCMP109FederbushAverageDerivativeExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- Ethan Eade,
-- "Derivative of the Exponential Map", technical note, 2018 revision.
-- No DOI recorded.
--
-- DASHI CONTRIBUTION
--
-- Differentiate Bałaban's implicit Federbush characterization of the analytic
-- group average rather than treating equation (0.11) as an opaque derivative
-- producer.  If V=M(U_1,...,U_n) is characterized by
--
--       sum_j log(U_j V^{-1}) = 0,
--
-- then in left-trivialized Lie coordinates its linearization has the form
--
--       sum_j J_j (u_j - T_j v) = 0.
--
-- Here J_j is the principal-log differential at U_j V^{-1}, T_j is the exact
-- transport dictated by the chosen trivialization, u_j are input path
-- variations, and v is the variation of the group average.  This module proves
-- the finite noncommutative linear algebra:
--
--       A v = b,
--       A = sum_j J_j T_j,
--       b = sum_j J_j u_j,
--       v = A^{-1} b.
--
-- Thus the derivative of equation (0.11) is reduced to the already isolated
-- principal-log differential plus one finite average-Jacobian inverse.  At the
-- identity reference the formula target is the ordinary arithmetic mean; its
-- physical identification is intentionally a separate instantiation theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

Endomorphism : Set → Set
Endomorphism V = V → V

record LinearOperatorAlgebra (V : Set) : Set₁ where
  field
    zero : V
    add subtract : V → V → V

    zeroOperator identityOperator : Endomorphism V
    addOperator : Endomorphism V → Endomorphism V → Endomorphism V
    compose : Endomorphism V → Endomorphism V → Endomorphism V

    addOperatorPointwise : ∀ left right vector →
      addOperator left right vector ≡ add (left vector) (right vector)
    composePointwise : ∀ outer inner vector →
      compose outer inner vector ≡ outer (inner vector)
    zeroOperatorPointwise : ∀ vector → zeroOperator vector ≡ zero
    identityOperatorPointwise : ∀ vector → identityOperator vector ≡ vector

    addZeroLeft : ∀ vector → add zero vector ≡ vector
    addZeroRight : ∀ vector → add vector zero ≡ vector
    addAssoc : ∀ a b c → add (add a b) c ≡ add a (add b c)

open LinearOperatorAlgebra public

sumVectors : ∀ {V} → LinearOperatorAlgebra V → List V → V
sumVectors algebra [] = zero algebra
sumVectors algebra (value ∷ values) =
  add algebra value (sumVectors algebra values)

sumOperators : ∀ {V} → LinearOperatorAlgebra V → List (Endomorphism V) → Endomorphism V
sumOperators algebra [] = zeroOperator algebra
sumOperators algebra (operator ∷ operators) =
  addOperator algebra operator (sumOperators algebra operators)

map : ∀ {A B : Set} → (A → B) → List A → List B
map function [] = []
map function (value ∷ values) = function value ∷ map function values

sumOperatorActsAsSum :
  ∀ {V} (algebra : LinearOperatorAlgebra V)
    (operators : List (Endomorphism V)) vector →
  sumOperators algebra operators vector
  ≡ sumVectors algebra (map (λ operator → operator vector) operators)
sumOperatorActsAsSum algebra [] vector =
  zeroOperatorPointwise algebra vector
sumOperatorActsAsSum algebra (operator ∷ operators) vector =
  trans
    (addOperatorPointwise algebra operator (sumOperators algebra operators) vector)
    (cong (add algebra (operator vector))
      (sumOperatorActsAsSum algebra operators vector))

record FederbushLinearizationData
    {Index V : Set}
    (algebra : LinearOperatorAlgebra V)
    (indices : List Index) : Set₁ where
  field
    logJacobian : Index → Endomorphism V
    outputTransport : Index → Endomorphism V
    inputVariation : Index → V
    averageVariation : V

    -- Exact linearized Federbush equation after differentiating
    -- sum log(U_j V^-1)=0 in the selected left trivialization.
    linearizedFederbush :
      sumVectors algebra
        (map
          (λ index →
            logJacobian index
              (subtract algebra
                (inputVariation index)
                (outputTransport index averageVariation)))
          indices)
      ≡ zero algebra

    -- This is the finite distributivity/linearity collection step.  In a
    -- concrete vector space it is proved from linearity of J_j and T_j.
    linearizedEquationCollects :
      linearizedFederbush →
      sumOperators algebra
        (map
          (λ index →
            compose algebra (logJacobian index) (outputTransport index))
          indices)
        averageVariation
      ≡ sumVectors algebra
          (map (λ index → logJacobian index (inputVariation index)) indices)

open FederbushLinearizationData public

averageJacobian :
  ∀ {Index V algebra indices} →
  FederbushLinearizationData {Index} {V} algebra indices → Endomorphism V
averageJacobian {algebra = algebra} {indices = indices} dataSet =
  sumOperators algebra
    (map
      (λ index →
        compose algebra
          (logJacobian dataSet index)
          (outputTransport dataSet index))
      indices)

averageSource :
  ∀ {Index V algebra indices} →
  FederbushLinearizationData {Index} {V} algebra indices → V
averageSource {algebra = algebra} {indices = indices} dataSet =
  sumVectors algebra
    (map
      (λ index → logJacobian dataSet index (inputVariation dataSet index))
      indices)

record FederbushAverageJacobianInverse
    {Index V : Set}
    {algebra : LinearOperatorAlgebra V}
    {indices : List Index}
    (dataSet : FederbushLinearizationData algebra indices) : Set₁ where
  field
    inverse : Endomorphism V
    inverseAfterJacobian : ∀ vector →
      inverse (averageJacobian dataSet vector) ≡ vector

open FederbushAverageJacobianInverse public

federbushAverageDerivativeSolved :
  ∀ {Index V algebra indices}
    (dataSet : FederbushLinearizationData {Index} {V} algebra indices)
    (inverseData : FederbushAverageJacobianInverse dataSet) →
  averageVariation dataSet
  ≡ inverse inverseData (averageSource dataSet)
federbushAverageDerivativeSolved dataSet inverseData =
  let
    collected :
      averageJacobian dataSet (averageVariation dataSet)
      ≡ averageSource dataSet
    collected = linearizedEquationCollects dataSet
      (linearizedFederbush dataSet)
  in
  trans
    (sym (inverseAfterJacobian inverseData (averageVariation dataSet)))
    (cong (inverse inverseData) collected)

------------------------------------------------------------------------
-- Identity-reference target.  The physical reference theorem will prove that
-- all J_j and T_j are identities and that the inverse of the n-fold identity
-- sum is multiplication by 1/n.  We keep that numerical normalization outside
-- this algebraic solver so the n=13 and contour-cardinality witnesses cannot be
-- silently conflated.
------------------------------------------------------------------------

record IdentityReferenceAverageData
    {Index V Scalar : Set}
    (algebra : LinearOperatorAlgebra V)
    (indices : List Index) : Set₁ where
  field
    scalarMultiply : Scalar → V → V
    reciprocalCount : Scalar
    inputVariation : Index → V
    averageVariation : V
    identityReferenceDerivative :
      averageVariation
      ≡ scalarMultiply reciprocalCount
          (sumVectors algebra (map inputVariation indices))

open IdentityReferenceAverageData public

arithmeticMean :
  ∀ {Index V Scalar algebra indices} →
  IdentityReferenceAverageData {Index} {V} {Scalar} algebra indices → V
arithmeticMean {algebra = algebra} {indices = indices} dataSet =
  scalarMultiply dataSet (reciprocalCount dataSet)
    (sumVectors algebra (map (inputVariation dataSet) indices))

identityReferenceFederbushDerivativeIsArithmeticMean :
  ∀ {Index V Scalar algebra indices}
    (dataSet : IdentityReferenceAverageData {Index} {V} {Scalar} algebra indices) →
  averageVariation dataSet ≡ arithmeticMean dataSet
identityReferenceFederbushDerivativeIsArithmeticMean dataSet =
  identityReferenceDerivative dataSet

cmp109FederbushLinearizedEquationSolveLevel : ProofLevel
cmp109FederbushLinearizedEquationSolveLevel = machineChecked

cmp109FederbushIdentityDerivativeLevel : ProofLevel
cmp109FederbushIdentityDerivativeLevel = machineChecked

-- The remaining physical input is now sharply localized: instantiate the
-- differentiated Federbush equation with the principal-log differential and
-- prove invertibility/small perturbation of the finite average Jacobian on the
-- selected SU(2) principal chart.
physicalCMP109FederbushDifferentialInstantiationLevel : ProofLevel
physicalCMP109FederbushDifferentialInstantiationLevel = conditional
