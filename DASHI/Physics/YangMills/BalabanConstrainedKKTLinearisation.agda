module DASHI.Physics.YangMills.BalabanConstrainedKKTLinearisation where

-- Source-neutral operator algebra for the differentiated constrained minimum.
--
-- At a regular minimising pair the linearised KKT equations are
--
--   L db = Q* dλ,
--   Q db = dc.
--
-- If L^{-1} and (Q L^{-1} Q*)^{-1} exist on the literal gauge-fixed carriers,
-- this module constructs
--
--   db = L^{-1} Q* (Q L^{-1} Q*)^{-1} dc,
--   dλ = (Q L^{-1} Q*)^{-1} dc,
--
-- proves both equations, and proves uniqueness when the supplied inverses are
-- two-sided on their carriers.  The constraint-curvature term is not omitted:
-- it belongs to the source-provided operator L.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _∘_
  ; _≈_
  ; constrainedCovariance
  ; cong
  ; trans
  )

sym : {A : Set} → {x y : A} → x ≡ y → y ≡ x
sym refl = refl

identity : {A : Set} → A → A
identity x = x

coarseSchurOperator :
  {Fine Coarse : Set} →
  (Fine → Coarse) →
  (Fine → Fine) →
  (Coarse → Fine) →
  ((Coarse → Coarse) → Coarse → Coarse) →
  Coarse → Coarse
coarseSchurOperator Q inverseL Q* inverseCoarse =
  inverseCoarse (constrainedCovariance Q inverseL Q*)

constrainedBackgroundDerivative :
  {Fine Coarse : Set} →
  (Fine → Fine) →
  (Coarse → Fine) →
  (Coarse → Coarse) →
  Coarse → Fine
constrainedBackgroundDerivative inverseL Q* coarseSchur =
  inverseL ∘ Q* ∘ coarseSchur

multiplierDerivative :
  {Coarse : Set} →
  (Coarse → Coarse) →
  Coarse → Coarse
multiplierDerivative coarseSchur = coarseSchur

LinearisedKKTSystem :
  {Fine Coarse : Set} →
  (Fine → Fine) →
  (Fine → Coarse) →
  (Coarse → Fine) →
  (Coarse → Fine) →
  (Coarse → Coarse) →
  Set
LinearisedKKTSystem L Q Q* db dλ =
  (L ∘ db ≈ Q* ∘ dλ)
  ×
  (Q ∘ db ≈ identity)

-- The candidate derivative satisfies the linearised constraint because the
-- coarse Schur operator is a right inverse of Q L^{-1} Q*.
backgroundDerivativeSatisfiesConstraint :
  {Fine Coarse : Set} →
  (Q : Fine → Coarse) →
  (inverseL : Fine → Fine) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (coarseRightInverse :
    constrainedCovariance Q inverseL Q* ∘ coarseSchur
      ≈ identity) →
  Q ∘ constrainedBackgroundDerivative inverseL Q* coarseSchur
    ≈ identity
backgroundDerivativeSatisfiesConstraint
  Q inverseL Q* coarseSchur coarseRightInverse dc =
  coarseRightInverse dc

-- It also satisfies differentiated stationarity when L L^{-1} is the identity
-- on the fine carrier.
backgroundDerivativeSatisfiesStationarity :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineRightInverse : L ∘ inverseL ≈ identity) →
  L ∘ constrainedBackgroundDerivative inverseL Q* coarseSchur
    ≈ Q* ∘ multiplierDerivative coarseSchur
backgroundDerivativeSatisfiesStationarity
  L inverseL Q* coarseSchur fineRightInverse dc =
  fineRightInverse (Q* (coarseSchur dc))

-- Complete proof term for the linearised KKT pair.
constrainedKKTLinearisationSolution :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineRightInverse : L ∘ inverseL ≈ identity) →
  (coarseRightInverse :
    constrainedCovariance Q inverseL Q* ∘ coarseSchur
      ≈ identity) →
  LinearisedKKTSystem
    L Q Q*
    (constrainedBackgroundDerivative inverseL Q* coarseSchur)
    (multiplierDerivative coarseSchur)
constrainedKKTLinearisationSolution
  L inverseL Q Q* coarseSchur
  fineRightInverse coarseRightInverse =
  backgroundDerivativeSatisfiesStationarity
    L inverseL Q* coarseSchur fineRightInverse
  ,
  backgroundDerivativeSatisfiesConstraint
    Q inverseL Q* coarseSchur coarseRightInverse

-- Any solution of the KKT equations has the stated multiplier derivative when
-- L^{-1} and the coarse Schur operator are left inverses as well.
linearisedKKTMultiplierUnique :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineLeftInverse : inverseL ∘ L ≈ identity) →
  (coarseLeftInverse :
    coarseSchur ∘ constrainedCovariance Q inverseL Q*
      ≈ identity) →
  (db : Coarse → Fine) →
  (dλ : Coarse → Coarse) →
  LinearisedKKTSystem L Q Q* db dλ →
  dλ ≈ multiplierDerivative coarseSchur
linearisedKKTMultiplierUnique
  L inverseL Q Q* coarseSchur
  fineLeftInverse coarseLeftInverse db dλ system dc =
  let
    stationarity = proj₁ system dc
    constraint = proj₂ system dc
    dbRepresentation = trans
      (sym (fineLeftInverse (db dc)))
      (cong inverseL stationarity)
    covarianceEquation = trans
      (sym (cong Q dbRepresentation))
      constraint
  in
    trans
      (sym (coarseLeftInverse (dλ dc)))
      (cong coarseSchur covarianceEquation)

-- The fine/background derivative is unique as well.
linearisedKKTBackgroundUnique :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineLeftInverse : inverseL ∘ L ≈ identity) →
  (coarseLeftInverse :
    coarseSchur ∘ constrainedCovariance Q inverseL Q*
      ≈ identity) →
  (db : Coarse → Fine) →
  (dλ : Coarse → Coarse) →
  LinearisedKKTSystem L Q Q* db dλ →
  db ≈ constrainedBackgroundDerivative inverseL Q* coarseSchur
linearisedKKTBackgroundUnique
  L inverseL Q Q* coarseSchur
  fineLeftInverse coarseLeftInverse db dλ system dc =
  let
    stationarity = proj₁ system dc
    dbRepresentation = trans
      (sym (fineLeftInverse (db dc)))
      (cong inverseL stationarity)
    multiplierEquality = linearisedKKTMultiplierUnique
      L inverseL Q Q* coarseSchur
      fineLeftInverse coarseLeftInverse
      db dλ system dc
    p2 = cong
      (λ multiplier → inverseL (Q* multiplier))
      multiplierEquality
  in
    trans dbRepresentation p2

linearisedKKTSolutionUnique :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (coarseSchur : Coarse → Coarse) →
  (fineLeftInverse : inverseL ∘ L ≈ identity) →
  (coarseLeftInverse :
    coarseSchur ∘ constrainedCovariance Q inverseL Q*
      ≈ identity) →
  (db : Coarse → Fine) →
  (dλ : Coarse → Coarse) →
  LinearisedKKTSystem L Q Q* db dλ →
  (db ≈ constrainedBackgroundDerivative inverseL Q* coarseSchur)
  ×
  (dλ ≈ multiplierDerivative coarseSchur)
linearisedKKTSolutionUnique
  L inverseL Q Q* coarseSchur
  fineLeftInverse coarseLeftInverse db dλ system =
  linearisedKKTBackgroundUnique
    L inverseL Q Q* coarseSchur
    fineLeftInverse coarseLeftInverse db dλ system
  ,
  linearisedKKTMultiplierUnique
    L inverseL Q Q* coarseSchur
    fineLeftInverse coarseLeftInverse db dλ system

-- Specialisation where the coarse operator is constructed by the supplied
-- inverse implementation.
constructedConstrainedKKTLinearisationSolution :
  {Fine Coarse : Set} →
  (L inverseL : Fine → Fine) →
  (Q : Fine → Coarse) →
  (Q* : Coarse → Fine) →
  (inverseCoarse :
    (Coarse → Coarse) →
    Coarse → Coarse) →
  (fineRightInverse : L ∘ inverseL ≈ identity) →
  (coarseRightInverse :
    constrainedCovariance Q inverseL Q*
      ∘ coarseSchurOperator Q inverseL Q* inverseCoarse
      ≈ identity) →
  LinearisedKKTSystem
    L Q Q*
    (constrainedBackgroundDerivative
      inverseL Q*
      (coarseSchurOperator Q inverseL Q* inverseCoarse))
    (multiplierDerivative
      (coarseSchurOperator Q inverseL Q* inverseCoarse))
constructedConstrainedKKTLinearisationSolution
  L inverseL Q Q* inverseCoarse
  fineRightInverse coarseRightInverse =
  constrainedKKTLinearisationSolution
    L inverseL Q Q*
    (coarseSchurOperator Q inverseL Q* inverseCoarse)
    fineRightInverse coarseRightInverse
