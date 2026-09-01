{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact where

------------------------------------------------------------------------
-- ROUND146 A1: LITERAL CMP98 EQ. (119) ONE-STEP Q' OPERATOR
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- CMP98 Eq. (118) identifies the linear term of the perturbed one-step average
-- with Q'(V0) A.  Eq. (119) then gives that derivative explicitly:
--
--   g(-i ad Y) sum_{x in B(c-)} L^-d g^-1(-i ad Y_x)
--     [ (R0 A)(F_{c-,x} U [x,x'])
--       - R(e^{iY_x}) (R0 A)(c U F_{c+,x'}) ]
--   + R(e^{iY}) (R0 A)(c).
--
-- R126 already proves that literal one-step q' data propagate through every
-- finite multiscale blocking composition by the noncommutative product rule.
-- Therefore we implement Eq. (119) itself here rather than adding another
-- abstract `qPrime` socket.
--
-- The geometry-specific maps below are deliberately separate operators:
--   outerG       = g(-i ad Y)
--   inverseGAt   = g^-1(-i ad Y_x)
--   blockWeight  = multiplication by L^-d
--   adjointAt    = R(e^{iY_x})
--   adjointOuter = R(e^{iY})
--   minusPath / plusPath / centrePath = the three literal R0 path evaluations.
--
-- No commutativity is assumed.  The only remaining physical task after this
-- module is to realize those operators by the literal CMP98 lattice/background
-- objects used by the repository's one-step averaging map.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126

------------------------------------------------------------------------
-- Signed extension of the R126 additive carrier.
------------------------------------------------------------------------

record SignedAdditiveOperatorCarrier : Set₁ where
  field
    additive : R126.AdditiveOperatorCarrier
    negV : R126.Vector additive → R126.Vector additive

open SignedAdditiveOperatorCarrier public

subV :
  ∀ {C : SignedAdditiveOperatorCarrier} →
  R126.Vector (additive C) →
  R126.Vector (additive C) →
  R126.Vector (additive C)
subV {C} left right =
  R126.addV (additive C) left (negV C right)

sumV :
  ∀ {C : SignedAdditiveOperatorCarrier} →
  List (R126.Vector (additive C)) →
  R126.Vector (additive C)
sumV {C} [] = R126.zeroV (additive C)
sumV {C} (x ∷ xs) = R126.addV (additive C) x (sumV xs)

------------------------------------------------------------------------
-- Exact component language for source Eq. (119).
------------------------------------------------------------------------

record CMP98Equation119SourceOperators
    (C : SignedAdditiveOperatorCarrier) : Set₁ where
  field
    -- The literal one-step average Q(V0) itself.  Eq. (119) supplies its
    -- background derivative, not a replacement definition of Q.
    qSource : Nat → R126.Operator (additive C)

    -- Finite block B(c-) at one blocking step.  A point is represented by its
    -- finite source index; all lattice/path semantics stay in the path maps.
    blockPoints : Nat → List Nat

    -- L^-d, g(-i ad Y), g^-1(-i ad Y_x).
    blockWeight : Nat → R126.Operator (additive C)
    outerG : Nat → R126.Operator (additive C)
    inverseGAt : Nat → Nat → R126.Operator (additive C)

    -- R(e^{iY_x}) and R(e^{iY}).
    adjointAt : Nat → Nat → R126.Operator (additive C)
    adjointOuter : Nat → R126.Operator (additive C)

    -- The three literal R0 path evaluations appearing in Eq. (119).
    minusPath : Nat → Nat → R126.Operator (additive C)
    plusPath : Nat → Nat → R126.Operator (additive C)
    centrePath : Nat → R126.Operator (additive C)

open CMP98Equation119SourceOperators public

pointContribution :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  Nat → Nat →
  R126.Vector (additive C) →
  R126.Vector (additive C)
pointContribution source step x A =
  blockWeight source step
    (inverseGAt source step x
      (subV
        (minusPath source step x A)
        (adjointAt source step x (plusPath source step x A))))

pointContributions :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  Nat →
  R126.Vector (additive C) →
  List Nat →
  List (R126.Vector (additive C))
pointContributions source step A [] = []
pointContributions source step A (x ∷ xs) =
  pointContribution source step x A
  ∷ pointContributions source step A xs

blockContribution :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  Nat →
  R126.Vector (additive C) →
  R126.Vector (additive C)
blockContribution source step A =
  sumV (pointContributions source step A (blockPoints source step))

-- Literal CMP98 Eq. (119).
equation119QPrime :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  Nat → R126.Operator (additive C)
equation119QPrime {C} source step A =
  R126.addV (additive C)
    (outerG source step (blockContribution source step A))
    (adjointOuter source step (centrePath source step A))

------------------------------------------------------------------------
-- Direct R126 producer: Eq. (119) is now the actual one-step q' function.
------------------------------------------------------------------------

asOneStepAveragingDerivative :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  R126.OneStepAveragingDerivative (additive C)
asOneStepAveragingDerivative source = record
  { R126.OneStepAveragingDerivative.q = qSource source
  ; R126.OneStepAveragingDerivative.qPrime = equation119QPrime source
  }

-- No function extensionality is required: the derivative selected by the R126
-- producer reduces pointwise to the literal Eq. (119) expression.
oneStepDerivativeIsCMP98Equation119 :
  ∀ {C}
    (source : CMP98Equation119SourceOperators C)
    step A →
  R126.qPrime (asOneStepAveragingDerivative source) step A
  ≡ equation119QPrime source step A
oneStepDerivativeIsCMP98Equation119 source step A = refl

-- The entire k-step q' is therefore generated by R126 from this exact one-step
-- source operator; there is no second multiscale derivative hypothesis.
equation119MultiscaleDerivative :
  ∀ {C} →
  CMP98Equation119SourceOperators C →
  Nat → R126.Operator (additive C)
equation119MultiscaleDerivative source =
  R126.multiscaleAveragePrime (asOneStepAveragingDerivative source)

cmp98Equation119OneStepFormulaLevel : ProofLevel
cmp98Equation119OneStepFormulaLevel = standardImported

cmp98Equation119ToR126CompilerLevel : ProofLevel
cmp98Equation119ToR126CompilerLevel = machineChecked

-- Irreducible source/repository seam after Eq. (119) is represented literally:
-- instantiate `blockPoints`, the three R0 path evaluations, L^-d, g/inverse-g
-- and the two adjoint transports by the actual CMP98 background/lattice objects
-- used by the repository one-step average.
literalCMP98Equation119OperatorRealizationRound146Level : ProofLevel
literalCMP98Equation119OperatorRealizationRound146Level = conditional
