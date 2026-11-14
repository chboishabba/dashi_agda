module DASHI.Physics.YangMills.BalabanLiteralBishopPositiveExpressionCompilerExact where

-- Same-source Bishop-real semantics for the ACTUAL recursively evaluated
-- DiagramExpression, driven by the genuine Canonical physical atom data.
--
-- The only premises are:
--   (1) equality of selected BoxTrigEnvironment atom intervals with the
--       existing canonical SU2/Wilson Bishop atom environment;
--   (2) a SUCCESSFUL recursive strict-positive rational denominator check.
--
-- For every expression, construct a CertifiedBishopExpression whose interval
-- is PROP. EQUAL to Eval.evaluateExpression selectedArithmetic.
-- The division clause calls the existing sound Bishop divideCertificate,
-- and proof-irrelevant typed positive quotient congruence.
--
-- This does not invent PhysicalTrigBoxData nor a physical source AST.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)

import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4TypedRationalExpressionIntervalExact as Typed
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4BishopExpressionIntervalSemanticsExact as Sem
import DASHI.Physics.YangMills.BalabanLiteralRationalEndpointSemiringExact as End
import DASHI.Physics.YangMills.BalabanLiteralProofIrrelevantIntervalBackendExact as Proofs
import DASHI.Physics.YangMills.BalabanLiteralTotalRationalBackendExact as Selected
import DASHI.Physics.YangMills.BalabanLiteralRecursivePositiveDivisionCompilerExact as Pos

record SelectedBishopExpression
    (trig : Canonical.PhysicalTrigBoxData)
    (environment : Eval.BoxTrigEnvironment)
    (expression : Eval.DiagramExpression) : Set₁ where
  constructor selectedBishopExpression
  field
    certified :
      Sem.CertifiedBishopExpression
        (Canonical.canonicalBishopAtomEnvironment trig)
        expression
    sameSelectedInterval :
      Sem.interval certified ≡
      Eval.evaluateExpression Selected.selectedArithmetic environment expression

open SelectedBishopExpression public

endpointsOfEqual :
  ∀ {a b : Eval.RationalInterval} →
  a ≡ b → End.SameEndpoints a b
endpointsOfEqual refl = End.sameEndpoints refl refl

compileBishopPositive :
  (trig : Canonical.PhysicalTrigBoxData) →
  (environment : Eval.BoxTrigEnvironment) →
  (sameSourceAtom : ∀ atom →
    Canonical.canonicalAtomInterval trig atom
      ≡ Eval.atomInterval environment atom) →
  ∀ {expression} →
  Pos.AllDivisionsPositive environment expression →
  SelectedBishopExpression trig environment expression
compileBishopPositive trig environment sameSourceAtom
  (Pos.constantPositive value) =
  selectedBishopExpression
    (Sem.constantCertificate (Canonical.canonicalBishopAtomEnvironment trig) value)
    refl
compileBishopPositive trig environment sameSourceAtom
  (Pos.atomPositive atom) =
  selectedBishopExpression
    (Sem.atomCertificate (Canonical.canonicalBishopAtomEnvironment trig) atom)
    (sameSourceAtom atom)
compileBishopPositive trig environment sameSourceAtom
  (Pos.addPositive left right) =
  let
    l = compileBishopPositive trig environment sameSourceAtom left
    r = compileBishopPositive trig environment sameSourceAtom right
  in
  selectedBishopExpression
    (Sem.addCertificate (certified l) (certified r))
    (cong₂ Typed.addInterval (sameSelectedInterval l) (sameSelectedInterval r))
compileBishopPositive trig environment sameSourceAtom
  (Pos.subtractPositive left right) =
  let
    l = compileBishopPositive trig environment sameSourceAtom left
    r = compileBishopPositive trig environment sameSourceAtom right
  in
  selectedBishopExpression
    (Sem.subtractCertificate (certified l) (certified r))
    (cong₂ Typed.subtractInterval
      (sameSelectedInterval l) (sameSelectedInterval r))
compileBishopPositive trig environment sameSourceAtom
  (Pos.multiplyPositive left right) =
  let
    l = compileBishopPositive trig environment sameSourceAtom left
    r = compileBishopPositive trig environment sameSourceAtom right
  in
  selectedBishopExpression
    (Sem.multiplyCertificate (certified l) (certified r))
    (cong₂ Typed.multiplyInterval
      (sameSelectedInterval l) (sameSelectedInterval r))
compileBishopPositive trig environment sameSourceAtom
  (Pos.dividePositive {numerator} {denominator}
    numeratorPositive denominatorPositive positive) =
  let
    l = compileBishopPositive trig environment sameSourceAtom numeratorPositive
    r = compileBishopPositive trig environment sameSourceAtom denominatorPositive

    denominatorCertifiedPositive :
      0ℚ < Eval.lower (Sem.interval (certified r))
    denominatorCertifiedPositive =
      subst (λ box → 0ℚ < Eval.lower box)
        (sym (sameSelectedInterval r))
        positive

    sourceBishopCertificate =
      Sem.divideCertificate
        (certified l) (certified r) denominatorCertifiedPositive

    numeratorBox =
      Eval.evaluateExpression Selected.selectedArithmetic environment numerator
    denominatorBox =
      Eval.evaluateExpression Selected.selectedArithmetic environment denominator

    typedEndpointIdentity :
      Typed.divideInterval
        (Sem.interval (certified l))
        (Sem.interval (certified r))
        denominatorCertifiedPositive
      ≡ Typed.divideInterval numeratorBox denominatorBox positive
    typedEndpointIdentity =
      Proofs.typedPositiveDivideCongruenceFull
        (endpointsOfEqual (sameSelectedInterval l))
        (endpointsOfEqual (sameSelectedInterval r))
        denominatorCertifiedPositive positive
  in
  selectedBishopExpression
    sourceBishopCertificate
    (trans
      typedEndpointIdentity
      (sym (Selected.totalDivideEqualsTypedWhenPositive
        numeratorBox denominatorBox positive)))
compileBishopPositive trig environment sameSourceAtom
  (Pos.negatePositive expressionPositive) =
  let
    x = compileBishopPositive trig environment sameSourceAtom expressionPositive
  in
  selectedBishopExpression
    (Sem.negateCertificate (certified x))
    (cong Typed.negateInterval (sameSelectedInterval x))

-- Direct physical source consumer. All source identities refer to the SAME
-- literal scalarData.regularIntegrand expression and selected environment.
literalWilsonGhostHaarBishopEvaluation :
  ∀ {expressions ward}
    (scalarData : Eval.LiteralScalarIntegrandExpression expressions ward)
    (trig : Canonical.PhysicalTrigBoxData)
    (environment : Eval.BoxTrigEnvironment) →
    (sameSourceAtom : ∀ atom →
      Canonical.canonicalAtomInterval trig atom
        ≡ Eval.atomInterval environment atom) →
    Pos.AllDivisionsPositive environment
      (Eval.regularIntegrand scalarData) →
    SelectedBishopExpression trig environment
      (Eval.regularIntegrand scalarData)
literalWilsonGhostHaarBishopEvaluation scalarData trig environment sameAtom proof =
  compileBishopPositive trig environment sameAtom proof

-- No assertion that the literal Wilson/ghost/Haar physical scalar has
-- already been instantiated; no physical quadrature results are inferred.
