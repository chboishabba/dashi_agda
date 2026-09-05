module DASHI.Physics.QuantumVacuum.CasimirZetaMinusThreeBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ZetaMinusThreeBernoulliArithmeticExact as Zeta3
import DASHI.Physics.QuantumVacuum.ParallelPlateRegulatedDifferenceBidiExact as Difference
import DASHI.Physics.QuantumVacuum.Casimir720FactorisationBidiExact as C720
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir

------------------------------------------------------------------------
-- CASIMIR LONGITUDINAL DEFECT -> ZETA(-3), BIDI
--
-- A zeta special value is useful only if the transformed Casimir longitudinal
-- defect is proved to be the same analytic object whose finite part is being
-- evaluated.  This owner makes that weld explicit.
------------------------------------------------------------------------

record CasimirLongitudinalZetaProblem
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    defect : Difference.CasimirLongitudinalDefect kernel

    ZetaFunction : Set
    zetaFunction : ZetaFunction
    MinusThreePoint : Set
    minusThreePoint : MinusThreePoint
    ZetaValue : Set
    evaluateZeta : ZetaFunction → MinusThreePoint → ZetaValue

    transformedDefectValue : ZetaValue

    sameDefectAfterTransformation : Set
    finitePartEqualsZetaMinusThree :
      transformedDefectValue ≡ evaluateZeta zetaFunction minusThreePoint

    reading : String

open CasimirLongitudinalZetaProblem public

record CasimirZetaMinusThreeClosure
    (kernel : Casimir.CasimirScalarModel)
    (P : CasimirLongitudinalZetaProblem kernel) : Set₁ where
  field
    bernoulliAnalyticReceipt : Zeta3.ZetaMinusThreeBernoulliAnalyticReceipt

    sameZetaValueCarrier : Set
    sameZetaObject : Set
    rationalValueTransport : Set

    producesCasimirOneOver120 : Set
    sameLongitudinalDefect : sameDefectAfterTransformation P

    reading : String

open CasimirZetaMinusThreeClosure public

------------------------------------------------------------------------
-- Projection to the 720-factorisation receipt is still authority-bound by the
-- same-object transport.  The arithmetic 1/120 itself is already compiler
-- output in ZetaMinusThreeBernoulliArithmeticExact.
------------------------------------------------------------------------

record CasimirZeta120Producer
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    problem : CasimirLongitudinalZetaProblem kernel
    closure : CasimirZetaMinusThreeClosure kernel problem
    receipt : C720.ZetaMinusThree120Receipt
    receiptUsesProblemDefect : Set
    reading : String

open CasimirZeta120Producer public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RiemannZetaSpecialValueAutomaticallyIdentifiesCasimirDefect : Set where

data BernoulliArithmeticAutomaticallyProvesAnalyticContinuation : Set where

zetaSpecialValueNeedsDefectWeld :
  RiemannZetaSpecialValueAutomaticallyIdentifiesCasimirDefect → ⊥
zetaSpecialValueNeedsDefectWeld ()

bernoulliArithmeticDoesNotProveZetaContinuation :
  BernoulliArithmeticAutomaticallyProvesAnalyticContinuation → ⊥
bernoulliArithmeticDoesNotProveZetaContinuation ()

record CasimirZetaMinusThreeStatus : Set where
  field
    rationalOneOver120CompilerOwned : Bool
    casimirLongitudinalZetaWeldInterfaceOwned : Bool
    analyticZetaMinusThreeClosed : Bool
    sameObjectCasimir120Closed : Bool

    rationalOneOver120CompilerOwnedIsTrue :
      rationalOneOver120CompilerOwned ≡ true
    casimirLongitudinalZetaWeldInterfaceOwnedIsTrue :
      casimirLongitudinalZetaWeldInterfaceOwned ≡ true
    analyticZetaMinusThreeClosedIsFalse : analyticZetaMinusThreeClosed ≡ false
    sameObjectCasimir120ClosedIsFalse : sameObjectCasimir120Closed ≡ false

open CasimirZetaMinusThreeStatus public

canonicalCasimirZetaMinusThreeStatus : CasimirZetaMinusThreeStatus
canonicalCasimirZetaMinusThreeStatus = record
  { rationalOneOver120CompilerOwned = true
  ; casimirLongitudinalZetaWeldInterfaceOwned = true
  ; analyticZetaMinusThreeClosed = false
  ; sameObjectCasimir120Closed = false
  ; rationalOneOver120CompilerOwnedIsTrue = refl
  ; casimirLongitudinalZetaWeldInterfaceOwnedIsTrue = refl
  ; analyticZetaMinusThreeClosedIsFalse = refl
  ; sameObjectCasimir120ClosedIsFalse = refl
  }
