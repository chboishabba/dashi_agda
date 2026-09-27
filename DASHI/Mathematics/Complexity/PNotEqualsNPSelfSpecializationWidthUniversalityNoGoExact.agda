module DASHI.Mathematics.Complexity.PNotEqualsNPSelfSpecializationWidthUniversalityNoGoExact where

------------------------------------------------------------------------
-- GENERIC SELF-SPECIALIZATION DOES NOT FORCE SMALL SHANNON WIDTH
--
-- Candidate structural hope under audit:
--
--   perhaps being produced by the finite Kleene/self-specializing calculus
--   already forces a special restricted family of Boolean formulas.
--
-- This is false for the generic calculus.
--
-- One fixed primitive semantics can ignore the quoted program and return its
-- dynamic Cook-formula input unchanged.  The ONE literal fixed-point program
--
--   primitiveBodyFixedPoint echoInput
--
-- then evaluates to every Cook Boolean formula as the dynamic input varies.
--
-- Therefore the generic self-specialization syntax is surjective onto ordinary
-- Cook formula syntax.  Any residual-width restriction used by Q1 must come
-- from stronger properties of the SPECIFIC SAT-diagonal primitive semantics,
-- not from Kleene specialization/diagonalization itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; subst; sym; trans)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe.Base using (just)
open import Data.Product using (_×_; _,_)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPFiniteSelfSpecializingCodeExact as Finite
import DASHI.Mathematics.Complexity.PNotEqualsNPCookIndexedFormulaBridgeExact as Bridge
import DASHI.Mathematics.Complexity.PolynomialReductionExact as PR
import DASHI.Mathematics.Complexity.PNotEqualsNPDirectSATLowerBoundExact as Direct
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneToSelfDiagonalBridgeExact as Diagonal
import DASHI.Mathematics.Complexity.PNotEqualsNPKleeneSpecializationFixedPointExact as TotalKleene
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalResidualWidthExact as Width
import DASHI.Mathematics.Complexity.PNotEqualsNPSelfDiagonalRestrictionFamilyExact as Family

------------------------------------------------------------------------
-- One fixed primitive instruction.
------------------------------------------------------------------------

data EchoPrimitive : Set where
  echoInput : EchoPrimitive

------------------------------------------------------------------------
-- One fixed semantics:
--
--   run1 echo x   = x
--   run2 echo q x = x
--
-- The quoted program is intentionally ignored.  This is a valid inhabitant of
-- the generic finite-code interface and demonstrates that self-specialization
-- alone imposes no output-language restriction.
------------------------------------------------------------------------

echoFormulaSemantics :
  Finite.PrimitiveSemantics
    EchoPrimitive
    Cook.BooleanFormula
    Cook.BooleanFormula
echoFormulaSemantics = record
  { Finite.runPrimitive1 =
      λ primitive input →
        just input
  ; Finite.runPrimitive2 =
      λ primitive quoted input →
        just input
  }

------------------------------------------------------------------------
-- One literal self-specializing fixed-point program.
------------------------------------------------------------------------

echoFixedPointProgram :
  Finite.Program EchoPrimitive
echoFixedPointProgram =
  Finite.primitiveBodyFixedPoint echoInput

------------------------------------------------------------------------
-- Main universality theorem.
------------------------------------------------------------------------

echoFixedPointOutputsEveryFormula :
  (formula : Cook.BooleanFormula) →
  Finite.run1
    echoFormulaSemantics
    echoFixedPointProgram
    formula
  ≡
  just formula
echoFixedPointOutputsEveryFormula formula =
  refl

------------------------------------------------------------------------
-- The exact indexed Shannon root of every formula is therefore obtainable as
-- the restriction root of a literal output of the same self-specializing
-- fixed-point program.
------------------------------------------------------------------------

echoFixedPointRestrictionRoot :
  (formula : Cook.BooleanFormula) →
  Family.cookIndexedRestrictionRoot formula
  ≡
  Family.cookIndexedRestrictionRoot formula
echoFixedPointRestrictionRoot formula =
  refl

echoFixedPointRestrictionRootRoundTrip :
  (formula : Cook.BooleanFormula) →
  Bridge.indexedToCook
    (Family.cookIndexedRestrictionRoot formula)
  ≡
  formula
echoFixedPointRestrictionRootRoundTrip =
  Family.cookRestrictionRootRoundTrip

------------------------------------------------------------------------
-- Explicit image receipt for the one fixed-point program.
------------------------------------------------------------------------

record EchoFixedPointImage
    (formula : Cook.BooleanFormula) : Set where
  constructor echo-fixed-point-image
  field
    dynamicInput :
      Cook.BooleanFormula

    execution :
      Finite.run1
        echoFormulaSemantics
        echoFixedPointProgram
        dynamicInput
      ≡
      just formula

open EchoFixedPointImage public

everyFormulaIsInEchoFixedPointImage :
  (formula : Cook.BooleanFormula) →
  EchoFixedPointImage formula
everyFormulaIsInEchoFixedPointImage formula =
  echo-fixed-point-image
    formula
    refl

------------------------------------------------------------------------
-- Width transport is literal: self-specialization does not shrink the Shannon
-- residual family because the fixed-point output is the payload formula itself.
------------------------------------------------------------------------

record EchoFixedPointResidualWidth
    (remaining width : Nat) : Set₁ where
  constructor echo-fixed-point-residual-width
  field
    formula :
      Cook.BooleanFormula

    image :
      EchoFixedPointImage formula

    widthWitness :
      Width.ResidualWidthWitness
        {root = Family.cookIndexedRestrictionRoot formula}
        remaining
        width

open EchoFixedPointResidualWidth public

anyResidualWidthOccursInEchoFixedPointImage :
  ∀ {remaining width}
    (formula : Cook.BooleanFormula) →
  Width.ResidualWidthWitness
    {root = Family.cookIndexedRestrictionRoot formula}
    remaining
    width →
  EchoFixedPointResidualWidth remaining width
anyResidualWidthOccursInEchoFixedPointImage
    formula
    witness =
  echo-fixed-point-residual-width
    formula
    (everyFormulaIsInEchoFixedPointImage formula)
    witness

------------------------------------------------------------------------
-- Specific SAT-diagonal body: literal payload passthrough is blocked.
--
-- Suppose one quoted program evaluates to the known satisfiable anchor and the
-- diagonal body returns literally that same formula.  The body obligation
--
--   body satisfiable -> candidate rejects quoted output
--
-- then contradicts the anchored candidate's acceptance of that formula.
--
-- Therefore the generic echo/passthrough universality above cannot simply be
-- reused as the actual SAT-diagonal primitive body.
------------------------------------------------------------------------

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

literalPassthroughAtKnownSatisfiableImpossible :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    {system : TotalKleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : TotalKleene.Input system}
    (body :
      Diagonal.SATDiagonalBody
        (Direct.candidate anchored)
        system
        view
        dynamicInput)
    (quoted : TotalKleene.Program system) →
  Diagonal.asFormula view
      (TotalKleene.run1 system quoted dynamicInput)
    ≡
    Cook.excludedMiddleFormula →
  Diagonal.asFormula view
      (TotalKleene.run2
        system
        (Diagonal.bodyProgram body)
        quoted
        dynamicInput)
    ≡
    Diagonal.asFormula view
      (TotalKleene.run1 system quoted dynamicInput) →
  ⊥
literalPassthroughAtKnownSatisfiableImpossible
    {anchored = anchored}
    {system = system}
    {view = view}
    {dynamicInput = dynamicInput}
    body
    quoted
    quotedIsKnownSat
    bodyIsQuoted =
  trueNotFalse contradiction
  where
    quotedFormula :
      Cook.BooleanFormula
    quotedFormula =
      Diagonal.asFormula view
        (TotalKleene.run1 system quoted dynamicInput)

    bodyFormula :
      Cook.BooleanFormula
    bodyFormula =
      Diagonal.asFormula view
        (TotalKleene.run2
          system
          (Diagonal.bodyProgram body)
          quoted
          dynamicInput)

    quotedSatisfiable :
      Cook.Satisfiable quotedFormula
    quotedSatisfiable =
      subst
        Cook.Satisfiable
        (sym quotedIsKnownSat)
        Cook.excludedMiddleFormulaIsSatisfiable

    bodySatisfiable :
      Cook.Satisfiable bodyFormula
    bodySatisfiable =
      subst
        Cook.Satisfiable
        (sym bodyIsQuoted)
        quotedSatisfiable

    candidateRejectsQuoted :
      Direct.decide
        (Direct.candidate anchored)
        quotedFormula
      ≡
      false
    candidateRejectsQuoted =
      Diagonal.rejectsQuotedProgramIfBodySatisfiable
        body
        quoted
        bodySatisfiable

    candidateDecisionTransport :
      Direct.decide
        (Direct.candidate anchored)
        quotedFormula
      ≡
      Direct.decide
        (Direct.candidate anchored)
        Cook.excludedMiddleFormula
    candidateDecisionTransport =
      cong
        (Direct.decide
          (Direct.candidate anchored))
        quotedIsKnownSat

    contradiction :
      true
      ≡
      false
    contradiction =
      trans
        (sym
          (Direct.acceptsKnownSatisfiable anchored))
        (trans
          (sym candidateDecisionTransport)
          candidateRejectsQuoted)

------------------------------------------------------------------------
-- SIMPLE GUARD WRAPPER AUDIT
--
-- The obvious next embedding attempt is to carry an arbitrary payload formula
-- behind one Boolean guard while forcing the diagonal SAT polarity.
--
-- There are two non-absorbing guards:
--
--   true  AND payload = payload
--   false OR  payload = payload
--
-- These preserve the payload function exactly, but satisfiability still depends
-- on the payload.
--
-- The two absorbing guards:
--
--   false AND payload = false
--   true  OR  payload = true
--
-- force a SAT/UNSAT answer independently of the payload, but erase the payload
-- function completely.
------------------------------------------------------------------------

andGuard :
  Bool →
  Cook.BooleanFormula →
  Cook.BooleanFormula
andGuard guard payload =
  Cook.conjunction
    (Cook.constant guard)
    payload

orGuard :
  Bool →
  Cook.BooleanFormula →
  Cook.BooleanFormula
orGuard guard payload =
  Cook.disjunction
    (Cook.constant guard)
    payload

andTruePreservesPayloadEvaluation :
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (andGuard true payload)
      assignment
  ≡
  Cook.evaluate payload assignment
andTruePreservesPayloadEvaluation payload assignment =
  refl

orFalsePreservesPayloadEvaluation :
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (orGuard false payload)
      assignment
  ≡
  Cook.evaluate payload assignment
orFalsePreservesPayloadEvaluation payload assignment =
  refl

andFalseErasesPayloadEvaluation :
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (andGuard false payload)
      assignment
  ≡ false
andFalseErasesPayloadEvaluation payload assignment =
  refl

orTrueErasesPayloadEvaluation :
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (orGuard true payload)
      assignment
  ≡ true
orTrueErasesPayloadEvaluation payload assignment =
  refl

andTrueSatisfiabilityEquivalentPayload :
  (payload : Cook.BooleanFormula) →
  (Cook.Satisfiable (andGuard true payload) → Cook.Satisfiable payload)
  ×
  (Cook.Satisfiable payload → Cook.Satisfiable (andGuard true payload))
andTrueSatisfiabilityEquivalentPayload payload =
  forward , backward
  where
    forward :
      Cook.Satisfiable (andGuard true payload) →
      Cook.Satisfiable payload
    forward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (sym
            (andTruePreservesPayloadEvaluation
              payload
              (Cook.Satisfiable.assignment witness)))
          (Cook.Satisfiable.evaluatesTrue witness))

    backward :
      Cook.Satisfiable payload →
      Cook.Satisfiable (andGuard true payload)
    backward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (andTruePreservesPayloadEvaluation
            payload
            (Cook.Satisfiable.assignment witness))
          (Cook.Satisfiable.evaluatesTrue witness))

orFalseSatisfiabilityEquivalentPayload :
  (payload : Cook.BooleanFormula) →
  (Cook.Satisfiable (orGuard false payload) → Cook.Satisfiable payload)
  ×
  (Cook.Satisfiable payload → Cook.Satisfiable (orGuard false payload))
orFalseSatisfiabilityEquivalentPayload payload =
  forward , backward
  where
    forward :
      Cook.Satisfiable (orGuard false payload) →
      Cook.Satisfiable payload
    forward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (sym
            (orFalsePreservesPayloadEvaluation
              payload
              (Cook.Satisfiable.assignment witness)))
          (Cook.Satisfiable.evaluatesTrue witness))

    backward :
      Cook.Satisfiable payload →
      Cook.Satisfiable (orGuard false payload)
    backward witness =
      Cook.satisfyingAssignment
        (Cook.Satisfiable.assignment witness)
        (trans
          (orFalsePreservesPayloadEvaluation
            payload
            (Cook.Satisfiable.assignment witness))
          (Cook.Satisfiable.evaluatesTrue witness))

andFalseUnsatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable (andGuard false payload) →
  ⊥
andFalseUnsatisfiable
    payload
    witness =
  trueNotFalse
    (trans
      (sym
        (Cook.Satisfiable.evaluatesTrue witness))
      (andFalseErasesPayloadEvaluation
        payload
        (Cook.Satisfiable.assignment witness)))

orTrueSatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable (orGuard true payload)
orTrueSatisfiable payload =
  Cook.satisfyingAssignment
    (λ index → false)
    (orTrueErasesPayloadEvaluation
      payload
      (λ index → false))

------------------------------------------------------------------------
-- The canonical polarity-forcing wrapper.
--
-- reject=true  -> force satisfiable with true OR payload
-- reject=false -> force unsatisfiable with false AND payload
------------------------------------------------------------------------

diagonalGuardWrapper :
  Bool →
  Cook.BooleanFormula →
  Cook.BooleanFormula
diagonalGuardWrapper true payload =
  orGuard true payload
diagonalGuardWrapper false payload =
  andGuard false payload

diagonalGuardWrapperRejectingIsSatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable
    (diagonalGuardWrapper true payload)
diagonalGuardWrapperRejectingIsSatisfiable =
  orTrueSatisfiable

diagonalGuardWrapperAcceptingIsUnsatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable
    (diagonalGuardWrapper false payload) →
  ⊥
diagonalGuardWrapperAcceptingIsUnsatisfiable =
  andFalseUnsatisfiable

diagonalGuardWrapperEvaluationIgnoresPayload :
  (reject : Bool) →
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (diagonalGuardWrapper reject payload)
      assignment
  ≡ reject
diagonalGuardWrapperEvaluationIgnoresPayload
    true payload assignment =
  orTrueErasesPayloadEvaluation
    payload
    assignment
diagonalGuardWrapperEvaluationIgnoresPayload
    false payload assignment =
  andFalseErasesPayloadEvaluation
    payload
    assignment

------------------------------------------------------------------------
-- Concrete no-go for the simple guard embedding:
--
-- it can force the diagonal SAT polarity for every payload only by using the
-- absorbing branches, and those make the resulting Boolean function constant.
-- Hence no residual-function width of the payload survives this wrapper.
------------------------------------------------------------------------

simpleGuardPolarityForcingErasesPayload :
  (reject : Bool) →
  (leftPayload rightPayload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (diagonalGuardWrapper reject leftPayload)
      assignment
  ≡
  Cook.evaluate
      (diagonalGuardWrapper reject rightPayload)
      assignment
simpleGuardPolarityForcingErasesPayload
    reject
    leftPayload
    rightPayload
    assignment =
  trans
    (diagonalGuardWrapperEvaluationIgnoresPayload
      reject leftPayload assignment)
    (sym
      (diagonalGuardWrapperEvaluationIgnoresPayload
        reject rightPayload assignment))

------------------------------------------------------------------------
-- ASYMMETRIC WIDTH-PRESERVING REJECT GADGET
--
-- Unlike the dead simple polarity wrapper, we only require width preservation
-- on the REJECT branch.  This is enough for a width transfer if we can keep one
-- quoted program on a candidate-rejected anchor while varying the payload.
--
-- A fresh guard variable occupies Cook variable zero.  Every payload variable
-- is shifted by one.
------------------------------------------------------------------------

shiftCookFormula :
  Cook.BooleanFormula →
  Cook.BooleanFormula
shiftCookFormula (Cook.variable index) =
  Cook.variable (suc index)
shiftCookFormula (Cook.constant value) =
  Cook.constant value
shiftCookFormula (Cook.negate formula) =
  Cook.negate
    (shiftCookFormula formula)
shiftCookFormula (Cook.conjunction left right) =
  Cook.conjunction
    (shiftCookFormula left)
    (shiftCookFormula right)
shiftCookFormula (Cook.disjunction left right) =
  Cook.disjunction
    (shiftCookFormula left)
    (shiftCookFormula right)

tailCookAssignment :
  Cook.Assignment →
  Cook.Assignment
tailCookAssignment assignment index =
  assignment (suc index)

shiftCookEvaluation :
  (payload : Cook.BooleanFormula) →
  (assignment : Cook.Assignment) →
  Cook.evaluate
      (shiftCookFormula payload)
      assignment
  ≡
  Cook.evaluate
      payload
      (tailCookAssignment assignment)
shiftCookEvaluation (Cook.variable index) assignment =
  refl
shiftCookEvaluation (Cook.constant value) assignment =
  refl
shiftCookEvaluation (Cook.negate formula) assignment =
  cong Cook.notBool
    (shiftCookEvaluation formula assignment)
shiftCookEvaluation (Cook.conjunction left right) assignment =
  cong₂
    Cook.andBool
    (shiftCookEvaluation left assignment)
    (shiftCookEvaluation right assignment)
shiftCookEvaluation (Cook.disjunction left right) assignment =
  cong₂
    Cook.orBool
    (shiftCookEvaluation left assignment)
    (shiftCookEvaluation right assignment)

extendCookAssignment :
  Bool →
  Cook.Assignment →
  Cook.Assignment
extendCookAssignment guard payloadAssignment zero =
  guard
extendCookAssignment guard payloadAssignment (suc index) =
  payloadAssignment index

rejectWidthGadget :
  Cook.BooleanFormula →
  Cook.BooleanFormula
rejectWidthGadget payload =
  Cook.disjunction
    (Cook.variable zero)
    (shiftCookFormula payload)

acceptCollapseGadget :
  Cook.BooleanFormula →
  Cook.BooleanFormula
acceptCollapseGadget payload =
  Cook.constant false

diagonalAsymmetricGadget :
  Bool →
  Cook.BooleanFormula →
  Cook.BooleanFormula
diagonalAsymmetricGadget true payload =
  rejectWidthGadget payload
diagonalAsymmetricGadget false payload =
  acceptCollapseGadget payload

------------------------------------------------------------------------
-- Reject branch: SAT is forced, but guard=false recovers the payload exactly.
------------------------------------------------------------------------

rejectWidthGadgetSatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable (rejectWidthGadget payload)
rejectWidthGadgetSatisfiable payload =
  Cook.satisfyingAssignment
    (extendCookAssignment true
      (λ index → false))
    refl

rejectWidthGadgetFalseGuardRecoversPayload :
  (payload : Cook.BooleanFormula) →
  (payloadAssignment : Cook.Assignment) →
  Cook.evaluate
      (rejectWidthGadget payload)
      (extendCookAssignment false payloadAssignment)
  ≡
  Cook.evaluate payload payloadAssignment
rejectWidthGadgetFalseGuardRecoversPayload
    payload
    payloadAssignment =
  shiftCookEvaluation
    payload
    (extendCookAssignment false payloadAssignment)

------------------------------------------------------------------------
-- Hence distinct payload Boolean functions remain distinct inside the reject
-- gadgets: any distinguishing payload assignment extends with guard=false.
------------------------------------------------------------------------

rejectGadgetEqualityImpliesPayloadEquality :
  (left right : Cook.BooleanFormula) →
  ((assignment : Cook.Assignment) →
    Cook.evaluate
      (rejectWidthGadget left)
      assignment
    ≡
    Cook.evaluate
      (rejectWidthGadget right)
      assignment) →
  (payloadAssignment : Cook.Assignment) →
  Cook.evaluate left payloadAssignment
  ≡
  Cook.evaluate right payloadAssignment
rejectGadgetEqualityImpliesPayloadEquality
    left
    right
    gadgetEqual
    payloadAssignment =
  trans
    (sym
      (rejectWidthGadgetFalseGuardRecoversPayload
        left payloadAssignment))
    (trans
      (gadgetEqual
        (extendCookAssignment false payloadAssignment))
      (rejectWidthGadgetFalseGuardRecoversPayload
        right payloadAssignment))

------------------------------------------------------------------------
-- Accept branch: forced UNSAT.
------------------------------------------------------------------------

acceptCollapseGadgetUnsatisfiable :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable (acceptCollapseGadget payload) →
  ⊥
acceptCollapseGadgetUnsatisfiable
    payload
    witness =
  trueNotFalse
    (Cook.Satisfiable.evaluatesTrue witness)

------------------------------------------------------------------------
-- Exact diagonal polarity for the asymmetric gadget:
--
-- reject=true  => SAT
-- reject=false => UNSAT
--
-- while reject=true still contains a literal Shannon child equal to the
-- shifted payload function.
------------------------------------------------------------------------

asymmetricRejectBranchPreservesWidthAndForcesSAT :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable
      (diagonalAsymmetricGadget true payload)
  ×
  ((payloadAssignment : Cook.Assignment) →
    Cook.evaluate
      (diagonalAsymmetricGadget true payload)
      (extendCookAssignment false payloadAssignment)
    ≡
    Cook.evaluate payload payloadAssignment)
asymmetricRejectBranchPreservesWidthAndForcesSAT payload =
  rejectWidthGadgetSatisfiable payload
  ,
  rejectWidthGadgetFalseGuardRecoversPayload payload

asymmetricAcceptBranchForcesUNSAT :
  (payload : Cook.BooleanFormula) →
  Cook.Satisfiable
      (diagonalAsymmetricGadget false payload) →
  ⊥
asymmetricAcceptBranchForcesUNSAT =
  acceptCollapseGadgetUnsatisfiable

------------------------------------------------------------------------
-- This defeats the strongest possible global width-destruction conjecture:
-- diagonal SAT-polarity compatibility ALONE does not force width erasure.
--
-- On a rejected quote, an arbitrary payload can remain exactly recoverable in
-- a future Shannon child while the body is satisfiable immediately via the
-- guard=true branch.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- CONCRETE REFUTATION OF "POLARITY COMPATIBILITY FORCES WIDTH ERASURE"
------------------------------------------------------------------------

payloadVariable0 :
  Cook.BooleanFormula
payloadVariable0 =
  Cook.variable zero

payloadNotVariable0 :
  Cook.BooleanFormula
payloadNotVariable0 =
  Cook.negate
    (Cook.variable zero)

payloadDistinguishingAssignment :
  Cook.Assignment
payloadDistinguishingAssignment zero =
  false
payloadDistinguishingAssignment (suc index) =
  false

rejectGadgetsRemainSemanticallyDistinct :
  Cook.evaluate
      (rejectWidthGadget payloadVariable0)
      (extendCookAssignment
        false
        payloadDistinguishingAssignment)
  ≡
  Cook.evaluate
      (rejectWidthGadget payloadNotVariable0)
      (extendCookAssignment
        false
        payloadDistinguishingAssignment)
  →
  ⊥
rejectGadgetsRemainSemanticallyDistinct ()

record PolarityCompatiblePair : Set where
  constructor polarity-compatible-pair
  field
    leftBody rightBody :
      Cook.BooleanFormula

    leftSatisfiable :
      Cook.Satisfiable leftBody

    rightSatisfiable :
      Cook.Satisfiable rightBody

    semanticallyDistinct :
      ((assignment : Cook.Assignment) →
        Cook.evaluate leftBody assignment
        ≡
        Cook.evaluate rightBody assignment)
      →
      ⊥

open PolarityCompatiblePair public

rejectPolarityDoesNotForceSemanticCollapse :
  PolarityCompatiblePair
rejectPolarityDoesNotForceSemanticCollapse =
  polarity-compatible-pair
    (rejectWidthGadget payloadVariable0)
    (rejectWidthGadget payloadNotVariable0)
    (rejectWidthGadgetSatisfiable payloadVariable0)
    (rejectWidthGadgetSatisfiable payloadNotVariable0)
    (λ equalEverywhere →
      rejectGadgetsRemainSemanticallyDistinct
        (equalEverywhere
          (extendCookAssignment
            false
            payloadDistinguishingAssignment)))

------------------------------------------------------------------------
-- Therefore any width-destruction theorem must use MORE than the extensional
-- diagonal polarity condition.  It must exploit the actual finite-code body,
-- quotation dependence, construction budget, or another special law of the
-- SAT-diagonal implementation.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- LOCAL GADGET VS FULL DIAGONAL BODY
--
-- The asymmetric reject gadget is locally compatible with the diagonal
-- polarity condition at any quote the candidate rejects.  But a FULL
-- SATDiagonalBody must satisfy that condition for every quote, including the
-- compiler-generated fixed-point quote.  Existing infrastructure already
-- proves that a full body + diagonal compiler yields a concrete SAT decision
-- failure.
--
-- So the positive gadget does not bypass the main theorem: its unresolved step
-- is precisely compiling the quote-dependent candidate branch for ALL quotes.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Cleaner local compatibility package without dependent projection noise.
------------------------------------------------------------------------

LocalDiagonalPolarity :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula} →
  Direct.PolynomialSATDeciderCandidate cost →
  Cook.BooleanFormula →
  Cook.BooleanFormula →
  Set
LocalDiagonalPolarity candidate quoted body =
  (Direct.decide candidate quoted ≡ false →
    Cook.Satisfiable body)
  ×
  (Cook.Satisfiable body →
    Direct.decide candidate quoted ≡ false)

rejectWidthGadgetLocallyDiagonalCompatible :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {anchored : Direct.AnchoredPolynomialSATDeciderCandidate cost}
    {quoted payload : Cook.BooleanFormula} →
  Direct.decide
      (Direct.candidate anchored)
      quoted
    ≡ false →
  LocalDiagonalPolarity
    (Direct.candidate anchored)
    quoted
    (rejectWidthGadget payload)
rejectWidthGadgetLocallyDiagonalCompatible rejected =
  (λ _ → rejectWidthGadgetSatisfiable _)
  ,
  (λ _ → rejected)

------------------------------------------------------------------------
-- Full-body promotion is exactly the already-live SAT failure seam.
------------------------------------------------------------------------

fullWidthCompatibleBodyStillYieldsDecisionFailure :
  ∀ {cost : PR.PolynomialCostModel Cook.BooleanFormula}
    {candidate : Direct.PolynomialSATDeciderCandidate cost}
    {system : TotalKleene.SpecializingProgramSystem}
    {view : Diagonal.CookFormulaOutputView system}
    {dynamicInput : TotalKleene.Input system} →
  TotalKleene.DiagonalCompiler system →
  Diagonal.SATDiagonalBody
    candidate
    system
    view
    dynamicInput →
  Direct.SATDecisionFailure candidate
fullWidthCompatibleBodyStillYieldsDecisionFailure =
  Diagonal.kleeneBodyGivesSATDecisionFailure

------------------------------------------------------------------------
-- Therefore:
--
--   local rejected-branch width preservation   CONSTRUCTED;
--   polarity-only width destruction            REFUTED;
--   full all-quotes body realization           still the hard SAT-failure seam.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- FRONTIER CONSEQUENCE
--
-- The universality fork is partly resolved:
--
--   generic self-specialization
--     DOES NOT
--   imply small FutureEquivalent / residual-function width.
--
-- The fixed-point machinery can emit arbitrary formula syntax.
--
-- Hence a positive Q1 width theorem must use a law of the actual SAT-diagonal
-- primitive body / candidate interaction which is absent from this echo model.
--
-- The remaining high-alpha falsification question is narrower:
--
--   does the SPECIFIC SAT-diagonal body still admit a width-preserving payload
--   embedding, or does its candidate/rejection semantics forbid one?
------------------------------------------------------------------------
