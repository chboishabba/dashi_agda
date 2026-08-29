module DASHI.Foundations.Wette1969Rule915CanonicalP145PremisesExact where

------------------------------------------------------------------------
-- WETTE 1969 RULE 9.1.5: CANONICAL PURE p.145 PREMISE VECTOR
--
-- Primary source: Eduard Wette, 1969, printed p.145.
--
-- Wette's rule schemata use exactly nineteen word variables.  The historical
-- signature already represents those by Fin 19.  This module fixes one concrete
-- source-order assignment
--
--   U,V,W,U1..U6,V1..V5,W1..W5
--
-- and constructs all twenty-seven premise formulae literally from the p.145
-- surface.  This closes the source-identity part of the 9.1.5 reconstruction:
-- there are no opaque Formula slots and premises 18/27 are no longer represented
-- merely by semantic labels.
--
-- The module proves syntax identity only.  It does not claim that any of the
-- twenty-seven premises is derivable for this canonical schema assignment.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import Data.Fin as Fin

import DASHI.Foundations.Wette1969HistoricalSignatureExact as Signature
import DASHI.Foundations.Wette1969JudgementConstructorsExact as Judgment
import DASHI.Foundations.Wette1969CriticalRuleDependencyExact as Critical
import DASHI.Foundations.Wette1969Rule915PredicateProducerExact as Rule915
import DASHI.Foundations.Wette1969RuleRevisionExact as Revision
import DASHI.Foundations.Wette1969InitialRuleTranscriptionExact as RuleBody

WordTerm = Signature.WordTerm
Formula = Signature.Formula

------------------------------------------------------------------------
-- The nineteen literal rule-schema variables, in source order.
------------------------------------------------------------------------

U V W U1 U2 U3 U4 U5 U6 V1 V2 V3 V4 V5 W1 W2 W3 W4 W5 : WordTerm
U  = Signature.variableWordTerm Fin.zero
V  = Signature.variableWordTerm (Fin.suc Fin.zero)
W  = Signature.variableWordTerm (Fin.suc (Fin.suc Fin.zero))
U1 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc Fin.zero)))
U2 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))
U3 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))
U4 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))
U5 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))
U6 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))
V1 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))
V2 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))
V3 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))
V4 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))
V5 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))
W1 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))
W2 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))
W3 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))
W4 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero)))))))))))))))))
W5 = Signature.variableWordTerm (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc (Fin.suc Fin.zero))))))))))))))))))

------------------------------------------------------------------------
-- Pure word constructors used on p.145.
------------------------------------------------------------------------

juxtapose : WordTerm → WordTerm → WordTerm
juxtapose left right =
  Signature.binaryWordTerm Signature.juxtapositionFunctor refl left right

implication : WordTerm → WordTerm → WordTerm
implication left right =
  Signature.binaryWordTerm Signature.implicationFunctor refl left right

conjunction : WordTerm → WordTerm → WordTerm
conjunction left right =
  Signature.binaryWordTerm Signature.conjunctionFunctor refl left right

generalize : WordTerm → WordTerm → WordTerm
generalize binder body =
  Signature.binaryWordTerm Signature.generalizationFunctor refl binder body

------------------------------------------------------------------------
-- Dense words that p.145 prints explicitly.
------------------------------------------------------------------------

contextU1V1W1 : WordTerm
contextU1V1W1 = juxtapose U1 (juxtapose V1 W1)

contextV4V1W1 : WordTerm
contextV4V1W1 = juxtapose V4 (juxtapose V1 W1)

abbreviation16Word : WordTerm
abbreviation16Word =
  generalize V4
    (implication (juxtapose V1 V4)
      (implication (juxtapose W1 V5) (juxtapose W3 V4)))

abbreviation17Word : WordTerm
abbreviation17Word =
  generalize V3
    (implication (juxtapose V1 V3)
      (implication U2 (juxtapose W3 V3)))

premise18ConsequentWord : WordTerm
premise18ConsequentWord =
  implication U3
    (implication (juxtapose V1 V3) (juxtapose W3 V3))

contextW4W5 : WordTerm
contextW4W5 = juxtapose W4 W5

abbreviation26Word : WordTerm
abbreviation26Word =
  generalize V4
    (implication (juxtapose V1 V4)
      (implication (juxtapose W1 V5)
        (conjunction
          (implication (juxtapose W4 V4) (juxtapose W5 V4))
          (implication (juxtapose W5 V4) (juxtapose W4 V4)))))

premise27ConsequentWord : WordTerm
premise27ConsequentWord =
  implication (juxtapose V1 V3)
    (implication U6
      (conjunction
        (implication U4 U5)
        (implication U5 U4)))

------------------------------------------------------------------------
-- The literal twenty-seven p.145 premises.
------------------------------------------------------------------------

p145Premise : Critical.Premise915 → Formula
p145Premise Critical.p01 = Judgment.duplicates V W
p145Premise Critical.p02 = Judgment.predicateMarkArity V W2
p145Premise Critical.p03 = Judgment.distinctVariableTuple V V2
p145Premise Critical.p04 = Judgment.predicateSchema V V1
p145Premise Critical.p05 = Judgment.predicateSchema W W1
p145Premise Critical.p06 = Judgment.assertionSchemaNoPredicateQuantification U
p145Premise Critical.p07 = Judgment.assertionSchema U1
p145Premise Critical.p08 = Judgment.predicateMarkArity V W3
p145Premise Critical.p09 = Judgment.freeForSyntax W3 contextU1V1W1
p145Premise Critical.p10 = Judgment.distinctVariableTuple V V3
p145Premise Critical.p11 = Judgment.distinctVariableTuple V V4
p145Premise Critical.p12 = Judgment.freeForSyntax V3 V4
p145Premise Critical.p13 = Judgment.freeForSyntax V3 U1
p145Premise Critical.p14 = Judgment.freeForSyntax V3 contextV4V1W1
p145Premise Critical.p15 = Judgment.juxtapositionResult V4 V3 V5
p145Premise Critical.p16 = Judgment.abbreviates abbreviation16Word U2
p145Premise Critical.p17 = Judgment.abbreviates abbreviation17Word U3
p145Premise Critical.p18 = Judgment.implies U1 premise18ConsequentWord
p145Premise Critical.p19 = Judgment.predicateMarkArity V W4
p145Premise Critical.p20 = Judgment.predicateMarkArity V W5
p145Premise Critical.p21 = Judgment.freeForSyntax W4 W5
p145Premise Critical.p22 = Judgment.freeForSyntax contextW4W5 contextU1V1W1
p145Premise Critical.p23 = Judgment.freeForSyntax V3 U
p145Premise Critical.p24 =
  Judgment.substitution
    (juxtapose W2 V2) U (juxtapose W4 V3) U4
p145Premise Critical.p25 =
  Judgment.substitution
    (juxtapose W2 V2) U (juxtapose W5 V3) U5
p145Premise Critical.p26 = Judgment.abbreviates abbreviation26Word U6
p145Premise Critical.p27 = Judgment.implies U1 premise27ConsequentWord

canonicalP145Transcription : Rule915.Rule915PremiseTranscription
canonicalP145Transcription = Rule915.rule915PremiseTranscription p145Premise

------------------------------------------------------------------------
-- Regression receipts for the two former major-word holes and for the complete
-- finite slot surface.
------------------------------------------------------------------------

premise18IsLiteralP145NestedImplication :
  Rule915.premiseAt canonicalP145Transcription Critical.p18
    ≡ Judgment.implies U1
        (implication U3
          (implication (juxtapose V1 V3) (juxtapose W3 V3)))
premise18IsLiteralP145NestedImplication = refl

premise27IsLiteralP145IndependenceWord :
  Rule915.premiseAt canonicalP145Transcription Critical.p27
    ≡ Judgment.implies U1
        (implication (juxtapose V1 V3)
          (implication U6
            (conjunction
              (implication U4 U5)
              (implication U5 U4))))
premise27IsLiteralP145IndependenceWord = refl

allTwentySevenSlotsAreFixedByOneConcreteTranscription :
  (slot : Critical.Premise915) →
  Rule915.premiseAt canonicalP145Transcription slot ≡ p145Premise slot
allTwentySevenSlotsAreFixedByOneConcreteTranscription slot = refl

canonicalRule915PremiseCount :
  (recursivePredicate : WordTerm) →
  RuleBody.premiseCount
    (Rule915.rule9-1-5 canonicalP145Transcription V recursivePredicate) ≡ 27
canonicalRule915PremiseCount recursivePredicate = refl

canonicalRule915AddressIs915 :
  (recursivePredicate : WordTerm) →
  RuleBody.address
    (Rule915.rule9-1-5 canonicalP145Transcription V recursivePredicate)
    ≡ Revision.rule9-1-5
canonicalRule915AddressIs915 recursivePredicate = refl

record Wette1969Rule915CanonicalP145PremisesBoundary : Set where
  constructor wette1969Rule915CanonicalP145PremisesBoundary
  field
    nineteenSourceMetavariablesAssignedToHistoricalFin19 : Bool
    nineteenSourceMetavariablesAssignedToHistoricalFin19IsTrue :
      nineteenSourceMetavariablesAssignedToHistoricalFin19 ≡ true
    allTwentySevenP145PremisesNowOneConcreteTypedVector : Bool
    allTwentySevenP145PremisesNowOneConcreteTypedVectorIsTrue :
      allTwentySevenP145PremisesNowOneConcreteTypedVector ≡ true
    premise18DenseWordNoLongerOpaqueInCanonicalP145Surface : Bool
    premise18DenseWordNoLongerOpaqueInCanonicalP145SurfaceIsTrue :
      premise18DenseWordNoLongerOpaqueInCanonicalP145Surface ≡ true
    premise27DenseWordNoLongerOpaqueInCanonicalP145Surface : Bool
    premise27DenseWordNoLongerOpaqueInCanonicalP145SurfaceIsTrue :
      premise27DenseWordNoLongerOpaqueInCanonicalP145Surface ≡ true
    thisModuleClaimsDerivabilityOfAnyPremise : Bool
    thisModuleClaimsDerivabilityOfAnyPremiseIsFalse :
      thisModuleClaimsDerivabilityOfAnyPremise ≡ false

canonicalWette1969Rule915CanonicalP145PremisesBoundary :
  Wette1969Rule915CanonicalP145PremisesBoundary
canonicalWette1969Rule915CanonicalP145PremisesBoundary =
  wette1969Rule915CanonicalP145PremisesBoundary
    true refl true refl true refl true refl false refl
