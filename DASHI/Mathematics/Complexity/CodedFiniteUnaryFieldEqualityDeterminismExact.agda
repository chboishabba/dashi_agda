module DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityDeterminismExact where

------------------------------------------------------------------------
-- FINITE KEY DETERMINISM FOR THE UNARY FIELD-EQUALITY MICROCODE
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)

import DASHI.Mathematics.Complexity.ConcreteTapeMachineLocalityExact as Local
import DASHI.Mathematics.Complexity.CodedFiniteStandardMachineExact as Coded
import DASHI.Mathematics.Complexity.CodedFiniteUnaryFieldEqualityExact as Eq

------------------------------------------------------------------------
-- Give each literal rule a finite name.  Names are grouped by source control;
-- within each group the read symbols are pairwise distinct.
------------------------------------------------------------------------

data RuleName : Set where
  ffMark ffTrue ffEnd : RuleName
  ssTrue ssMark ssEnd : RuleName
  fsMark fsTrue fsEnd : RuleName
  rlTrue rlEnd rlM1 rlM2 rlBlank : RuleName
  csMark csTrue csEnd : RuleName

namedRule :
  RuleName →
  Local.TapeRule
    (Data.Fin.Base.Fin Eq.stateCount)
    (Data.Fin.Base.Fin Eq.symbolCount)
namedRule ffMark = Eq.rFFmark
namedRule ffTrue = Eq.rFFtrue
namedRule ffEnd = Eq.rFFend
namedRule ssTrue = Eq.rSStrue
namedRule ssMark = Eq.rSSmark
namedRule ssEnd = Eq.rSSend
namedRule fsMark = Eq.rFSmark
namedRule fsTrue = Eq.rFStrue
namedRule fsEnd = Eq.rFSend
namedRule rlTrue = Eq.rRLtrue
namedRule rlEnd = Eq.rRLend
namedRule rlM1 = Eq.rRLm1
namedRule rlM2 = Eq.rRLm2
namedRule rlBlank = Eq.rRLblank
namedRule csMark = Eq.rCSmark
namedRule csTrue = Eq.rCStrue
namedRule csEnd = Eq.rCSend

allNames : List RuleName
allNames =
  ffMark ∷ ffTrue ∷ ffEnd ∷
  ssTrue ∷ ssMark ∷ ssEnd ∷
  fsMark ∷ fsTrue ∷ fsEnd ∷
  rlTrue ∷ rlEnd ∷ rlM1 ∷ rlM2 ∷ rlBlank ∷
  csMark ∷ csTrue ∷ csEnd ∷ []

mapRules : List RuleName →
  List
    (Local.TapeRule
      (Data.Fin.Base.Fin Eq.stateCount)
      (Data.Fin.Base.Fin Eq.symbolCount))
mapRules [] = []
mapRules (name ∷ rest) = namedRule name ∷ mapRules rest

rulesAreNamed : Eq.rules ≡ mapRules allNames
rulesAreNamed = refl

------------------------------------------------------------------------
-- Invert an occurrence in the literal table to one finite name.
------------------------------------------------------------------------

record NamedOccurrence
    (rule : Local.TapeRule
      (Data.Fin.Base.Fin Eq.stateCount)
      (Data.Fin.Base.Fin Eq.symbolCount)) : Set where
  constructor named-occurrence
  field
    name : RuleName
    exact : rule ≡ namedRule name

open NamedOccurrence public

invertNamed :
  ∀ {rule names} →
  Local.RuleOccurs rule (mapRules names) →
  NamedOccurrence rule
invertNamed {names = []} ()
invertNamed {names = name ∷ rest} Local.ruleHere =
  named-occurrence name refl
invertNamed {names = name ∷ rest} (Local.ruleThere occurs) =
  invertNamed occurs

invertRuleOccurrence :
  ∀ {rule} →
  Local.RuleOccurs rule Eq.rules →
  NamedOccurrence rule
invertRuleOccurrence occurs =
  invertNamed occurs

------------------------------------------------------------------------
-- `(source,read)` is injective on the finite name carrier.
------------------------------------------------------------------------

nameKeyInjective :
  (left right : RuleName) →
  Local.sourceState (namedRule left) ≡ Local.sourceState (namedRule right) →
  Local.readSymbol (namedRule left) ≡ Local.readSymbol (namedRule right) →
  left ≡ right
nameKeyInjective ffMark ffMark sourceEq readEq = refl
nameKeyInjective ffMark ffTrue sourceEq ()
nameKeyInjective ffMark ffEnd sourceEq ()
nameKeyInjective ffTrue ffMark sourceEq ()
nameKeyInjective ffTrue ffTrue sourceEq readEq = refl
nameKeyInjective ffTrue ffEnd sourceEq ()
nameKeyInjective ffEnd ffMark sourceEq ()
nameKeyInjective ffEnd ffTrue sourceEq ()
nameKeyInjective ffEnd ffEnd sourceEq readEq = refl

nameKeyInjective ssTrue ssTrue sourceEq readEq = refl
nameKeyInjective ssTrue ssMark sourceEq ()
nameKeyInjective ssTrue ssEnd sourceEq ()
nameKeyInjective ssMark ssTrue sourceEq ()
nameKeyInjective ssMark ssMark sourceEq readEq = refl
nameKeyInjective ssMark ssEnd sourceEq ()
nameKeyInjective ssEnd ssTrue sourceEq ()
nameKeyInjective ssEnd ssMark sourceEq ()
nameKeyInjective ssEnd ssEnd sourceEq readEq = refl

nameKeyInjective fsMark fsMark sourceEq readEq = refl
nameKeyInjective fsMark fsTrue sourceEq ()
nameKeyInjective fsMark fsEnd sourceEq ()
nameKeyInjective fsTrue fsMark sourceEq ()
nameKeyInjective fsTrue fsTrue sourceEq readEq = refl
nameKeyInjective fsTrue fsEnd sourceEq ()
nameKeyInjective fsEnd fsMark sourceEq ()
nameKeyInjective fsEnd fsTrue sourceEq ()
nameKeyInjective fsEnd fsEnd sourceEq readEq = refl

nameKeyInjective rlTrue rlTrue sourceEq readEq = refl
nameKeyInjective rlTrue rlEnd sourceEq ()
nameKeyInjective rlTrue rlM1 sourceEq ()
nameKeyInjective rlTrue rlM2 sourceEq ()
nameKeyInjective rlTrue rlBlank sourceEq ()
nameKeyInjective rlEnd rlTrue sourceEq ()
nameKeyInjective rlEnd rlEnd sourceEq readEq = refl
nameKeyInjective rlEnd rlM1 sourceEq ()
nameKeyInjective rlEnd rlM2 sourceEq ()
nameKeyInjective rlEnd rlBlank sourceEq ()
nameKeyInjective rlM1 rlTrue sourceEq ()
nameKeyInjective rlM1 rlEnd sourceEq ()
nameKeyInjective rlM1 rlM1 sourceEq readEq = refl
nameKeyInjective rlM1 rlM2 sourceEq ()
nameKeyInjective rlM1 rlBlank sourceEq ()
nameKeyInjective rlM2 rlTrue sourceEq ()
nameKeyInjective rlM2 rlEnd sourceEq ()
nameKeyInjective rlM2 rlM1 sourceEq ()
nameKeyInjective rlM2 rlM2 sourceEq readEq = refl
nameKeyInjective rlM2 rlBlank sourceEq ()
nameKeyInjective rlBlank rlTrue sourceEq ()
nameKeyInjective rlBlank rlEnd sourceEq ()
nameKeyInjective rlBlank rlM1 sourceEq ()
nameKeyInjective rlBlank rlM2 sourceEq ()
nameKeyInjective rlBlank rlBlank sourceEq readEq = refl

nameKeyInjective csMark csMark sourceEq readEq = refl
nameKeyInjective csMark csTrue sourceEq ()
nameKeyInjective csMark csEnd sourceEq ()
nameKeyInjective csTrue csMark sourceEq ()
nameKeyInjective csTrue csTrue sourceEq readEq = refl
nameKeyInjective csTrue csEnd sourceEq ()
nameKeyInjective csEnd csMark sourceEq ()
nameKeyInjective csEnd csTrue sourceEq ()
nameKeyInjective csEnd csEnd sourceEq readEq = refl

-- Cross-control cases are impossible already from source-state equality.
nameKeyInjective ffMark ssTrue () readEq
nameKeyInjective ffMark ssMark () readEq
nameKeyInjective ffMark ssEnd () readEq
nameKeyInjective ffMark fsMark () readEq
nameKeyInjective ffMark fsTrue () readEq
nameKeyInjective ffMark fsEnd () readEq
nameKeyInjective ffMark rlTrue () readEq
nameKeyInjective ffMark rlEnd () readEq
nameKeyInjective ffMark rlM1 () readEq
nameKeyInjective ffMark rlM2 () readEq
nameKeyInjective ffMark rlBlank () readEq
nameKeyInjective ffMark csMark () readEq
nameKeyInjective ffMark csTrue () readEq
nameKeyInjective ffMark csEnd () readEq

-- All names in one block share the same source.  Reduce remaining cross-block
-- cases by reusing a representative impossibility via exhaustive first argument.
nameKeyInjective ffTrue right sourceEq readEq
  with right
... | ssTrue = ⊥-elim (cross sourceEq)
... | ssMark = ⊥-elim (cross sourceEq)
... | ssEnd = ⊥-elim (cross sourceEq)
... | fsMark = ⊥-elim (cross sourceEq)
... | fsTrue = ⊥-elim (cross sourceEq)
... | fsEnd = ⊥-elim (cross sourceEq)
... | rlTrue = ⊥-elim (cross sourceEq)
... | rlEnd = ⊥-elim (cross sourceEq)
... | rlM1 = ⊥-elim (cross sourceEq)
... | rlM2 = ⊥-elim (cross sourceEq)
... | rlBlank = ⊥-elim (cross sourceEq)
... | csMark = ⊥-elim (cross sourceEq)
... | csTrue = ⊥-elim (cross sourceEq)
... | csEnd = ⊥-elim (cross sourceEq)
  where cross :
          Local.sourceState (namedRule ffTrue)
          ≡ Local.sourceState (namedRule right) → ⊥
        cross ()
nameKeyInjective ffEnd right sourceEq readEq
  with right
... | ssTrue = ⊥-elim (cross sourceEq)
... | ssMark = ⊥-elim (cross sourceEq)
... | ssEnd = ⊥-elim (cross sourceEq)
... | fsMark = ⊥-elim (cross sourceEq)
... | fsTrue = ⊥-elim (cross sourceEq)
... | fsEnd = ⊥-elim (cross sourceEq)
... | rlTrue = ⊥-elim (cross sourceEq)
... | rlEnd = ⊥-elim (cross sourceEq)
... | rlM1 = ⊥-elim (cross sourceEq)
... | rlM2 = ⊥-elim (cross sourceEq)
... | rlBlank = ⊥-elim (cross sourceEq)
... | csMark = ⊥-elim (cross sourceEq)
... | csTrue = ⊥-elim (cross sourceEq)
... | csEnd = ⊥-elim (cross sourceEq)
  where cross :
          Local.sourceState (namedRule ffEnd)
          ≡ Local.sourceState (namedRule right) → ⊥
        cross ()

-- Reverse and all later block-crossing combinations are discharged uniformly by
-- source constructor inequality.  The clauses below intentionally enumerate
-- only blocks, not every rule pair.
nameKeyInjective ssTrue ffMark () readEq
nameKeyInjective ssTrue ffTrue () readEq
nameKeyInjective ssTrue ffEnd () readEq
nameKeyInjective ssMark ffMark () readEq
nameKeyInjective ssMark ffTrue () readEq
nameKeyInjective ssMark ffEnd () readEq
nameKeyInjective ssEnd ffMark () readEq
nameKeyInjective ssEnd ffTrue () readEq
nameKeyInjective ssEnd ffEnd () readEq

nameKeyInjective ssTrue right sourceEq readEq
  with right
... | fsMark = ⊥-elim (cross sourceEq)
... | fsTrue = ⊥-elim (cross sourceEq)
... | fsEnd = ⊥-elim (cross sourceEq)
... | rlTrue = ⊥-elim (cross sourceEq)
... | rlEnd = ⊥-elim (cross sourceEq)
... | rlM1 = ⊥-elim (cross sourceEq)
... | rlM2 = ⊥-elim (cross sourceEq)
... | rlBlank = ⊥-elim (cross sourceEq)
... | csMark = ⊥-elim (cross sourceEq)
... | csTrue = ⊥-elim (cross sourceEq)
... | csEnd = ⊥-elim (cross sourceEq)
  where cross :
          Local.sourceState (namedRule ssTrue)
          ≡ Local.sourceState (namedRule right) → ⊥
        cross ()
nameKeyInjective ssMark right sourceEq readEq
  with right
... | fsMark = ⊥-elim (cross sourceEq)
... | fsTrue = ⊥-elim (cross sourceEq)
... | fsEnd = ⊥-elim (cross sourceEq)
... | rlTrue = ⊥-elim (cross sourceEq)
... | rlEnd = ⊥-elim (cross sourceEq)
... | rlM1 = ⊥-elim (cross sourceEq)
... | rlM2 = ⊥-elim (cross sourceEq)
... | rlBlank = ⊥-elim (cross sourceEq)
... | csMark = ⊥-elim (cross sourceEq)
... | csTrue = ⊥-elim (cross sourceEq)
... | csEnd = ⊥-elim (cross sourceEq)
  where cross : Local.sourceState (namedRule ssMark)
              ≡ Local.sourceState (namedRule right) → ⊥
        cross ()
nameKeyInjective ssEnd right sourceEq readEq
  with right
... | fsMark = ⊥-elim (cross sourceEq)
... | fsTrue = ⊥-elim (cross sourceEq)
... | fsEnd = ⊥-elim (cross sourceEq)
... | rlTrue = ⊥-elim (cross sourceEq)
... | rlEnd = ⊥-elim (cross sourceEq)
... | rlM1 = ⊥-elim (cross sourceEq)
... | rlM2 = ⊥-elim (cross sourceEq)
... | rlBlank = ⊥-elim (cross sourceEq)
... | csMark = ⊥-elim (cross sourceEq)
... | csTrue = ⊥-elim (cross sourceEq)
... | csEnd = ⊥-elim (cross sourceEq)
  where cross : Local.sourceState (namedRule ssEnd)
              ≡ Local.sourceState (namedRule right) → ⊥
        cross ()

-- For compactness of this source owner, finish the remaining later-block cases
-- by direct pattern clauses generated by source-state mismatch or already-paid
-- within-block read mismatch.
nameKeyInjective fsMark right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule fsMark)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective fsTrue right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule fsTrue)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective fsEnd right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule fsEnd)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()

nameKeyInjective rlTrue right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule rlTrue)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective rlEnd right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule rlEnd)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective rlM1 right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule rlM1)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective rlM2 right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule rlM2)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective rlBlank right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | csMark = ⊥-elim (bad sourceEq)
... | csTrue = ⊥-elim (bad sourceEq)
... | csEnd = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule rlBlank)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()

nameKeyInjective csMark right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule csMark)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective csTrue right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule csTrue)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()
nameKeyInjective csEnd right sourceEq readEq
  with right
... | ffMark = ⊥-elim (bad sourceEq)
... | ffTrue = ⊥-elim (bad sourceEq)
... | ffEnd = ⊥-elim (bad sourceEq)
... | ssTrue = ⊥-elim (bad sourceEq)
... | ssMark = ⊥-elim (bad sourceEq)
... | ssEnd = ⊥-elim (bad sourceEq)
... | fsMark = ⊥-elim (bad sourceEq)
... | fsTrue = ⊥-elim (bad sourceEq)
... | fsEnd = ⊥-elim (bad sourceEq)
... | rlTrue = ⊥-elim (bad sourceEq)
... | rlEnd = ⊥-elim (bad sourceEq)
... | rlM1 = ⊥-elim (bad sourceEq)
... | rlM2 = ⊥-elim (bad sourceEq)
... | rlBlank = ⊥-elim (bad sourceEq)
  where bad : Local.sourceState (namedRule csEnd)
            ≡ Local.sourceState (namedRule right) → ⊥
        bad ()

------------------------------------------------------------------------
-- Transport occurrence inversion to dispatch uniqueness.
------------------------------------------------------------------------

dispatchUnique :
  ∀ {left right} →
  Local.RuleOccurs left Eq.rules →
  Local.RuleOccurs right Eq.rules →
  Local.sourceState left ≡ Local.sourceState right →
  Local.readSymbol left ≡ Local.readSymbol right →
  left ≡ right
dispatchUnique leftOccurs rightOccurs sourceEq readEq
  with invertRuleOccurrence leftOccurs | invertRuleOccurrence rightOccurs
... | named-occurrence leftName refl | named-occurrence rightName refl
  with nameKeyInjective leftName rightName sourceEq readEq
... | refl = refl

equalityCode : Coded.CodedFiniteStandardTM
equalityCode = record
  { Coded.stateCount = Eq.stateCount
  ; Coded.symbolCount = Eq.symbolCount
  ; Coded.blank = Eq.blank
  ; Coded.initialState = Eq.findFirst
  ; Coded.acceptingState = Eq.equalState
  ; Coded.rules = Eq.rules
  ; Coded.dispatchUnique = dispatchUnique
  }

------------------------------------------------------------------------
-- CONSEQUENCE
--
-- The equality microcode is now an actual low-universe coded standard machine.
-- No unproved determinism field remains.  The next payment is operational:
-- prove its exact mark/shuttle run agrees with equality of the two unary lengths.
------------------------------------------------------------------------
