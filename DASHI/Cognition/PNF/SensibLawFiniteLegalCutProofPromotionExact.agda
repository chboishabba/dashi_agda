module DASHI.Cognition.PNF.SensibLawFiniteLegalCutProofPromotionExact where

------------------------------------------------------------------------
-- FINITE CUT CANDIDATE -> PROOF-RELEVANT MINIMAL CUT
--
-- The executable singleton cuts for Mabo and Cullen are promoted on the exact
-- same graphs/facts/goals. Pabai remains outside this lane because its current
-- target is already unreachable and therefore belongs to repair search.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.SensibLawUniversalLegalRuleAlgebraExact as Algebra
import DASHI.Cognition.PNF.SensibLawFiniteExecutableLegalSearchExact as Search
import DASHI.Cognition.PNF.SensibLawFiniteLegalSearchRegressionExact as Regression
import DASHI.Cognition.PNF.SensibLawCullenPublicAuthorityDutyCalibrationExact as Cullen

------------------------------------------------------------------------
-- Mabo singleton final-rule cut.
--
-- `Derivation ... maboSurvival` indexes the final proposition, so the first
-- graph rule (whose conclusion is radical title) is not a possible top-level
-- constructor after dependent unification. The only surviving byRule case is
-- the survival rule itself, whose Enabled witness contradicts membership in the
-- disabled singleton.
------------------------------------------------------------------------

maboSurvivalCut :
  Algebra.CutSet Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboSurvivalCut = Algebra.cut-set
  (Regression.maboSurvivalRule ∷ [])
  block
  where
    block :
      Algebra.Derivation
        Regression.maboGraph
        Regression.maboFacts
        (λ r → Algebra._∈_ r (Regression.maboSurvivalRule ∷ []) → ⊥)
        Regression.maboSurvival → ⊥
    block (Algebra.fromFact ())
    block (Algebra.byRule (Algebra.there Algebra.here) enabled premises exceptions defeaters) =
      enabled Algebra.here
    block (Algebra.byRule (Algebra.there (Algebra.there ())) enabled premises exceptions defeaters)

maboSurvivalMinimalCut :
  Algebra.MinimalCut Regression.maboGraph Regression.maboFacts Regression.maboSurvival
maboSurvivalMinimalCut = Algebra.minimal-cut
  maboSurvivalCut
  essential
  where
    essential :
      ∀ {r} →
      Algebra._∈_ r (Regression.maboSurvivalRule ∷ []) →
      Algebra.Derivation
        Regression.maboGraph Regression.maboFacts
        (λ s → (s ≡ r) ⊎
          (Algebra._∈_ s (Regression.maboSurvivalRule ∷ []) → ⊥))
        Regression.maboSurvival
    essential Algebra.here =
      Algebra.byRule
        (Algebra.there Algebra.here)
        (inj₁ refl)
        (Algebra._∷_ radical
          (Algebra._∷_ preExisting
            (Algebra._∷_ notExtinguished Algebra.[])))
        Algebra.[]
        Algebra.[]
      where
        sovereignty :
          Algebra.Derivation
            Regression.maboGraph Regression.maboFacts
            (λ s → (s ≡ Regression.maboSurvivalRule) ⊎
              (Algebra._∈_ s (Regression.maboSurvivalRule ∷ []) → ⊥))
            Regression.maboSovereignty
        sovereignty = Algebra.fromFact Algebra.here

        radical :
          Algebra.Derivation
            Regression.maboGraph Regression.maboFacts
            (λ s → (s ≡ Regression.maboSurvivalRule) ⊎
              (Algebra._∈_ s (Regression.maboSurvivalRule ∷ []) → ⊥))
            Regression.maboRadicalTitle
        radical = Algebra.byRule
          Algebra.here
          (inj₂ (λ ()))
          (Algebra._∷_ sovereignty Algebra.[])
          Algebra.[] Algebra.[]

        preExisting :
          Algebra.Derivation
            Regression.maboGraph Regression.maboFacts
            (λ s → (s ≡ Regression.maboSurvivalRule) ⊎
              (Algebra._∈_ s (Regression.maboSurvivalRule ∷ []) → ⊥))
            Regression.maboPreExistingNativeTitle
        preExisting = Algebra.fromFact (Algebra.there Algebra.here)

        notExtinguished :
          Algebra.Derivation
            Regression.maboGraph Regression.maboFacts
            (λ s → (s ≡ Regression.maboSurvivalRule) ⊎
              (Algebra._∈_ s (Regression.maboSurvivalRule ∷ []) → ⊥))
            Regression.maboNotExtinguished
        notExtinguished = Algebra.fromFact
          (Algebra.there (Algebra.there Algebra.here))
    essential (Algebra.there ())

maboCutPromotion :
  Search.CutPromotion
    2 Regression.maboGraph Regression.maboFacts Regression.maboSurvival
    (Search.ruleKey Regression.maboSurvivalRule ∷ [])
maboCutPromotion = Search.cut-promotion refl maboSurvivalMinimalCut

------------------------------------------------------------------------
-- Cullen singleton rule cut.
------------------------------------------------------------------------

cullenDutyCut :
  Algebra.CutSet Regression.cullenGraph Regression.cullenFacts
    Cullen.cullenDutyProposition
cullenDutyCut = Algebra.cut-set
  (Regression.cullenDutyRule ∷ [])
  block
  where
    block :
      Algebra.Derivation
        Regression.cullenGraph Regression.cullenFacts
        (λ r → Algebra._∈_ r (Regression.cullenDutyRule ∷ []) → ⊥)
        Cullen.cullenDutyProposition → ⊥
    block (Algebra.fromFact ())
    block (Algebra.byRule Algebra.here enabled premises exceptions defeaters) =
      enabled Algebra.here
    block (Algebra.byRule (Algebra.there ()) enabled premises exceptions defeaters)

cullenDutyMinimalCut :
  Algebra.MinimalCut Regression.cullenGraph Regression.cullenFacts
    Cullen.cullenDutyProposition
cullenDutyMinimalCut = Algebra.minimal-cut
  cullenDutyCut
  essential
  where
    essential :
      ∀ {r} →
      Algebra._∈_ r (Regression.cullenDutyRule ∷ []) →
      Algebra.Derivation
        Regression.cullenGraph Regression.cullenFacts
        (λ s → (s ≡ r) ⊎
          (Algebra._∈_ s (Regression.cullenDutyRule ∷ []) → ⊥))
        Cullen.cullenDutyProposition
    essential Algebra.here =
      Algebra.byRule
        Algebra.here
        (inj₁ refl)
        (Algebra._∷_ positiveAct
          (Algebra._∷_ foreseeable
            (Algebra._∷_ statutoryFunction Algebra.[])))
        Algebra.[] Algebra.[]
      where
        positiveAct :
          Algebra.Derivation
            Regression.cullenGraph Regression.cullenFacts
            (λ s → (s ≡ Regression.cullenDutyRule) ⊎
              (Algebra._∈_ s (Regression.cullenDutyRule ∷ []) → ⊥))
            Cullen.positiveOperationalAct
        positiveAct = Algebra.fromFact Algebra.here

        foreseeable :
          Algebra.Derivation
            Regression.cullenGraph Regression.cullenFacts
            (λ s → (s ≡ Regression.cullenDutyRule) ⊎
              (Algebra._∈_ s (Regression.cullenDutyRule ∷ []) → ⊥))
            Cullen.foreseeablePhysicalInjuryRisk
        foreseeable = Algebra.fromFact (Algebra.there Algebra.here)

        statutoryFunction :
          Algebra.Derivation
            Regression.cullenGraph Regression.cullenFacts
            (λ s → (s ≡ Regression.cullenDutyRule) ⊎
              (Algebra._∈_ s (Regression.cullenDutyRule ∷ []) → ⊥))
            Cullen.statutoryPoliceFunction
        statutoryFunction = Algebra.fromFact
          (Algebra.there (Algebra.there Algebra.here))
    essential (Algebra.there ())

cullenCutPromotion :
  Search.CutPromotion
    1 Regression.cullenGraph Regression.cullenFacts Cullen.cullenDutyProposition
    (Search.ruleKey Regression.cullenDutyRule ∷ [])
cullenCutPromotion = Search.cut-promotion refl cullenDutyMinimalCut

------------------------------------------------------------------------
-- Pabai firewall.
------------------------------------------------------------------------

data PabaiAlreadyUnreachableTargetHasPromotedCurrentRouteCut : Set where

pabaiCurrentRouteHasNoPromotedCut :
  PabaiAlreadyUnreachableTargetHasPromotedCurrentRouteCut → ⊥
pabaiCurrentRouteHasNoPromotedCut ()
