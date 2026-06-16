module DASHI.Physics.Closure.GRPerturbationBoundShapeCore where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- GR perturbation bound shape core.
--
-- This module is carrier/receipt only.  It records the names and shapes of
-- the perturbation-bound claims that downstream modules may want to consume,
-- but it does not import, derive, or promote any local tensor formula law.
-- Any actual proof of the named bounds must come from concrete tensor formula
-- laws supplied elsewhere.

data GRPerturbationBoundShapeCoreStatus : Set where
  carrierOnlyFailClosed :
    GRPerturbationBoundShapeCoreStatus

record GRPerturbationBoundShapeCore : Setω where
  field
    carrier :
      Set

    status :
      GRPerturbationBoundShapeCoreStatus

    statusIsFailClosed :
      status ≡ carrierOnlyFailClosed

    christoffelPerturbBoundName :
      String

    christoffelPerturbBoundShape :
      String

    ricciBoundName :
      String

    ricciBoundShape :
      String

    constant22Le48Name :
      String

    constant22Le48Shape :
      String

    constant22Le48Witness :
      Bool

    constant22Le48WitnessIsTrue :
      constant22Le48Witness ≡ true

    constant2144Over27Le80Le640Name :
      String

    constant2144Over27Le80Le640Shape :
      String

    constant2144Over27Le80Le640Witness :
      Bool

    constant2144Over27Le80Le640WitnessIsTrue :
      constant2144Over27Le80Le640Witness ≡ true

    concreteChristoffelTensorFormulaLaw :
      Set

    concreteRicciTensorFormulaLaw :
      Set

    noLocalProofOrPromotionWithoutConcreteTensorFormulaLaws :
      Bool

    noLocalProofOrPromotionWithoutConcreteTensorFormulaLawsIsTrue :
      noLocalProofOrPromotionWithoutConcreteTensorFormulaLaws ≡ true

    boundary :
      List String

open GRPerturbationBoundShapeCore public

canonicalGRPerturbationBoundShapeCore :
  GRPerturbationBoundShapeCore
canonicalGRPerturbationBoundShapeCore =
  record
    { carrier =
        Bool
    ; status =
        carrierOnlyFailClosed
    ; statusIsFailClosed =
        refl
    ; christoffelPerturbBoundName =
        "christoffelPerturbBound"
    ; christoffelPerturbBoundShape =
        "carrier/receipt only: christoffelPerturbBound is named here as a downstream-bound shape and is not locally proved"
    ; ricciBoundName =
        "ricciBound"
    ; ricciBoundShape =
        "carrier/receipt only: ricciBound is named here as a downstream-bound shape and is not locally proved"
    ; constant22Le48Name =
        "22<=48"
    ; constant22Le48Shape =
        "string/Bool witness for the local arithmetic note 22<=48"
    ; constant22Le48Witness =
        true
    ; constant22Le48WitnessIsTrue =
        refl
    ; constant2144Over27Le80Le640Name =
        "2144/27<=80<=640"
    ; constant2144Over27Le80Le640Shape =
        "string/Bool witness for the local arithmetic note 2144/27<=80<=640"
    ; constant2144Over27Le80Le640Witness =
        true
    ; constant2144Over27Le80Le640WitnessIsTrue =
        refl
    ; concreteChristoffelTensorFormulaLaw =
        Bool
    ; concreteRicciTensorFormulaLaw =
        Bool
    ; noLocalProofOrPromotionWithoutConcreteTensorFormulaLaws =
        true
    ; noLocalProofOrPromotionWithoutConcreteTensorFormulaLawsIsTrue =
        refl
    ; boundary =
        "This module is carrier/receipt only"
        ∷ "christoffelPerturbBound is recorded by name and shape only"
        ∷ "ricciBound is recorded by name and shape only"
        ∷ "22<=48 is recorded as a string/Bool witness only"
        ∷ "2144/27<=80<=640 is recorded as a string/Bool witness only"
        ∷ "No local proof or promotion is introduced unless concrete tensor formula laws are supplied"
        ∷ "No import or edit of Everything.agda is performed here"
        ∷ []
    }
