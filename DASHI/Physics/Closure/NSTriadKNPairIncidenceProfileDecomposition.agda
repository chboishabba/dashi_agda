module DASHI.Physics.Closure.NSTriadKNPairIncidenceProfileDecomposition where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)

------------------------------------------------------------------------
-- Theorem-facing surface for the Stage 3 profile decomposition.
--
-- This module does not claim the decomposition is proved. It exposes the
-- exact theorem shape needed to upgrade the receipt layer into a genuine
-- profile-wise analytic argument.

data PairIncidenceProfile : Set where
  forcedTailProfile : PairIncidenceProfile
  adversarialGeometryProfile : PairIncidenceProfile
  transitionProfile : PairIncidenceProfile
  residualProfile : PairIncidenceProfile

record NSTriadKNPairIncidenceProfileDecompositionModel
    {ℓS ℓE ℓV ℓR : Level} : Set (lsuc (ℓS ⊔ ℓE ⊔ ℓV ⊔ ℓR)) where
  field
    Shell : Set ℓS
    Entry : Set ℓE
    Value : Set ℓV

    _≈_ : Value -> Value -> Set ℓR
    _+_ : Value -> Value -> Value
    0# : Value

    totalKernel : Shell -> Entry -> Entry -> Value
    profileKernel : PairIncidenceProfile -> Shell -> Entry -> Entry -> Value

    profileClassifier : Shell -> Entry -> Entry -> PairIncidenceProfile

    pointwiseProfileDecomposition :
      (N : Shell) -> (i j : Entry) ->
      _≈_ (totalKernel N i j)
        ((profileKernel forcedTailProfile N i j + profileKernel adversarialGeometryProfile N i j) +
         (profileKernel transitionProfile N i j + profileKernel residualProfile N i j))

    forcedTailClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ forcedTailProfile ->
      _≈_ (profileKernel adversarialGeometryProfile N i j) 0#

    adversarialClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ adversarialGeometryProfile ->
      _≈_ (profileKernel forcedTailProfile N i j) 0#

    transitionClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ transitionProfile ->
      _≈_ (profileKernel residualProfile N i j) 0#

    residualClassifierSound :
      (N : Shell) -> (i j : Entry) ->
      profileClassifier N i j ≡ residualProfile ->
      _≈_ (profileKernel transitionProfile N i j) 0#

open NSTriadKNPairIncidenceProfileDecompositionModel public

forcedTailProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
forcedTailProfileKernel m =
  profileKernel m forcedTailProfile

adversarialProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
adversarialProfileKernel m =
  profileKernel m adversarialGeometryProfile

transitionProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
transitionProfileKernel m =
  profileKernel m transitionProfile

residualProfileKernel :
  ∀ {ℓS ℓE ℓV ℓR}
  (m : NSTriadKNPairIncidenceProfileDecompositionModel {ℓS} {ℓE} {ℓV} {ℓR}) ->
  Shell m -> Entry m -> Entry m -> Value m
residualProfileKernel m =
  profileKernel m residualProfile
