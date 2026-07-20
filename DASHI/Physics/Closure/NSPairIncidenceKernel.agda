module DASHI.Physics.Closure.NSPairIncidenceKernel where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Analysis.FiniteWeightedKernelSums

------------------------------------------------------------------------
-- Exact finite pair-incidence construction for rectangular shell transfer.
--
-- A Pair contributes to one source/target mode entry through pairContribution.
-- The concrete Biot--Savart lane must identify its transfer kernel pointwise
-- with the finite fold below.  Coarse shell/angle aggregates cannot inhabit
-- that identification without an explicit representation theorem.
------------------------------------------------------------------------

record PairIncidenceData
    {p r c s : Level}
    (Pair : Set p)
    (Row : Set r)
    (Col : Set c)
    (Scalar : Set s) : Set (lsuc (p ⊔ r ⊔ c ⊔ s)) where
  field
    pairs : List Pair
    rows : List Row
    columns : List Col

    zero : Scalar
    add : Scalar → Scalar → Scalar
    multiply : Scalar → Scalar → Scalar
    _≤_ : Scalar → Scalar → Set s

    pairContribution : Pair → Row → Col → Scalar
    rowWeight : Row → Scalar
    colWeight : Col → Scalar

open PairIncidenceData public

pairKernelEntry :
  ∀ {p r c s}
    {Pair : Set p} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  PairIncidenceData Pair Row Col Scalar →
  Row → Col → Scalar
pairKernelEntry P row col =
  fold (add P) (zero P)
    (map (λ pair → pairContribution P pair row col) (pairs P))

asFiniteWeightedKernel :
  ∀ {p r c s}
    {Pair : Set p} {Row : Set r} {Col : Set c} {Scalar : Set s} →
  PairIncidenceData Pair Row Col Scalar →
  FiniteWeightedKernel Row Col Scalar
asFiniteWeightedKernel P = record
  { rows = rows P
  ; columns = columns P
  ; zero = zero P
  ; add = add P
  ; multiply = multiply P
  ; _≤_ = _≤_ P
  ; kernel = pairKernelEntry P
  ; rowWeight = rowWeight P
  ; colWeight = colWeight P
  }

record ConcreteBiotSavartKernelMatch
    {p r c s : Level}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (P : PairIncidenceData Pair Row Col Scalar)
    (concreteKernel : Row → Col → Scalar) :
    Set (r ⊔ c ⊔ s) where
  field
    pointwiseKernelMatch :
      ∀ row col → concreteKernel row col ≡ pairKernelEntry P row col

open ConcreteBiotSavartKernelMatch public

record PairIncidenceWeightedCertificate
    {p r c s : Level}
    {Pair : Set p}
    {Row : Set r}
    {Col : Set c}
    {Scalar : Set s}
    (P : PairIncidenceData Pair Row Col Scalar) :
    Set (lsuc (p ⊔ r ⊔ c ⊔ s)) where
  field
    finiteCertificate :
      FiniteWeightedSchurCertificate (asFiniteWeightedKernel P)

open PairIncidenceWeightedCertificate public
