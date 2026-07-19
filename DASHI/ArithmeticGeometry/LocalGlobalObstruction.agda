module DASHI.ArithmeticGeometry.LocalGlobalObstruction where

open import Agda.Builtin.Bool     using (Bool; true; false)
open import Agda.Builtin.Nat      using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma    using (Σ; _,_)
open import Agda.Builtin.Unit     using (⊤; tt)
open import Relation.Nullary      using (¬_)

------------------------------------------------------------------------
-- Abstract local-global problem.
------------------------------------------------------------------------

record LocalGlobalProblem : Set₁ where
  field
    Place        : Set
    GlobalPoint  : Set
    LocalPoint   : Place → Set
    localise     : (v : Place) → GlobalPoint → LocalPoint v

open LocalGlobalProblem public

EverywhereLocal : (P : LocalGlobalProblem) → Set
EverywhereLocal P = (v : Place P) → LocalPoint P v

GlobalWitness : (P : LocalGlobalProblem) → Set
GlobalWitness P = GlobalPoint P

------------------------------------------------------------------------
-- A torsor class is represented abstractly.  Triviality is the exact bridge
-- from everywhere-local data to a global point; no bounded-search failure is
-- allowed to stand in for this witness.
------------------------------------------------------------------------

record CohomologyObstruction (P : LocalGlobalProblem) : Set₁ where
  field
    H1Class      : Set
    classOfLocal : EverywhereLocal P → H1Class
    trivial      : H1Class → Set

    trivial→global :
      (locals : EverywhereLocal P) →
      trivial (classOfLocal locals) →
      GlobalWitness P

    global→trivial :
      (Q : GlobalWitness P) →
      trivial (classOfLocal (λ v → localise P v Q))

open CohomologyObstruction public

------------------------------------------------------------------------
-- Selmer layer: finite local conditions containing both Mordell-Weil image
-- and possible Tate-Shafarevich classes.
------------------------------------------------------------------------

record SelmerLayer (P : LocalGlobalProblem)
                   (O : CohomologyObstruction P) : Set₁ where
  field
    SelmerClass : Set
    injectH1    : H1Class O → SelmerClass

    locallyAdmissible : SelmerClass → Set
    mwImage           : SelmerClass → Set
    shaCandidate      : SelmerClass → Set

    image-partition :
      ∀ s → locallyAdmissible s →
      mwImage s → ¬ shaCandidate s

open SelmerLayer public

------------------------------------------------------------------------
-- Cassels-Tate-style pairing interface.
-- A nonzero pairing is a certificate that a locally admissible class is not
-- being silently identified with a global Mordell-Weil witness.
------------------------------------------------------------------------

record PairingCertificate {Class : Set} : Set₁ where
  field
    Value    : Set
    zeroV    : Value
    pair     : Class → Class → Value
    nonzero  : Value → Set

    detects : ∀ x y → nonzero (pair x y) → ¬ (pair x y ≡ zeroV)

open PairingCertificate public

------------------------------------------------------------------------
-- DASHI obstruction/lift result.  Unknown is explicit: persistent search
-- failure is not promoted to a proof of global insolubility.
------------------------------------------------------------------------

data Decision : Set where
  global-found       : Decision
  certified-obstructed : Decision
  lift-required      : Decision

record LocalGlobalDecision (P : LocalGlobalProblem) : Set₁ where
  field
    decision : Decision
    globalWitness : decision ≡ global-found → GlobalWitness P

------------------------------------------------------------------------
-- Search-depth receipts are deliberately weaker than obstruction receipts.
------------------------------------------------------------------------

record BoundedSearchReceipt (P : LocalGlobalProblem) : Set₁ where
  field
    bound       : Nat
    pointFound  : Bool
    found→point : pointFound ≡ true → GlobalWitness P

noPointFoundIsNotObstruction :
  ∀ {P : LocalGlobalProblem} →
  BoundedSearchReceipt P → Set
noPointFoundIsNotObstruction _ = ⊤
