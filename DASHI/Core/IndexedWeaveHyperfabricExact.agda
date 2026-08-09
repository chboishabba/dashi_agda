module DASHI.Core.IndexedWeaveHyperfabricExact where

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- A weave is an indexed family, not an untyped bag of moves.
--
-- Index identifies the hyperfabric site/fibre.  State i is the carrier at
-- that site.  Path i j is a typed weave from site i to site j, and transport
-- is required to respect identities and composition.  Residuals remain
-- indexed at the target, so a path cannot silently erase which fibre owns a
-- defect.
------------------------------------------------------------------------

record IndexedWeave
  (Index : Set)
  (State : Index → Set) : Set₁ where

  infixr 40 _∙_

  field
    Path : Index → Index → Set

    idPath :
      (index : Index) → Path index index

    _∙_ :
      {source middle target : Index} →
      Path middle target →
      Path source middle →
      Path source target

    pathIdLeft :
      {source target : Index} →
      (path : Path source target) →
      idPath target ∙ path ≡ path

    pathIdRight :
      {source target : Index} →
      (path : Path source target) →
      path ∙ idPath source ≡ path

    pathAssoc :
      {i j k l : Index} →
      (r : Path k l) →
      (q : Path j k) →
      (p : Path i j) →
      (r ∙ q) ∙ p ≡ r ∙ (q ∙ p)

    transport :
      {source target : Index} →
      Path source target →
      State source →
      State target

    transportId :
      (index : Index) →
      (state : State index) →
      transport (idPath index) state ≡ state

    transportComp :
      {source middle target : Index} →
      (q : Path middle target) →
      (p : Path source middle) →
      (state : State source) →
      transport (q ∙ p) state
      ≡ transport q (transport p state)

    Residual : Index → Set

    zeroResidual :
      (index : Index) → Residual index

    residualAfter :
      {source target : Index} →
      Path source target →
      State source →
      Residual target

    residualId :
      (index : Index) →
      (state : State index) →
      residualAfter (idPath index) state ≡ zeroResidual index

open IndexedWeave public

IndexedCarrier :
  {Index : Set} →
  (State : Index → Set) →
  Set
IndexedCarrier {Index} State = Σ Index State

IndexedPathCarrier :
  {Index : Set} →
  {State : Index → Set} →
  IndexedWeave Index State →
  Set
IndexedPathCarrier {Index} weave =
  Σ Index
    (λ source →
      Σ Index
        (λ target → Path weave source target))

sourceOf :
  {Index : Set} →
  {State : Index → Set} →
  (weave : IndexedWeave Index State) →
  IndexedPathCarrier weave →
  Index
sourceOf weave indexedPath = fst indexedPath

targetOf :
  {Index : Set} →
  {State : Index → Set} →
  (weave : IndexedWeave Index State) →
  IndexedPathCarrier weave →
  Index
targetOf weave indexedPath = fst (snd indexedPath)

pathOf :
  {Index : Set} →
  {State : Index → Set} →
  (weave : IndexedWeave Index State) →
  (indexedPath : IndexedPathCarrier weave) →
  Path weave (sourceOf weave indexedPath) (targetOf weave indexedPath)
pathOf weave indexedPath = snd (snd indexedPath)

transportIndexed :
  {Index : Set} →
  {State : Index → Set} →
  (weave : IndexedWeave Index State) →
  (indexedPath : IndexedPathCarrier weave) →
  State (sourceOf weave indexedPath) →
  State (targetOf weave indexedPath)
transportIndexed weave indexedPath =
  transport weave (pathOf weave indexedPath)

------------------------------------------------------------------------
-- A law-bearing upgrade surface for older Hyperfibre-style records.  The
-- legacy carrier can be embedded only after identity, composition and
-- transport laws are supplied; merely sharing field names is insufficient.
------------------------------------------------------------------------

record LawfulHyperfibreUpgrade
  (Index : Set)
  (State : Index → Set) : Set₁ where
  constructor lawfulHyperfibreUpgrade
  field
    indexedWeave : IndexedWeave Index State
    reading : Set

open LawfulHyperfibreUpgrade public
