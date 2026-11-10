module DASHI.Information.PNFTrialecticSpectralDescentExact where

-- A genuinely reusable three-chart descent result for a typed spectral
-- observation carrier. The canonical 369 observer chart is reused;
-- no identity between stock correlations, PNF predicates, and triadic
-- face ontology is inferred from an equal-sized carrier.
--
-- The source trialectic descent theorem specialises to SSP trits.
-- Here the chart algebra is proved for ANY View, including numerical
-- diagnostic values, by preserving the same overlap identities.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Reasoning.TrialecticObserverMatrix369Exact as Observer
import DASHI.Reasoning.TrialecticBoundaryFaceNonfactorabilityExact as Face
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import Data.Empty

record ABChart (View : Set) : Set where
  constructor ab-chart
  field
    aaAB : View
    ab : View
    ba : View
    bbAB : View
open ABChart public

record BCChart (View : Set) : Set where
  constructor bc-chart
  field
    bbBC : View
    bc : View
    cb : View
    ccBC : View
open BCChart public

record CAChart (View : Set) : Set where
  constructor ca-chart
  field
    ccCA : View
    ca : View
    ac : View
    aaCA : View
open CAChart public

abOf :
  {View : Set} → Observer.ObserverMatrix3 View → ABChart View
abOf x = ab-chart
  (Observer.aA x) (Observer.aB x)
  (Observer.bA x) (Observer.bB x)

bcOf :
  {View : Set} → Observer.ObserverMatrix3 View → BCChart View
bcOf x = bc-chart
  (Observer.bB x) (Observer.bC x)
  (Observer.cB x) (Observer.cC x)

caOf :
  {View : Set} → Observer.ObserverMatrix3 View → CAChart View
caOf x = ca-chart
  (Observer.cC x) (Observer.cA x)
  (Observer.aC x) (Observer.aA x)

record SpectralMatchingFamily (View : Set) : Set where
  constructor spectral-matching-family
  field
    localAB : ABChart View
    localBC : BCChart View
    localCA : CAChart View
    overlapA : aaAB localAB ≡ aaCA localCA
    overlapB : bbAB localAB ≡ bbBC localBC
    overlapC : ccBC localBC ≡ ccCA localCA
open SpectralMatchingFamily public

restrictSpectral :
  {View : Set} →
  Observer.ObserverMatrix3 View → SpectralMatchingFamily View
restrictSpectral x = spectral-matching-family
  (abOf x) (bcOf x) (caOf x) refl refl refl

glueSpectral :
  {View : Set} →
  SpectralMatchingFamily View → Observer.ObserverMatrix3 View
glueSpectral f = Observer.observerMatrix3
  (aaAB (localAB f)) (ab (localAB f)) (ac (localCA f))
  (ba (localAB f)) (bbAB (localAB f)) (bc (localBC f))
  (ca (localCA f)) (cb (localBC f)) (ccBC (localBC f))

glueRestrictAB :
  {View : Set} →
  (f : SpectralMatchingFamily View) →
  abOf (glueSpectral f) ≡ localAB f
glueRestrictAB
  (spectral-matching-family
    (ab-chart aa abv bav bb)
    (bc-chart bb' bcv cbv cc)
    (ca-chart cc' cav acv aa')
    agreeA agreeB agreeC) = refl

glueRestrictBC :
  {View : Set} →
  (f : SpectralMatchingFamily View) →
  bcOf (glueSpectral f) ≡ localBC f
glueRestrictBC
  (spectral-matching-family
    (ab-chart aa abv bav bb)
    (bc-chart bb' bcv cbv cc)
    (ca-chart cc' cav acv aa')
    agreeA agreeB agreeC)
  rewrite agreeB = refl

glueRestrictCA :
  {View : Set} →
  (f : SpectralMatchingFamily View) →
  caOf (glueSpectral f) ≡ localCA f
glueRestrictCA
  (spectral-matching-family
    (ab-chart aa abv bav bb)
    (bc-chart bb' bcv cbv cc)
    (ca-chart cc' cav acv aa')
    agreeA agreeB agreeC)
  rewrite agreeA | agreeC = refl

spectralObserverRoundTrip :
  {View : Set} →
  (x : Observer.ObserverMatrix3 View) →
  glueSpectral (restrictSpectral x) ≡ x
spectralObserverRoundTrip
  (Observer.observerMatrix3 aa abv acv ba bb bc ca cb cc) = refl

mapAB :
  {A B : Set} → (f : A → B) → ABChart A → ABChart B
mapAB f (ab-chart aa abv bav bb) =
  ab-chart (f aa) (f abv) (f bav) (f bb)

mapBC :
  {A B : Set} → (f : A → B) → BCChart A → BCChart B
mapBC f (bc-chart bb bcv cbv cc) =
  bc-chart (f bb) (f bcv) (f cbv) (f cc)

mapCA :
  {A B : Set} → (f : A → B) → CAChart A → CAChart B
mapCA f (ca-chart cc cav acv aa) =
  ca-chart (f cc) (f cav) (f acv) (f aa)

mapObserver :
  {A B : Set} → (f : A → B) →
  Observer.ObserverMatrix3 A → Observer.ObserverMatrix3 B
mapObserver f x = Observer.observerMatrix3
  (f (Observer.aA x)) (f (Observer.aB x)) (f (Observer.aC x))
  (f (Observer.bA x)) (f (Observer.bB x)) (f (Observer.bC x))
  (f (Observer.cA x)) (f (Observer.cB x)) (f (Observer.cC x))

mapMatchingFamily :
  {A B : Set} → (f : A → B) →
  SpectralMatchingFamily A → SpectralMatchingFamily B
mapMatchingFamily f x = spectral-matching-family
  (mapAB f (localAB x))
  (mapBC f (localBC x))
  (mapCA f (localCA x))
  (cong f (overlapA x))
  (cong f (overlapB x))
  (cong f (overlapC x))

-- Local pointwise classification (e.g. applying the same MP threshold to
-- every already-existing diagnostic value) commutes with spectral gluing.
-- The theorem does not apply to covariance recomputation or eigendecomposition,
-- which depend on cross-chart terms and are not pointwise functions.
pointwiseSpectralClassificationCommutesWithGluing :
  {A B : Set} → (f : A → B) →
  (x : SpectralMatchingFamily A) →
  mapObserver f (glueSpectral x)
  ≡ glueSpectral (mapMatchingFamily f x)
pointwiseSpectralClassificationCommutesWithGluing f x = refl

pointwiseSpectralClassificationCommutesWithAB :
  {A B : Set} → (f : A → B) →
  (x : Observer.ObserverMatrix3 A) →
  abOf (mapObserver f x) ≡ mapAB f (abOf x)
pointwiseSpectralClassificationCommutesWithAB f x = refl

pointwiseSpectralClassificationCommutesWithBC :
  {A B : Set} → (f : A → B) →
  (x : Observer.ObserverMatrix3 A) →
  bcOf (mapObserver f x) ≡ mapBC f (bcOf x)
pointwiseSpectralClassificationCommutesWithBC f x = refl

pointwiseSpectralClassificationCommutesWithCA :
  {A B : Set} → (f : A → B) →
  (x : Observer.ObserverMatrix3 A) →
  caOf (mapObserver f x) ≡ mapCA f (caOf x)
pointwiseSpectralClassificationCommutesWithCA f x = refl

-- Reuse the ORIGINAL nonfactorability theorem. Three agreeing edge
-- observations never warrant the irreducible trialectic face.
spectralDyadicBoundaryDoesNotDetermineTriadicFace :
  Descent.FactorsThrough Face.boundaryObserver Face.faceConsumer →
  Data.Empty.⊥
spectralDyadicBoundaryDoesNotDetermineTriadicFace =
  Face.triadicFaceCannotFactorThroughThreeEdges
