module DASHI.Core.CertifiedLatticeDescentTests where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero)

open import DASHI.Core.CertifiedLatticeDescent

------------------------------------------------------------------------
-- A finite smoke-test surface. The singleton fibre makes the leastness
-- proof explicit without postulates or external optimisation authority.

data ExampleSurface : Set where
  candidateSurface : ExampleSurface

zeroPressure : StructuralPressure
zeroPressure =
  structuralPressure zero zero zero zero zero zero

sourceState : DescentState ExampleSurface
sourceState = descentState candidateSurface zeroPressure

chosenState : DescentState ExampleSurface
chosenState = sourceState

singletonSearchFibre :
  DescentState ExampleSurface →
  Set
singletonSearchFibre state = state ≡ chosenState

identityAdmissible :
  AdmissibleRefinement sourceState chosenState
identityAdmissible =
  admissibleRefinement
    true refl
    true refl
    true refl
    true refl

identityRefinement :
  RefinementWitness sourceState chosenState
identityRefinement =
  refinementWitness
    identityAdmissible
    (≤-refl (totalPressure (pressure sourceState)))

singletonLeast :
  (competitor : DescentState ExampleSurface) →
  singletonSearchFibre competitor →
  RefinementWitness sourceState competitor →
  totalPressure (pressure chosenState)
  ≤
  totalPressure (pressure competitor)
singletonLeast .chosenState refl competitorWitness =
  ≤-refl (totalPressure (pressure chosenState))

exampleCertifiedArgmin :
  CertifiedArgmin sourceState singletonSearchFibre
exampleCertifiedArgmin =
  certifiedArgmin
    chosenState
    refl
    identityRefinement
    singletonLeast

exampleReceipt :
  CertifiedDescentReceipt sourceState singletonSearchFibre
exampleReceipt =
  mkNonPromotingDescentReceipt
    "singleton certified DASHI lattice descent"
    exampleCertifiedArgmin

exampleArgminIsChosen :
  argminState exampleCertifiedArgmin ≡ chosenState
exampleArgminIsChosen = refl

exampleOptimizerAuthorityFalse :
  numericOptimizerImplemented exampleReceipt ≡ false
exampleOptimizerAuthorityFalse = refl

exampleGlobalOptimalityFalse :
  globalOptimalityClaimed exampleReceipt ≡ false
exampleGlobalOptimalityFalse = refl

examplePromotionAuthorityFalse :
  promotionAuthority exampleReceipt ≡ false
examplePromotionAuthorityFalse = refl
