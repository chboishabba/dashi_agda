module DASHI.Moonshine.Monster369ZetaSameObjectWeldValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.Monster369ZetaSameObjectWeldExact as P

paidRegression :
  P.Monster369ZetaWeldBoundary.fourierZetaMapsToMonsterZeta
    P.canonicalMonster369ZetaWeldBoundary
  ≡ true
  × P.Monster369ZetaWeldBoundary.inertiaZetaMapsToExactCyclotomicZeta
    P.canonicalMonster369ZetaWeldBoundary
  ≡ true
  × P.Monster369ZetaWeldBoundary.schrodingerModelUsesSameCyclotomicZeta
    P.canonicalMonster369ZetaWeldBoundary
  ≡ true
  × P.Monster369ZetaWeldBoundary.literalVOAZetaSectorUsesThatPhase
    P.canonicalMonster369ZetaWeldBoundary
  ≡ true
  × P.Monster369ZetaWeldBoundary.linearRestrictionReusesLiteralZetaSector
    P.canonicalMonster369ZetaWeldBoundary
  ≡ true
paidRegression = refl , refl , refl , refl , refl

frontierRegression :
  P.Monster369ZetaWeldBoundary.base369ZetaSheetIsLiteralCyclotomicScalar
    P.canonicalMonster369ZetaWeldBoundary
  ≡ false
  × P.Monster369ZetaWeldBoundary.actualHZetaWZetaSameObjectRecognitionPaid
    P.canonicalMonster369ZetaWeldBoundary
  ≡ false
  × P.Monster369ZetaWeldBoundary.actualMultiplicityIntertwinerPaid
    P.canonicalMonster369ZetaWeldBoundary
  ≡ false
frontierRegression = refl , refl , refl
