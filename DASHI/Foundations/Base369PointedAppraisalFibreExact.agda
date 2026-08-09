module DASHI.Foundations.Base369PointedAppraisalFibreExact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- The exact arithmetic 729 = 8 * 90 + 9 is promoted to a typed pointed
-- address decomposition.  Eight noncentral interaction positions receive ten
-- fine sectors, each carrying a nine-state secondary sheet.  The distinguished
-- central interaction receives one shared nine-state sheet.  This is an
-- address-carrier theorem, not a claim that every appraisal semantics is
-- canonically forced by the arithmetic alone.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Fin.Base using (Fin)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_)

Noncentral8 : Set
Noncentral8 = Fin 8

Fine10 : Set
Fine10 = Fin 10

SecondarySheet9 : Set
SecondarySheet9 = Fin 9

record NoncentralFineAddress : Set where
  constructor noncentralFineAddress
  field
    noncentralPosition : Noncentral8
    fineSector : Fine10
    secondaryPosition : SecondarySheet9

open NoncentralFineAddress public

record CentralSharedAddress : Set where
  constructor centralSharedAddress
  field
    centralSecondaryPosition : SecondarySheet9

open CentralSharedAddress public

PointedAppraisal729 : Set
PointedAppraisal729 = NoncentralFineAddress ⊎ CentralSharedAddress

noncentralAddressCount : Nat
noncentralAddressCount = 8 * 10 * 9

centralAddressCount : Nat
centralAddressCount = 9

pointedAppraisalAddressCount : Nat
pointedAppraisalAddressCount = noncentralAddressCount + centralAddressCount

noncentralAddressCountIs720 : noncentralAddressCount ≡ 720
noncentralAddressCountIs720 = refl

pointedAppraisalAddressCountIs729 : pointedAppraisalAddressCount ≡ 729
pointedAppraisalAddressCountIs729 = refl

alternativeFactorisation : Nat
alternativeFactorisation = 8 * 90 + 9

alternativeFactorisationIs729 : alternativeFactorisation ≡ 729
alternativeFactorisationIs729 = refl

fineRelationalSurface90 : Nat
fineRelationalSurface90 = 10 * 9

fineRelationalSurface90Exact : fineRelationalSurface90 ≡ 90
fineRelationalSurface90Exact = refl

------------------------------------------------------------------------
-- The centre is shared rather than copied through all ten fine sectors.
------------------------------------------------------------------------

data InteractionPositionKind : Set where
  noncentralPositionKind
  centralPositionKind : InteractionPositionKind

positionKind : PointedAppraisal729 → InteractionPositionKind
positionKind (inj₁ address) = noncentralPositionKind
positionKind (inj₂ address) = centralPositionKind

fineSectorAvailable : PointedAppraisal729 → Set
fineSectorAvailable (inj₁ address) = Fine10
fineSectorAvailable (inj₂ address) = Fin 1

-- A total observer forgets fine-sector multiplicity but preserves the
-- secondary nine-sheet position.
secondaryObservation : PointedAppraisal729 → SecondarySheet9
secondaryObservation (inj₁ address) = secondaryPosition address
secondaryObservation (inj₂ address) = centralSecondaryPosition address

------------------------------------------------------------------------
-- Relation to the certified 729 x 90 carrier is kept at the address level.
------------------------------------------------------------------------

record AppraisalMultiplicityAddress : Set where
  constructor appraisalMultiplicityAddress
  field
    appraisalAddress : PointedAppraisal729
    multiplicityAddress : Fin 90

open AppraisalMultiplicityAddress public

appraisalMultiplicityCount : Nat
appraisalMultiplicityCount = 729 * 90

appraisalMultiplicityCountIs65610 : appraisalMultiplicityCount ≡ 65610
appraisalMultiplicityCountIs65610 = refl
