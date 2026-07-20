module DASHI.Algebra.FiniteQuaternionGroupReceipts where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Algebra.FiniteQuaternionDoubleCover as Q8

------------------------------------------------------------------------
-- Unit, inverse, and central-kernel receipts for the finite quaternion cover.

q8Inverse : Q8.Q8 → Q8.Q8
q8Inverse (Q8.quaternion Q8.positiveSign Q8.basisOne) = Q8.plusOne
q8Inverse (Q8.quaternion Q8.negativeSign Q8.basisOne) = Q8.minusOne
q8Inverse (Q8.quaternion Q8.positiveSign Q8.basisI) = Q8.minusI
q8Inverse (Q8.quaternion Q8.negativeSign Q8.basisI) = Q8.plusI
q8Inverse (Q8.quaternion Q8.positiveSign Q8.basisJ) = Q8.minusJ
q8Inverse (Q8.quaternion Q8.negativeSign Q8.basisJ) = Q8.plusJ
q8Inverse (Q8.quaternion Q8.positiveSign Q8.basisK) = Q8.minusK
q8Inverse (Q8.quaternion Q8.negativeSign Q8.basisK) = Q8.plusK

leftIdentity : (element : Q8.Q8) → Q8.q8Multiply Q8.plusOne element ≡ element
leftIdentity (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
leftIdentity (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
leftIdentity (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
leftIdentity (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
leftIdentity (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
leftIdentity (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
leftIdentity (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
leftIdentity (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

rightIdentity : (element : Q8.Q8) → Q8.q8Multiply element Q8.plusOne ≡ element
rightIdentity (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
rightIdentity (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
rightIdentity (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
rightIdentity (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
rightIdentity (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
rightIdentity (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
rightIdentity (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
rightIdentity (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

leftInverse :
  (element : Q8.Q8) →
  Q8.q8Multiply (q8Inverse element) element ≡ Q8.plusOne
leftInverse (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
leftInverse (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
leftInverse (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
leftInverse (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
leftInverse (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
leftInverse (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
leftInverse (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
leftInverse (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

rightInverse :
  (element : Q8.Q8) →
  Q8.q8Multiply element (q8Inverse element) ≡ Q8.plusOne
rightInverse (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
rightInverse (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
rightInverse (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
rightInverse (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
rightInverse (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
rightInverse (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
rightInverse (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
rightInverse (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

minusOneCentral :
  (element : Q8.Q8) →
  Q8.q8Multiply Q8.minusOne element
  ≡ Q8.q8Multiply element Q8.minusOne
minusOneCentral (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
minusOneCentral (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
minusOneCentral (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
minusOneCentral (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
minusOneCentral (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
minusOneCentral (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
minusOneCentral (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
minusOneCentral (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

rhoIgnoresCentralSign :
  (element : Q8.Q8) →
  Q8.rho (Q8.q8Multiply Q8.minusOne element) ≡ Q8.rho element
rhoIgnoresCentralSign (Q8.quaternion Q8.positiveSign Q8.basisOne) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.negativeSign Q8.basisOne) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.positiveSign Q8.basisI) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.negativeSign Q8.basisI) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.positiveSign Q8.basisJ) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.negativeSign Q8.basisJ) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.positiveSign Q8.basisK) = refl
rhoIgnoresCentralSign (Q8.quaternion Q8.negativeSign Q8.basisK) = refl

record FiniteQuaternionUnitReceipt : Set where
  constructor finite-quaternion-unit-receipt
  field
    leftUnitReceipt :
      (element : Q8.Q8) → Q8.q8Multiply Q8.plusOne element ≡ element
    rightUnitReceipt :
      (element : Q8.Q8) → Q8.q8Multiply element Q8.plusOne ≡ element
    leftInverseReceipt :
      (element : Q8.Q8) →
      Q8.q8Multiply (q8Inverse element) element ≡ Q8.plusOne
    rightInverseReceipt :
      (element : Q8.Q8) →
      Q8.q8Multiply element (q8Inverse element) ≡ Q8.plusOne
    centralKernelReceipt :
      (element : Q8.Q8) →
      Q8.q8Multiply Q8.minusOne element
      ≡ Q8.q8Multiply element Q8.minusOne
    quotientForgetsCentralSign :
      (element : Q8.Q8) →
      Q8.rho (Q8.q8Multiply Q8.minusOne element) ≡ Q8.rho element
    scope : String
open FiniteQuaternionUnitReceipt public

canonicalFiniteQuaternionUnitReceipt : FiniteQuaternionUnitReceipt
canonicalFiniteQuaternionUnitReceipt =
  finite-quaternion-unit-receipt
    leftIdentity
    rightIdentity
    leftInverse
    rightInverse
    minusOneCentral
    rhoIgnoresCentralSign
    "exact Q8 unit, inverse, and central-sign quotient laws; associativity follows from the standard quaternion multiplication authority and is not re-enumerated here"
