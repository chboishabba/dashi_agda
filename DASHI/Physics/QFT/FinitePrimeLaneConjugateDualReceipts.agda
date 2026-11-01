module DASHI.Physics.QFT.FinitePrimeLaneConjugateDualReceipts where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Finite p2/p3/p5 conjugate/dual receipts.
--
-- This module is intentionally finite-row only.  It records conjugate/dual
-- sockets for p2, p3, and p5 prime-lane rows.  It does not construct the full
-- DHR tensor category, arbitrary
-- localized endomorphism duals, DR reconstruction, Frobenius reciprocity, or
-- a compact gauge group.

data FinitePrimeLaneSMRow : Set where
  p2FinitePrimeLaneRow :
    FinitePrimeLaneSMRow

  p3FinitePrimeLaneRow :
    FinitePrimeLaneSMRow

  p5FinitePrimeLaneRow :
    FinitePrimeLaneSMRow

data FinitePrimeLaneDHRArrow :
  FinitePrimeLaneSMRow →
  FinitePrimeLaneSMRow →
  Set where
  finitePrimeLaneId :
    (row : FinitePrimeLaneSMRow) →
    FinitePrimeLaneDHRArrow row row

  finitePrimeLaneCompose :
    {x y z : FinitePrimeLaneSMRow} →
    FinitePrimeLaneDHRArrow y z →
    FinitePrimeLaneDHRArrow x y →
    FinitePrimeLaneDHRArrow x z

finitePrimeLaneDHRCompose :
  {x y z : FinitePrimeLaneSMRow} →
  FinitePrimeLaneDHRArrow y z →
  FinitePrimeLaneDHRArrow x y →
  FinitePrimeLaneDHRArrow x z
finitePrimeLaneDHRCompose (finitePrimeLaneId _) f =
  f
finitePrimeLaneDHRCompose g (finitePrimeLaneId _) =
  g
finitePrimeLaneDHRCompose g f =
  finitePrimeLaneCompose g f

data FinitePrimeLaneConjugateKind : Set where
  p2SelfPhaseConjugation :
    FinitePrimeLaneConjugateKind

  p3ContragredientTarget :
    FinitePrimeLaneConjugateKind

  p5ContragredientTarget :
    FinitePrimeLaneConjugateKind

finiteConjugateSource :
  FinitePrimeLaneConjugateKind →
  FinitePrimeLaneSMRow
finiteConjugateSource p2SelfPhaseConjugation =
  p2FinitePrimeLaneRow
finiteConjugateSource p3ContragredientTarget =
  p3FinitePrimeLaneRow
finiteConjugateSource p5ContragredientTarget =
  p5FinitePrimeLaneRow

finiteConjugateTarget :
  FinitePrimeLaneConjugateKind →
  FinitePrimeLaneSMRow
finiteConjugateTarget p2SelfPhaseConjugation =
  p2FinitePrimeLaneRow
finiteConjugateTarget p3ContragredientTarget =
  p3FinitePrimeLaneRow
finiteConjugateTarget p5ContragredientTarget =
  p5FinitePrimeLaneRow

finiteConjugateTargetIsFiniteRow :
  (kind : FinitePrimeLaneConjugateKind) →
  finiteConjugateTarget kind ≡ finiteConjugateSource kind
finiteConjugateTargetIsFiniteRow p2SelfPhaseConjugation =
  refl
finiteConjugateTargetIsFiniteRow p3ContragredientTarget =
  refl
finiteConjugateTargetIsFiniteRow p5ContragredientTarget =
  refl

record FinitePrimeLaneDualSocket
  (kind : FinitePrimeLaneConjugateKind) :
  Set where
  field
    sourceRow :
      FinitePrimeLaneSMRow

    sourceRowIsCanonical :
      sourceRow ≡ finiteConjugateSource kind

    conjugateTargetRow :
      FinitePrimeLaneSMRow

    conjugateTargetRowIsCanonical :
      conjugateTargetRow ≡ finiteConjugateTarget kind

    conjugateKind :
      FinitePrimeLaneConjugateKind

    conjugateKindIsCanonical :
      conjugateKind ≡ kind

    unitSocket :
      FinitePrimeLaneDHRArrow sourceRow sourceRow

    unitSocketIsFiniteIdentity :
      unitSocket ≡ finitePrimeLaneId sourceRow

    counitSocket :
      FinitePrimeLaneDHRArrow sourceRow sourceRow

    counitSocketIsFiniteIdentity :
      counitSocket ≡ finitePrimeLaneId sourceRow

    leftZigzag :
      finitePrimeLaneDHRCompose counitSocket unitSocket
      ≡
      finitePrimeLaneId sourceRow

    rightZigzag :
      finitePrimeLaneDHRCompose unitSocket counitSocket
      ≡
      finitePrimeLaneId sourceRow

    zigzagsAreDefinitionalOverFiniteIdentities :
      Bool

    zigzagsAreDefinitionalOverFiniteIdentitiesIsTrue :
      zigzagsAreDefinitionalOverFiniteIdentities ≡ true

    fullDHRDualCategoryPromoted :
      Bool

    fullDHRDualCategoryPromotedIsFalse :
      fullDHRDualCategoryPromoted ≡ false

    socketBoundary :
      List String

open FinitePrimeLaneDualSocket public

p2FiniteSelfPhaseDualSocket :
  FinitePrimeLaneDualSocket p2SelfPhaseConjugation
p2FiniteSelfPhaseDualSocket =
  record
    { sourceRow =
        p2FinitePrimeLaneRow
    ; sourceRowIsCanonical =
        refl
    ; conjugateTargetRow =
        p2FinitePrimeLaneRow
    ; conjugateTargetRowIsCanonical =
        refl
    ; conjugateKind =
        p2SelfPhaseConjugation
    ; conjugateKindIsCanonical =
        refl
    ; unitSocket =
        finitePrimeLaneId p2FinitePrimeLaneRow
    ; unitSocketIsFiniteIdentity =
        refl
    ; counitSocket =
        finitePrimeLaneId p2FinitePrimeLaneRow
    ; counitSocketIsFiniteIdentity =
        refl
    ; leftZigzag =
        refl
    ; rightZigzag =
        refl
    ; zigzagsAreDefinitionalOverFiniteIdentities =
        true
    ; zigzagsAreDefinitionalOverFiniteIdentitiesIsTrue =
        refl
    ; fullDHRDualCategoryPromoted =
        false
    ; fullDHRDualCategoryPromotedIsFalse =
        refl
    ; socketBoundary =
        "p2 records self/phase conjugation on the finite U1Y row"
        ∷ "unit and counit sockets are finite identity arrows"
        ∷ "zigzags close definitionally only because both sockets are identities"
        ∷ "no full DHR dual category is promoted"
        ∷ []
    }

p3FiniteContragredientDualSocket :
  FinitePrimeLaneDualSocket p3ContragredientTarget
p3FiniteContragredientDualSocket =
  record
    { sourceRow =
        p3FinitePrimeLaneRow
    ; sourceRowIsCanonical =
        refl
    ; conjugateTargetRow =
        p3FinitePrimeLaneRow
    ; conjugateTargetRowIsCanonical =
        refl
    ; conjugateKind =
        p3ContragredientTarget
    ; conjugateKindIsCanonical =
        refl
    ; unitSocket =
        finitePrimeLaneId p3FinitePrimeLaneRow
    ; unitSocketIsFiniteIdentity =
        refl
    ; counitSocket =
        finitePrimeLaneId p3FinitePrimeLaneRow
    ; counitSocketIsFiniteIdentity =
        refl
    ; leftZigzag =
        refl
    ; rightZigzag =
        refl
    ; zigzagsAreDefinitionalOverFiniteIdentities =
        true
    ; zigzagsAreDefinitionalOverFiniteIdentitiesIsTrue =
        refl
    ; fullDHRDualCategoryPromoted =
        false
    ; fullDHRDualCategoryPromotedIsFalse =
        refl
    ; socketBoundary =
        "p3 records a contragredient target socket on the finite SU2L row"
        ∷ "unit and counit sockets are finite identity arrows"
        ∷ "zigzags close definitionally only because both sockets are identities"
        ∷ "no full DHR dual category is promoted"
        ∷ []
    }

p5FiniteContragredientDualSocket :
  FinitePrimeLaneDualSocket p5ContragredientTarget
p5FiniteContragredientDualSocket =
  record
    { sourceRow =
        p5FinitePrimeLaneRow
    ; sourceRowIsCanonical =
        refl
    ; conjugateTargetRow =
        p5FinitePrimeLaneRow
    ; conjugateTargetRowIsCanonical =
        refl
    ; conjugateKind =
        p5ContragredientTarget
    ; conjugateKindIsCanonical =
        refl
    ; unitSocket =
        finitePrimeLaneId p5FinitePrimeLaneRow
    ; unitSocketIsFiniteIdentity =
        refl
    ; counitSocket =
        finitePrimeLaneId p5FinitePrimeLaneRow
    ; counitSocketIsFiniteIdentity =
        refl
    ; leftZigzag =
        refl
    ; rightZigzag =
        refl
    ; zigzagsAreDefinitionalOverFiniteIdentities =
        true
    ; zigzagsAreDefinitionalOverFiniteIdentitiesIsTrue =
        refl
    ; fullDHRDualCategoryPromoted =
        false
    ; fullDHRDualCategoryPromotedIsFalse =
        refl
    ; socketBoundary =
        "p5 records a contragredient target socket on the finite SU3c row"
        ∷ "unit and counit sockets are finite identity arrows"
        ∷ "zigzags close definitionally only because both sockets are identities"
        ∷ "no full DHR dual category is promoted"
        ∷ []
    }

canonicalFinitePrimeLaneDualSockets :
  (kind : FinitePrimeLaneConjugateKind) →
  FinitePrimeLaneDualSocket kind
canonicalFinitePrimeLaneDualSockets p2SelfPhaseConjugation =
  p2FiniteSelfPhaseDualSocket
canonicalFinitePrimeLaneDualSockets p3ContragredientTarget =
  p3FiniteContragredientDualSocket
canonicalFinitePrimeLaneDualSockets p5ContragredientTarget =
  p5FiniteContragredientDualSocket

record FinitePrimeLaneConjugateDualReceipt : Set where
  field
    p2Socket :
      FinitePrimeLaneDualSocket p2SelfPhaseConjugation

    p2SocketIsCanonical :
      p2Socket ≡ p2FiniteSelfPhaseDualSocket

    p3Socket :
      FinitePrimeLaneDualSocket p3ContragredientTarget

    p3SocketIsCanonical :
      p3Socket ≡ p3FiniteContragredientDualSocket

    p5Socket :
      FinitePrimeLaneDualSocket p5ContragredientTarget

    p5SocketIsCanonical :
      p5Socket ≡ p5FiniteContragredientDualSocket

    finiteRowsOnly :
      Bool

    finiteRowsOnlyIsTrue :
      finiteRowsOnly ≡ true

    fullDHRDualCategoryPromoted :
      Bool

    fullDHRDualCategoryPromotedIsFalse :
      fullDHRDualCategoryPromoted ≡ false

    receiptBoundary :
      List String

open FinitePrimeLaneConjugateDualReceipt public

canonicalFinitePrimeLaneConjugateDualReceipt :
  FinitePrimeLaneConjugateDualReceipt
canonicalFinitePrimeLaneConjugateDualReceipt =
  record
    { p2Socket =
        p2FiniteSelfPhaseDualSocket
    ; p2SocketIsCanonical =
        refl
    ; p3Socket =
        p3FiniteContragredientDualSocket
    ; p3SocketIsCanonical =
        refl
    ; p5Socket =
        p5FiniteContragredientDualSocket
    ; p5SocketIsCanonical =
        refl
    ; finiteRowsOnly =
        true
    ; finiteRowsOnlyIsTrue =
        refl
    ; fullDHRDualCategoryPromoted =
        false
    ; fullDHRDualCategoryPromotedIsFalse =
        refl
    ; receiptBoundary =
        "Finite conjugate/dual receipts are available for p2, p3, and p5 only"
        ∷ "p2 is self/phase conjugation; p3 and p5 expose contragredient target sockets"
        ∷ "unit/counit sockets and zigzags are finite identity receipts"
        ∷ "this is not a full DHR dual category construction"
        ∷ []
    }
