module DASHI.Geometry.ProObjectSemantics where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Nat.Base using (ℕ; zero; suc)

import DASHI.Geometry.DCHoTTBridgeObligationIndex as B0

------------------------------------------------------------------------
-- B0.1 DASHI-side pro-object semantics.
--
-- This module is the first proof-grade step under the DCHoTT bridge index.
-- It constructs the inverse-limit point surface as compatible families and
-- proves the depthwise agreement laws that underlie the ultrametric/formal
-- disk scaffold.  It deliberately does not prove the analytic smooth
-- structure, condensed embedding, DCHoTT formal disk equivalence, B0.2
-- holonomy limit, B0.3 G-structure binding, or Levi-Civita promotion.

sym :
  {A : Set} →
  {x y : A} →
  x ≡ y →
  y ≡ x
sym refl =
  refl

trans :
  {A : Set} →
  {x y z : A} →
  x ≡ y →
  y ≡ z →
  x ≡ z
trans refl refl =
  refl

cong :
  {A B : Set} →
  {x y : A} →
  (f : A → B) →
  x ≡ y →
  f x ≡ f y
cong _ refl =
  refl

id :
  {A : Set₁} →
  A →
  A
id x =
  x

record ConstructedProObjectLimitSurface
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    -- Universe-correct constructed limit: the current ProObjectPoint record
    -- lives in Set1 because P.depthCarrier ranges over Set.
    ConstructedLimit :
      Set₁

    limitProjection :
      (d : ℕ) →
      ConstructedLimit →
      B0.ProObjectCarrier.depthCarrier P d

    limitProjectionCompatible :
      (d : ℕ) →
      (x : ConstructedLimit) →
      B0.ProObjectCarrier.refinementMap P d
        (limitProjection (suc d) x)
      ≡
      limitProjection d x

    toProObjectPoint :
      ConstructedLimit →
      B0.ProObjectPoint P

    fromProObjectPoint :
      B0.ProObjectPoint P →
      ConstructedLimit

    toFromRoundtrip :
      (x : B0.ProObjectPoint P) →
      toProObjectPoint (fromProObjectPoint x)
      ≡
      x

    fromToRoundtrip :
      (x : ConstructedLimit) →
      fromProObjectPoint (toProObjectPoint x)
      ≡
      x

open ConstructedProObjectLimitSurface public

canonicalConstructedProObjectLimitSurface :
  (P : B0.ProObjectCarrier) →
  ConstructedProObjectLimitSurface P
canonicalConstructedProObjectLimitSurface P =
  record
    { ConstructedLimit =
        B0.ProObjectPoint P
    ; limitProjection =
        λ d x →
          B0.ProObjectPoint.point x d
    ; limitProjectionCompatible =
        λ d x →
          B0.ProObjectPoint.coherence x d
    ; toProObjectPoint =
        id
    ; fromProObjectPoint =
        id
    ; toFromRoundtrip =
        λ _ →
          refl
    ; fromToRoundtrip =
        λ _ →
          refl
    }

record ProObjectPointwiseEq
  {P : B0.ProObjectCarrier}
  (x y : B0.ProObjectPoint P) :
  Set₁ where
  field
    atDepth :
      (d : ℕ) →
      B0.ProObjectPoint.point x d
      ≡
      B0.ProObjectPoint.point y d

open ProObjectPointwiseEq public

pointwiseEqRefl :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  ProObjectPointwiseEq x x
pointwiseEqRefl _ =
  record
    { atDepth =
        λ _ →
          refl
    }

pointwiseEqSym :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  ProObjectPointwiseEq x y →
  ProObjectPointwiseEq y x
pointwiseEqSym _ _ xy =
  record
    { atDepth =
        λ d →
          sym (ProObjectPointwiseEq.atDepth xy d)
    }

pointwiseEqTrans :
  {P : B0.ProObjectCarrier} →
  (x y z : B0.ProObjectPoint P) →
  ProObjectPointwiseEq x y →
  ProObjectPointwiseEq y z →
  ProObjectPointwiseEq x z
pointwiseEqTrans _ _ _ xy yz =
  record
    { atDepth =
        λ d →
          trans
            (ProObjectPointwiseEq.atDepth xy d)
            (ProObjectPointwiseEq.atDepth yz d)
    }

DepthAgreement :
  {P : B0.ProObjectCarrier} →
  ℕ →
  B0.ProObjectPoint P →
  B0.ProObjectPoint P →
  Set
DepthAgreement d x y =
  B0.ProObjectPoint.point x d
  ≡
  B0.ProObjectPoint.point y d

depthAgreementRefl :
  {P : B0.ProObjectCarrier} →
  (d : ℕ) →
  (x : B0.ProObjectPoint P) →
  DepthAgreement d x x
depthAgreementRefl _ _ =
  refl

depthAgreementSym :
  {P : B0.ProObjectCarrier} →
  (d : ℕ) →
  (x y : B0.ProObjectPoint P) →
  DepthAgreement d x y →
  DepthAgreement d y x
depthAgreementSym _ _ _ xy =
  sym xy

depthAgreementTrans :
  {P : B0.ProObjectCarrier} →
  (d : ℕ) →
  (x y z : B0.ProObjectPoint P) →
  DepthAgreement d x y →
  DepthAgreement d y z →
  DepthAgreement d x z
depthAgreementTrans _ _ _ _ xy yz =
  trans xy yz

depthAgreementSucToDepth :
  {P : B0.ProObjectCarrier} →
  (d : ℕ) →
  (x y : B0.ProObjectPoint P) →
  DepthAgreement (suc d) x y →
  DepthAgreement d x y
depthAgreementSucToDepth {P} d x y xy-suc =
  trans
    (sym (B0.ProObjectPoint.coherence x d))
    (trans
      (cong (B0.ProObjectCarrier.refinementMap P d) xy-suc)
      (B0.ProObjectPoint.coherence y d))

-- BallAtDepth is the proof-relevant ultrametric ball scaffold: y belongs to
-- the depth-d ball around x when the two compatible families agree at depth d.
-- This is the part Agda can prove without decidable equality, real powers, or
-- analytic metric completion.
BallAtDepth :
  {P : B0.ProObjectCarrier} →
  B0.ProObjectPoint P →
  ℕ →
  B0.ProObjectPoint P →
  Set
BallAtDepth x d y =
  DepthAgreement d x y

ballAtDepthRefl :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  (d : ℕ) →
  BallAtDepth x d x
ballAtDepthRefl x d =
  depthAgreementRefl d x

ballAtDepthSym :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  (d : ℕ) →
  BallAtDepth x d y →
  BallAtDepth y d x
ballAtDepthSym x y d xy =
  depthAgreementSym d x y xy

ballAtDepthStrongTriangleShadow :
  {P : B0.ProObjectCarrier} →
  (x y z : B0.ProObjectPoint P) →
  (d : ℕ) →
  BallAtDepth x d y →
  BallAtDepth y d z →
  BallAtDepth x d z
ballAtDepthStrongTriangleShadow x y z d xy yz =
  depthAgreementTrans d x y z xy yz

depthZeroAgreementIsFormalClose :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  DepthAgreement zero x y →
  B0.FormallyClose x y
depthZeroAgreementIsFormalClose _ _ xy =
  xy

formalCloseIsDepthZeroAgreement :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  B0.FormallyClose x y →
  DepthAgreement zero x y
formalCloseIsDepthZeroAgreement _ _ xy =
  xy

formallyCloseRefl :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  B0.FormallyClose x x
formallyCloseRefl _ =
  refl

formallyCloseSym :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  B0.FormallyClose x y →
  B0.FormallyClose y x
formallyCloseSym _ _ xy =
  sym xy

formallyCloseTrans :
  {P : B0.ProObjectCarrier} →
  (x y z : B0.ProObjectPoint P) →
  B0.FormallyClose x y →
  B0.FormallyClose y z →
  B0.FormallyClose x z
formallyCloseTrans _ _ _ xy yz =
  trans xy yz

formalDiskCenter :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  B0.FormalDisk x
formalDiskCenter x =
  x , refl

formalDiskPoint :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  B0.FormalDisk x →
  B0.ProObjectPoint P
formalDiskPoint {x = _} (y , _) =
  y

formalDiskPointIsDepthZeroClose :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  (disk : B0.FormalDisk x) →
  BallAtDepth x zero (formalDiskPoint {x = x} disk)
formalDiskPointIsDepthZeroClose {x = _} (_ , close) =
  close

DepthZeroBall :
  {P : B0.ProObjectCarrier} →
  B0.ProObjectPoint P →
  Set₁
DepthZeroBall {P} x =
  Σ (B0.ProObjectPoint P) (BallAtDepth x zero)

depthZeroBallPoint :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  DepthZeroBall x →
  B0.ProObjectPoint P
depthZeroBallPoint {x = _} (y , _) =
  y

depthZeroBallProof :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  (ball : DepthZeroBall x) →
  BallAtDepth x zero (depthZeroBallPoint {x = x} ball)
depthZeroBallProof {x = _} (_ , close) =
  close

formalDiskToDepthZeroBall :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  B0.FormalDisk x →
  DepthZeroBall x
formalDiskToDepthZeroBall {x = _} disk =
  disk

depthZeroBallToFormalDisk :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  DepthZeroBall x →
  B0.FormalDisk x
depthZeroBallToFormalDisk {x = _} ball =
  ball

formalDiskDepthZeroBall-to-from :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  (disk : B0.FormalDisk x) →
  depthZeroBallToFormalDisk {x = x} (formalDiskToDepthZeroBall {x = x} disk)
  ≡
  disk
formalDiskDepthZeroBall-to-from {x = _} _ =
  refl

formalDiskDepthZeroBall-from-to :
  {P : B0.ProObjectCarrier} →
  {x : B0.ProObjectPoint P} →
  (ball : DepthZeroBall x) →
  formalDiskToDepthZeroBall {x = x} (depthZeroBallToFormalDisk {x = x} ball)
  ≡
  ball
formalDiskDepthZeroBall-from-to {x = _} _ =
  refl

formalDiskIsDepthZeroBallLemma :
  {P : B0.ProObjectCarrier} →
  (x y : B0.ProObjectPoint P) →
  BallAtDepth x zero y
  ≡
  B0.FormallyClose x y
formalDiskIsDepthZeroBallLemma _ _ =
  refl

record FormalDiskDepthZeroBallEquivalence
  {P : B0.ProObjectCarrier}
  (x : B0.ProObjectPoint P) :
  Setω where
  field
    depthZeroBallCarrier :
      Set₁

    depthZeroBallCarrier-v :
      depthZeroBallCarrier
      ≡
      DepthZeroBall x

    toDepthZeroBall :
      B0.FormalDisk x →
      depthZeroBallCarrier

    fromDepthZeroBall :
      depthZeroBallCarrier →
      B0.FormalDisk x

    toFromRoundtrip :
      (disk : B0.FormalDisk x) →
      fromDepthZeroBall (toDepthZeroBall disk)
      ≡
      disk

    fromToRoundtrip :
      (ball : depthZeroBallCarrier) →
      toDepthZeroBall (fromDepthZeroBall ball)
      ≡
      ball

open FormalDiskDepthZeroBallEquivalence public

canonicalFormalDiskDepthZeroBallEquivalence :
  {P : B0.ProObjectCarrier} →
  (x : B0.ProObjectPoint P) →
  FormalDiskDepthZeroBallEquivalence x
canonicalFormalDiskDepthZeroBallEquivalence x =
  record
    { depthZeroBallCarrier =
        DepthZeroBall x
    ; depthZeroBallCarrier-v =
        refl
    ; toDepthZeroBall =
        formalDiskToDepthZeroBall {x = x}
    ; fromDepthZeroBall =
        depthZeroBallToFormalDisk {x = x}
    ; toFromRoundtrip =
        formalDiskDepthZeroBall-to-from {x = x}
    ; fromToRoundtrip =
        formalDiskDepthZeroBall-from-to {x = x}
    }

ballAtDepthRestrictStep :
  {P : B0.ProObjectCarrier} →
  (d : ℕ) →
  (x y : B0.ProObjectPoint P) →
  BallAtDepth x (suc d) y →
  BallAtDepth x d y
ballAtDepthRestrictStep =
  depthAgreementSucToDepth

record DepthAgreementRestrictionSurface
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    restrictOneDepth :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      BallAtDepth x (suc d) y →
      BallAtDepth x d y

    restrictOneDepth-v :
      (d : ℕ) →
      (x y : B0.ProObjectPoint P) →
      (xy : BallAtDepth x (suc d) y) →
      restrictOneDepth d x y xy
      ≡
      depthAgreementSucToDepth d x y xy

    formalDiskMemberToDepthZeroBall :
      (x : B0.ProObjectPoint P) →
      B0.FormalDisk x →
      DepthZeroBall x

    depthZeroBallMemberToFormalDisk :
      (x : B0.ProObjectPoint P) →
      DepthZeroBall x →
      B0.FormalDisk x

open DepthAgreementRestrictionSurface public

canonicalDepthAgreementRestrictionSurface :
  (P : B0.ProObjectCarrier) →
  DepthAgreementRestrictionSurface P
canonicalDepthAgreementRestrictionSurface P =
  record
    { restrictOneDepth =
        ballAtDepthRestrictStep
    ; restrictOneDepth-v =
        λ _ _ _ _ →
          refl
    ; formalDiskMemberToDepthZeroBall =
        λ x →
          formalDiskToDepthZeroBall {x = x}
    ; depthZeroBallMemberToFormalDisk =
        λ x →
          depthZeroBallToFormalDisk {x = x}
    }

record ProObjectUltrametricTopologySurface
  (P : B0.ProObjectCarrier) :
  Set₁ where
  field
    Ball :
      B0.ProObjectPoint P →
      ℕ →
      B0.ProObjectPoint P →
      Set

    ballIsDepthAgreement :
      (x y : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y
      ≡
      DepthAgreement d x y

    ballReflexive :
      (x : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d x

    ballSymmetric :
      (x y : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y →
      Ball y d x

    ballStrongTriangleShadow :
      (x y z : B0.ProObjectPoint P) →
      (d : ℕ) →
      Ball x d y →
      Ball y d z →
      Ball x d z

    formalDiskIsDepthZeroBall :
      (x y : B0.ProObjectPoint P) →
      Ball x zero y
      ≡
      B0.FormallyClose x y

    topologyStatus :
      String

    topologyStatus-v :
      topologyStatus
      ≡
      "DASHI-side-depthwise-ball-laws-proved-no-real-valued-ultrametric-completion-here"

open ProObjectUltrametricTopologySurface public

canonicalProObjectUltrametricTopologySurface :
  (P : B0.ProObjectCarrier) →
  ProObjectUltrametricTopologySurface P
canonicalProObjectUltrametricTopologySurface P =
  record
    { Ball =
        BallAtDepth
    ; ballIsDepthAgreement =
        λ _ _ _ →
          refl
    ; ballReflexive =
        ballAtDepthRefl
    ; ballSymmetric =
        ballAtDepthSym
    ; ballStrongTriangleShadow =
        ballAtDepthStrongTriangleShadow
    ; formalDiskIsDepthZeroBall =
        formalDiskIsDepthZeroBallLemma
    ; topologyStatus =
        "DASHI-side-depthwise-ball-laws-proved-no-real-valued-ultrametric-completion-here"
    ; topologyStatus-v =
        refl
    }

data B01ConstructiveComponent : Set where
  compatibleFamilyLimit :
    B01ConstructiveComponent

  depthProjection :
    B01ConstructiveComponent

  refinementCoherence :
    B01ConstructiveComponent

  depthwiseAgreementBall :
    B01ConstructiveComponent

  depthZeroFormalDisk :
    B01ConstructiveComponent

  equivalenceRelationLaws :
    B01ConstructiveComponent

canonicalB01ConstructiveComponents :
  List B01ConstructiveComponent
canonicalB01ConstructiveComponents =
  compatibleFamilyLimit
  ∷ depthProjection
  ∷ refinementCoherence
  ∷ depthwiseAgreementBall
  ∷ depthZeroFormalDisk
  ∷ equivalenceRelationLaws
  ∷ []

data B01RemainingProofObligation : Set where
  missingDecidableSeparationDepth :
    B01RemainingProofObligation

  missingRealValuedRho :
    B01RemainingProofObligation

  missingMetricCompletionProof :
    B01RemainingProofObligation

  missingCompactProfiniteProof :
    B01RemainingProofObligation

  missingTransportSmoothFunctionSheaf :
    B01RemainingProofObligation

  missingFirstOrderApproximationLemma :
    B01RemainingProofObligation

  missingDCHoTTFormalDiskEquivalence :
    B01RemainingProofObligation

  missingLinearRefinementVectorSpaceBinding :
    B01RemainingProofObligation

canonicalB01RemainingProofObligations :
  List B01RemainingProofObligation
canonicalB01RemainingProofObligations =
  missingDecidableSeparationDepth
  ∷ missingRealValuedRho
  ∷ missingMetricCompletionProof
  ∷ missingCompactProfiniteProof
  ∷ missingTransportSmoothFunctionSheaf
  ∷ missingFirstOrderApproximationLemma
  ∷ missingDCHoTTFormalDiskEquivalence
  ∷ missingLinearRefinementVectorSpaceBinding
  ∷ []

record LinearRefinementBindingSurface
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    TangentScalar :
      Set

    TangentVectorAt :
      B0.ProObjectCarrier.depthCarrier P zero →
      Set

    DepthOneFibreOver :
      B0.ProObjectCarrier.depthCarrier P zero →
      Set

    depthOneFibreToTangentVector :
      (x0 : B0.ProObjectCarrier.depthCarrier P zero) →
      DepthOneFibreOver x0 →
      TangentVectorAt x0

    zeroVector :
      (x0 : B0.ProObjectCarrier.depthCarrier P zero) →
      TangentVectorAt x0

    addVector :
      (x0 : B0.ProObjectCarrier.depthCarrier P zero) →
      TangentVectorAt x0 →
      TangentVectorAt x0 →
      TangentVectorAt x0

    scalarMultiply :
      (x0 : B0.ProObjectCarrier.depthCarrier P zero) →
      TangentScalar →
      TangentVectorAt x0 →
      TangentVectorAt x0

    vectorSpaceLawTarget :
      String

    vectorSpaceLawTarget-v :
      vectorSpaceLawTarget
      ≡
      "target-only-depth-one-refinement-fibres-form-vector-spaces-from-carrier-linear-fibres"

    linearRefinementPromoted :
      Bool

    linearRefinementPromoted-v :
      linearRefinementPromoted
      ≡
      false

open LinearRefinementBindingSurface public

record B01ProObjectSemanticsReceipt
  (P : B0.ProObjectCarrier) :
  Setω where
  field
    constructedLimit :
      ConstructedProObjectLimitSurface P

    ultrametricTopology :
      ProObjectUltrametricTopologySurface P

    depthAgreementRestrictions :
      DepthAgreementRestrictionSurface P

    constructiveComponents :
      List B01ConstructiveComponent

    constructiveComponentsAreCanonical :
      constructiveComponents
      ≡
      canonicalB01ConstructiveComponents

    remainingProofObligations :
      List B01RemainingProofObligation

    remainingProofObligationsAreCanonical :
      remainingProofObligations
      ≡
      canonicalB01RemainingProofObligations

    ImReducedSpace :
      Set

    ImReducedSpaceIsDepthZero :
      ImReducedSpace
      ≡
      B0.ProObjectCarrier.depthCarrier P zero

    formalThickeningFibre :
      ImReducedSpace →
      Set₁

    formalThickeningStatus :
      String

    formalThickeningStatus-v :
      formalThickeningStatus
      ≡
      "DASHI-side-formal-thickening-over-depth-zero-recorded-DCHoTT-Im-equivalence-open"

    b01DASHISideConstructed :
      Bool

    b01DASHISideConstructed-v :
      b01DASHISideConstructed
      ≡
      true

    dchottFormalDiskEquivalenceProved :
      Bool

    dchottFormalDiskEquivalenceProved-v :
      dchottFormalDiskEquivalenceProved
      ≡
      false

    b0Promoted :
      Bool

    b0Promoted-v :
      b0Promoted
      ≡
      false

open B01ProObjectSemanticsReceipt public

canonicalB01ProObjectSemanticsReceipt :
  (P : B0.ProObjectCarrier) →
  B01ProObjectSemanticsReceipt P
canonicalB01ProObjectSemanticsReceipt P =
  record
    { constructedLimit =
        canonicalConstructedProObjectLimitSurface P
    ; ultrametricTopology =
        canonicalProObjectUltrametricTopologySurface P
    ; depthAgreementRestrictions =
        canonicalDepthAgreementRestrictionSurface P
    ; constructiveComponents =
        canonicalB01ConstructiveComponents
    ; constructiveComponentsAreCanonical =
        refl
    ; remainingProofObligations =
        canonicalB01RemainingProofObligations
    ; remainingProofObligationsAreCanonical =
        refl
    ; ImReducedSpace =
        B0.ProObjectCarrier.depthCarrier P zero
    ; ImReducedSpaceIsDepthZero =
        refl
    ; formalThickeningFibre =
        λ x0 →
          ΣFormalFibre P x0
    ; formalThickeningStatus =
        "DASHI-side-formal-thickening-over-depth-zero-recorded-DCHoTT-Im-equivalence-open"
    ; formalThickeningStatus-v =
        refl
    ; b01DASHISideConstructed =
        true
    ; b01DASHISideConstructed-v =
        refl
    ; dchottFormalDiskEquivalenceProved =
        false
    ; dchottFormalDiskEquivalenceProved-v =
        refl
    ; b0Promoted =
        false
    ; b0Promoted-v =
        refl
    }
  where
    ΣFormalFibre :
      (Q : B0.ProObjectCarrier) →
      B0.ProObjectCarrier.depthCarrier Q zero →
      Set₁
    ΣFormalFibre Q x0 =
      Σ (B0.ProObjectPoint Q) (λ x → B0.Im x ≡ x0)
