module DASHI.Physics.Closure.KleinQuarticQMReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Klein quartic / X_0(49)^3 receipt.
--
-- This corrects the previous correction.  Markushevich--Moreau record
-- that the Klein quartic Jacobian is isomorphic, as an abstract abelian
-- variety, to the cube of X_0(49).  Thus the product splitting is the
-- correct object-level source of three rank-two CM factors.  The remaining
-- carrier problem is not the existence of the three factors, but the
-- PSL(2,F7)-equivariant assignment of FactorVec CKM data to those factors.

data KleinQuarticCurve : Set where
  kleinQuartic :
    KleinQuarticCurve

data AutomorphismGroup : Set where
  PSL2F7 :
    AutomorphismGroup

data JacobianStructure : Set where
  cubeOfX049 :
    JacobianStructure

data ProductSplittingClaim : Set where
  productOfThreeX049Factors :
    ProductSplittingClaim

data EndomorphismAlgebraDatum : Set where
  M3QsqrtMinus7 :
    EndomorphismAlgebraDatum

data SupportStatus : Set where
  positiveResult_equivariantMorphismOpen :
    SupportStatus

data OpenKleinQuarticProblem : Set where
  PSL2F7EquivariantFactorAssignment :
    OpenKleinQuarticProblem

  flavourSubgroupIdentification :
    OpenKleinQuarticProblem

  symmetryBreakingForGenerationIndex :
    OpenKleinQuarticProblem

data PromotionToken : Set where

promotionImpossibleHere :
  PromotionToken →
  ⊥
promotionImpossibleHere ()

canonicalOpenProblems :
  List OpenKleinQuarticProblem
canonicalOpenProblems =
  PSL2F7EquivariantFactorAssignment
  ∷ flavourSubgroupIdentification
  ∷ symmetryBreakingForGenerationIndex
  ∷ []

kleinQuarticStatement :
  String
kleinQuarticStatement =
  "The Klein quartic is the genus-3 Hurwitz curve associated to the triangle group Delta(2,3,7), with automorphism group PSL(2,F7) of order 168."

jacobianCorrectionStatement :
  String
jacobianCorrectionStatement =
  "Correcting the correction: J(K) is isomorphic, as an abstract abelian variety, to X_0(49)^3; it is not simple."

endomorphismAlgebraStatement :
  String
endomorphismAlgebraStatement =
  "The corresponding rational endomorphism algebra is M_3(Q(sqrt(-7))), accommodating the PSL(2,F7) action on the three-factor product."

X049CMFieldStatement :
  String
X049CMFieldStatement =
  "X_0(49) has CM by O_-7 and lies in the Q(sqrt(-7))-isogeny class of the j=-3375 elliptic curve."

periodLatticeStatement :
  String
periodLatticeStatement =
  "The period lattice uses alpha=(1+i*sqrt(7))/2, the O_-7 CM generator appearing in the Klein-quartic root system."

characterValueStatement :
  String
characterValueStatement =
  "The 3-dimensional PSL(2,F7) representation has order-7 character value -(zeta7+zeta7^2+zeta7^4)=(-1+i*sqrt(7))/2=tau_-7, the D=-7 CM point period."

phenomenologyReferenceStatement :
  String
phenomenologyReferenceStatement =
  "PSL(2,F7) is also a known finite flavour-symmetry candidate in the phenomenological literature, including Luhn-Nasri-Ramond 2007 and King-Luhn 2013."

morphismOpenStatement :
  String
morphismOpenStatement =
  "The single-factor morphism to T_7(X_0(49)) is already recorded; the open task is a PSL(2,F7)-equivariant three-factor projection, with carrier symmetry-breaking data selecting one X_0(49) factor per generation."

record KleinQuarticQMReceipt : Set where
  field
    curve :
      KleinQuarticCurve

    curveIsKleinQuartic :
      curve ≡ kleinQuartic

    curveStatement :
      String

    curveStatementIsCanonical :
      curveStatement ≡ kleinQuarticStatement

    automorphismGroup :
      AutomorphismGroup

    automorphismGroupIsPSL2F7 :
      automorphismGroup ≡ PSL2F7

    genusThree :
      Bool

    genusThreeIsTrue :
      genusThree ≡ true

    jacobian :
      JacobianStructure

    jacobianIsX049Cubed :
      jacobian ≡ cubeOfX049

    productSplittingTrue :
      Bool

    productSplittingTrueIsTrue :
      productSplittingTrue ≡ true

    productSplittingClaim :
      ProductSplittingClaim

    productSplittingClaimIsX049Cubed :
      productSplittingClaim ≡ productOfThreeX049Factors

    jacobianCorrection :
      String

    jacobianCorrectionIsCanonical :
      jacobianCorrection ≡ jacobianCorrectionStatement

    endomorphismAlgebra :
      EndomorphismAlgebraDatum

    endomorphismAlgebraIsMatrixCM :
      endomorphismAlgebra ≡ M3QsqrtMinus7

    threeGenerationStructure :
      Bool

    threeGenerationStructureIsProvided :
      threeGenerationStructure ≡ true

    singleFactorMorphismExists :
      Bool

    singleFactorMorphismExistsIsTrue :
      singleFactorMorphismExists ≡ true

    endomorphismAlgebraSummary :
      String

    endomorphismAlgebraSummaryIsCanonical :
      endomorphismAlgebraSummary ≡ endomorphismAlgebraStatement

    X049CMField :
      String

    X049CMFieldIsCanonical :
      X049CMField ≡ X049CMFieldStatement

    periodLatticeGenerator :
      String

    periodLatticeGeneratorIsCanonical :
      periodLatticeGenerator ≡ periodLatticeStatement

    orderSevenCharacterGivesCMPoint :
      Bool

    orderSevenCharacterGivesCMPointIsTrue :
      orderSevenCharacterGivesCMPoint ≡ true

    characterValue :
      String

    characterValueIsCanonical :
      characterValue ≡ characterValueStatement

    PSL2F7PhenomenologyReference :
      String

    PSL2F7PhenomenologyReferenceIsCanonical :
      PSL2F7PhenomenologyReference ≡ phenomenologyReferenceStatement

    status :
      SupportStatus

    statusIsPositiveEquivariantMorphismOpen :
      status ≡ positiveResult_equivariantMorphismOpen

    openProblems :
      List OpenKleinQuarticProblem

    openProblemsAreCanonical :
      openProblems ≡ canonicalOpenProblems

    carrierMorphismOpen :
      Bool

    carrierMorphismOpenIsTrue :
      carrierMorphismOpen ≡ true

    openMorphismSummary :
      String

    openMorphismSummaryIsCanonical :
      openMorphismSummary ≡ morphismOpenStatement

    threeGenerationObjectExists :
      Bool

    threeGenerationObjectExistsIsTrue :
      threeGenerationObjectExists ≡ true

    equivariantGenerationAssignmentOpen :
      Bool

    equivariantGenerationAssignmentOpenIsTrue :
      equivariantGenerationAssignmentOpen ≡ true

    symmetryBreakingMechanismOpen :
      Bool

    symmetryBreakingMechanismOpenIsTrue :
      symmetryBreakingMechanismOpen ≡ true

    physicalCKMPromoted :
      Bool

    physicalCKMPromotedIsFalse :
      physicalCKMPromoted ≡ false

open KleinQuarticQMReceipt public

canonicalKleinQuarticQMReceipt :
  KleinQuarticQMReceipt
canonicalKleinQuarticQMReceipt =
  record
    { curve =
        kleinQuartic
    ; curveIsKleinQuartic =
        refl
    ; curveStatement =
        kleinQuarticStatement
    ; curveStatementIsCanonical =
        refl
    ; automorphismGroup =
        PSL2F7
    ; automorphismGroupIsPSL2F7 =
        refl
    ; genusThree =
        true
    ; genusThreeIsTrue =
        refl
    ; jacobian =
        cubeOfX049
    ; jacobianIsX049Cubed =
        refl
    ; productSplittingTrue =
        true
    ; productSplittingTrueIsTrue =
        refl
    ; productSplittingClaim =
        productOfThreeX049Factors
    ; productSplittingClaimIsX049Cubed =
        refl
    ; jacobianCorrection =
        jacobianCorrectionStatement
    ; jacobianCorrectionIsCanonical =
        refl
    ; endomorphismAlgebra =
        M3QsqrtMinus7
    ; endomorphismAlgebraIsMatrixCM =
        refl
    ; threeGenerationStructure =
        true
    ; threeGenerationStructureIsProvided =
        refl
    ; singleFactorMorphismExists =
        true
    ; singleFactorMorphismExistsIsTrue =
        refl
    ; endomorphismAlgebraSummary =
        endomorphismAlgebraStatement
    ; endomorphismAlgebraSummaryIsCanonical =
        refl
    ; X049CMField =
        X049CMFieldStatement
    ; X049CMFieldIsCanonical =
        refl
    ; periodLatticeGenerator =
        periodLatticeStatement
    ; periodLatticeGeneratorIsCanonical =
        refl
    ; orderSevenCharacterGivesCMPoint =
        true
    ; orderSevenCharacterGivesCMPointIsTrue =
        refl
    ; characterValue =
        characterValueStatement
    ; characterValueIsCanonical =
        refl
    ; PSL2F7PhenomenologyReference =
        phenomenologyReferenceStatement
    ; PSL2F7PhenomenologyReferenceIsCanonical =
        refl
    ; status =
        positiveResult_equivariantMorphismOpen
    ; statusIsPositiveEquivariantMorphismOpen =
        refl
    ; openProblems =
        canonicalOpenProblems
    ; openProblemsAreCanonical =
        refl
    ; carrierMorphismOpen =
        true
    ; carrierMorphismOpenIsTrue =
        refl
    ; openMorphismSummary =
        morphismOpenStatement
    ; openMorphismSummaryIsCanonical =
        refl
    ; threeGenerationObjectExists =
        true
    ; threeGenerationObjectExistsIsTrue =
        refl
    ; equivariantGenerationAssignmentOpen =
        true
    ; equivariantGenerationAssignmentOpenIsTrue =
        refl
    ; symmetryBreakingMechanismOpen =
        true
    ; symmetryBreakingMechanismOpenIsTrue =
        refl
    ; physicalCKMPromoted =
        false
    ; physicalCKMPromotedIsFalse =
        refl
    }

kleinQuarticProductSplittingConfirmed :
  productSplittingTrue canonicalKleinQuarticQMReceipt ≡ true
kleinQuarticProductSplittingConfirmed =
  refl

kleinQuarticMorphismStillOpen :
  carrierMorphismOpen canonicalKleinQuarticQMReceipt ≡ true
kleinQuarticMorphismStillOpen =
  refl

kleinQuarticDoesNotPromoteCKM :
  physicalCKMPromoted canonicalKleinQuarticQMReceipt ≡ false
kleinQuarticDoesNotPromoteCKM =
  refl

kleinQuarticEquivariantAssignmentStillOpen :
  equivariantGenerationAssignmentOpen canonicalKleinQuarticQMReceipt ≡ true
kleinQuarticEquivariantAssignmentStillOpen =
  refl

kleinQuarticSymmetryBreakingStillOpen :
  symmetryBreakingMechanismOpen canonicalKleinQuarticQMReceipt ≡ true
kleinQuarticSymmetryBreakingStillOpen =
  refl
