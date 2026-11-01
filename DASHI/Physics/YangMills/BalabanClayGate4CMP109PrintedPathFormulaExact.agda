module DASHI.Physics.YangMills.BalabanClayGate4CMP109PrintedPathFormulaExact where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier
  using (Axis4; PositiveBond; pair; first; second)
open import DASHI.Physics.YangMills.BalabanRootedPolymerWordEntropyExact
  using (SignedAxis4)

import DASHI.Physics.YangMills.BalabanClayT2PeriodicBlockPolymerCarrierExact as Periodic
import DASHI.Physics.YangMills.BalabanClayGate4PeriodicBondPathBianchiExact as Bond
import DASHI.Physics.YangMills.BalabanClayGate4CMP109ProjectedEndpointBlocksExact as Endpoint

------------------------------------------------------------------------
-- Literal path and averaging syntax for CMP 109, equations (0.4), (0.11)
-- and (0.12).
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (2) (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Equation (0.4) averages
--
--   (1/i) log U(Γ ∪ [x,x'] ∪ (-Γ') ∪ (-c))
--
-- over x in B(c_-), Γ in G(c_-,x), and Γ' in G(c_+,x').
-- Equation (0.11) replaces a contour variable by a permutation-invariant
-- group average U(y,x).  Equation (0.12) then uses
--
--   U(c_-,x) U([x,x']) U(x',c_+) U(-c)
--
-- inside the same L^{-d} block average.  The datatype and folds below encode
-- those printed orders literally.  They do not commute or reassociate factors.
------------------------------------------------------------------------

infixr 20 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[] ++ right = right
(value ∷ left) ++ right = value ∷ (left ++ right)

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ values) = suc (listLength values)

repeatDirection : Nat → SignedAxis4 → List SignedAxis4
repeatDirection zero direction = []
repeatDirection (suc count) direction =
  direction ∷ repeatDirection count direction

repeatDirectionLength : ∀ count direction →
  listLength (repeatDirection count direction) ≡ count
repeatDirectionLength zero direction = refl
repeatDirectionLength (suc count) direction =
  cong suc (repeatDirectionLength count direction)

positiveStraightDirections : Nat → Axis4 → List SignedAxis4
positiveStraightDirections count axis =
  repeatDirection count (pair axis true)

negativeStraightDirections : Nat → Axis4 → List SignedAxis4
negativeStraightDirections count axis =
  repeatDirection count (pair axis false)

walkAppend :
  ∀ {n} (site : Periodic.PeriodicBlock n)
    left right →
  Bond.walk site (left ++ right)
  ≡ Bond.walk (Bond.walk site left) right
walkAppend site [] right = refl
walkAppend site (direction ∷ left) right =
  walkAppend (Bond.walkStep site direction) left right

translatedFinePoint :
  ∀ {n} → Nat → Axis4 →
  Periodic.PeriodicBlock n → Periodic.PeriodicBlock n
translatedFinePoint blockSide axis fineSite =
  Bond.walk fineSite (positiveStraightDirections blockSide axis)

record PeriodicCMP109ContourGeometry
    (fineN coarseN : Nat) : Set₁ where
  field
    projection : Endpoint.PeriodicCMP109SiteProjection fineN coarseN
    blockSide : Nat

    embedCoarseSite :
      Periodic.PeriodicBlock coarseN →
      Periodic.PeriodicBlock fineN

    sourceContour :
      PositiveBond (suc coarseN) →
      Periodic.PeriodicBlock fineN →
      List SignedAxis4

    targetContourReverse :
      PositiveBond (suc coarseN) →
      Periodic.PeriodicBlock fineN →
      List SignedAxis4

    sourceContourEndpoint : ∀ coarseBond fineSite →
      Endpoint.coarseOfFineSite projection fineSite
        ≡ Endpoint.sourceEndpoint coarseBond →
      Bond.walk
        (embedCoarseSite (Endpoint.sourceEndpoint coarseBond))
        (sourceContour coarseBond fineSite)
      ≡ fineSite

    translatedPointProjectsToTarget : ∀ coarseBond fineSite →
      Endpoint.coarseOfFineSite projection fineSite
        ≡ Endpoint.sourceEndpoint coarseBond →
      Endpoint.coarseOfFineSite projection
        (translatedFinePoint
          blockSide (second coarseBond) fineSite)
      ≡ Endpoint.targetEndpoint coarseBond

    targetContourEndpoint : ∀ coarseBond fineSite →
      Endpoint.coarseOfFineSite projection fineSite
        ≡ Endpoint.sourceEndpoint coarseBond →
      Bond.walk
        (translatedFinePoint
          blockSide (second coarseBond) fineSite)
        (targetContourReverse coarseBond fineSite)
      ≡ embedCoarseSite (Endpoint.targetEndpoint coarseBond)

    coarseReverseEndpoint : ∀ coarseBond →
      Bond.walk
        (embedCoarseSite (Endpoint.targetEndpoint coarseBond))
        (negativeStraightDirections blockSide (second coarseBond))
      ≡ embedCoarseSite (Endpoint.sourceEndpoint coarseBond)

open PeriodicCMP109ContourGeometry public

relativeLoopDirections :
  ∀ {fineN coarseN} →
  PeriodicCMP109ContourGeometry fineN coarseN →
  PositiveBond (suc coarseN) →
  Periodic.PeriodicBlock fineN →
  List SignedAxis4
relativeLoopDirections geometry coarseBond fineSite =
  sourceContour geometry coarseBond fineSite
  ++ (positiveStraightDirections
        (blockSide geometry) (second coarseBond)
  ++ (targetContourReverse geometry coarseBond fineSite
  ++ negativeStraightDirections
        (blockSide geometry) (second coarseBond)))

relativeLoopCloses :
  ∀ {fineN coarseN}
    (geometry : PeriodicCMP109ContourGeometry fineN coarseN)
    coarseBond fineSite →
  Endpoint.coarseOfFineSite (projection geometry) fineSite
    ≡ Endpoint.sourceEndpoint coarseBond →
  Bond.walk
    (embedCoarseSite geometry (Endpoint.sourceEndpoint coarseBond))
    (relativeLoopDirections geometry coarseBond fineSite)
  ≡ embedCoarseSite geometry (Endpoint.sourceEndpoint coarseBond)
relativeLoopCloses geometry coarseBond fineSite sourceMembership =
  trans
    (walkAppend
      (embedCoarseSite geometry (Endpoint.sourceEndpoint coarseBond))
      (sourceContour geometry coarseBond fineSite)
      (positiveStraightDirections
        (blockSide geometry) (second coarseBond)
       ++ (targetContourReverse geometry coarseBond fineSite
       ++ negativeStraightDirections
          (blockSide geometry) (second coarseBond))))
    (subst
      (λ sourceEnd →
        Bond.walk sourceEnd
          (positiveStraightDirections
            (blockSide geometry) (second coarseBond)
           ++ (targetContourReverse geometry coarseBond fineSite
           ++ negativeStraightDirections
              (blockSide geometry) (second coarseBond)))
        ≡ embedCoarseSite geometry
            (Endpoint.sourceEndpoint coarseBond))
      (sym (sourceContourEndpoint geometry coarseBond fineSite sourceMembership))
      (trans
        (walkAppend fineSite
          (positiveStraightDirections
            (blockSide geometry) (second coarseBond))
          (targetContourReverse geometry coarseBond fineSite
           ++ negativeStraightDirections
              (blockSide geometry) (second coarseBond)))
        (trans
          (walkAppend
            (translatedFinePoint
              (blockSide geometry) (second coarseBond) fineSite)
            (targetContourReverse geometry coarseBond fineSite)
            (negativeStraightDirections
              (blockSide geometry) (second coarseBond)))
          (subst
            (λ targetEnd →
              Bond.walk targetEnd
                (negativeStraightDirections
                  (blockSide geometry) (second coarseBond))
              ≡ embedCoarseSite geometry
                  (Endpoint.sourceEndpoint coarseBond))
            (sym (targetContourEndpoint geometry
              coarseBond fineSite sourceMembership))
            (coarseReverseEndpoint geometry coarseBond)))))

------------------------------------------------------------------------
-- Exact printed segment order for equation (0.4).
------------------------------------------------------------------------

data PrintedLoopSegment
    (Path FineBond CoarseBond : Set) : Set where
  sourcePathSegment : Path → PrintedLoopSegment Path FineBond CoarseBond
  crossingSegment : FineBond → PrintedLoopSegment Path FineBond CoarseBond
  reversedTargetPathSegment : Path → PrintedLoopSegment Path FineBond CoarseBond
  reversedCoarseBondSegment : CoarseBond → PrintedLoopSegment Path FineBond CoarseBond

printedEquation04Loop :
  ∀ {Path FineBond CoarseBond} →
  Path → FineBond → Path → CoarseBond →
  List (PrintedLoopSegment Path FineBond CoarseBond)
printedEquation04Loop sourcePath crossing targetPath coarseBond =
  sourcePathSegment sourcePath ∷
  crossingSegment crossing ∷
  reversedTargetPathSegment targetPath ∷
  reversedCoarseBondSegment coarseBond ∷ []

printedEquation04HasFourOrderedSegments :
  ∀ {Path FineBond CoarseBond}
    (sourcePath : Path) (crossing : FineBond)
    (targetPath : Path) (coarseBond : CoarseBond) →
  listLength
    (printedEquation04Loop sourcePath crossing targetPath coarseBond)
  ≡ suc (suc (suc (suc zero)))
printedEquation04HasFourOrderedSegments sourcePath crossing targetPath coarseBond = refl

record PrintedCMP109Equation04Data
    (Field CoarseBond FineSite FineBond Path Group Lie Scalar : Set) : Set₁ where
  field
    blockSites : CoarseBond → List FineSite
    sourceContours : CoarseBond → FineSite → List Path
    targetContours : CoarseBond → FineSite → List Path
    crossingBond : CoarseBond → FineSite → FineBond

    blockWeight : CoarseBond → Scalar
    sourceContourWeight : CoarseBond → FineSite → Scalar
    targetContourWeight : CoarseBond → FineSite → Scalar

    zeroLie : Lie
    addLie : Lie → Lie → Lie
    scaleLie : Scalar → Lie → Lie

    identityGroup : Group
    multiplyGroup : Group → Group → Group
    segmentValue :
      Field → PrintedLoopSegment Path FineBond CoarseBond → Group
    antiHermitianLogCoordinate : Group → Lie
    outerExponential : Lie → Group
    coarseBondValue : Field → CoarseBond → Group

open PrintedCMP109Equation04Data public

sumList :
  (A : Set) (Scalar : Set) →
  Scalar → (Scalar → Scalar → Scalar) →
  List A → (A → Scalar) → Scalar
sumList A Scalar scalar add [] term = scalar
sumList A Scalar scalar add (value ∷ values) term =
  add (term value) (sumList A Scalar scalar add values term)

segmentProduct :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar}
    (dataSet : PrintedCMP109Equation04Data
      Field CoarseBond FineSite FineBond Path Group Lie Scalar) →
  Field → List (PrintedLoopSegment Path FineBond CoarseBond) → Group
segmentProduct dataSet coarseField [] = identityGroup dataSet
segmentProduct dataSet coarseField (segment ∷ segments) =
  multiplyGroup dataSet
    (segmentValue dataSet coarseField segment)
    (segmentProduct dataSet coarseField segments)

printedEquation04LoopHolonomy :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar}
    (dataSet : PrintedCMP109Equation04Data
      Field CoarseBond FineSite FineBond Path Group Lie Scalar) →
  Field → CoarseBond → FineSite → Path → Path → Group
printedEquation04LoopHolonomy dataSet coarseField coarse fine sourcePath targetPath =
  segmentProduct dataSet coarseField
    (printedEquation04Loop
      sourcePath
      (crossingBond dataSet coarse fine)
      targetPath
      coarse)

printedEquation04LieAverage :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar} →
  PrintedCMP109Equation04Data
    Field CoarseBond FineSite FineBond Path Group Lie Scalar →
  Field → CoarseBond → Lie
printedEquation04LieAverage dataSet coarseField coarse =
  sumList _ _ (zeroLie dataSet) (addLie dataSet)
    (blockSites dataSet coarse)
    (λ fine →
      scaleLie dataSet (blockWeight dataSet coarse)
        (sumList _ _ (zeroLie dataSet) (addLie dataSet)
          (sourceContours dataSet coarse fine)
          (λ sourcePath →
            scaleLie dataSet
              (sourceContourWeight dataSet coarse fine)
              (sumList _ _ (zeroLie dataSet) (addLie dataSet)
                (targetContours dataSet coarse fine)
                (λ targetPath →
                  scaleLie dataSet
                    (targetContourWeight dataSet coarse fine)
                    (antiHermitianLogCoordinate dataSet
                      (printedEquation04LoopHolonomy dataSet coarseField coarse fine
                        sourcePath targetPath)))))))

printedEquation04Map :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar} →
  PrintedCMP109Equation04Data
    Field CoarseBond FineSite FineBond Path Group Lie Scalar →
  Field → CoarseBond → Group
printedEquation04Map dataSet coarseField coarse =
  multiplyGroup dataSet
    (outerExponential dataSet
      (printedEquation04LieAverage dataSet coarseField coarse))
    (coarseBondValue dataSet coarseField coarse)

implementedEquation04Map :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar} →
  PrintedCMP109Equation04Data
    Field CoarseBond FineSite FineBond Path Group Lie Scalar →
  Field → CoarseBond → Group
implementedEquation04Map = printedEquation04Map

implementedEquation04MatchesPrinted :
  ∀ {Field CoarseBond FineSite FineBond Path Group Lie Scalar}
    (dataSet : PrintedCMP109Equation04Data
      Field CoarseBond FineSite FineBond Path Group Lie Scalar) →
  implementedEquation04Map dataSet ≡ printedEquation04Map dataSet
implementedEquation04MatchesPrinted dataSet = refl

------------------------------------------------------------------------
-- Euclidean-averaged contour version, equations (0.11)--(0.12).
------------------------------------------------------------------------

record PrintedCMP109Equation012Data
    (Field CoarseBond FineSite Group Lie Scalar : Set) : Set₁ where
  field
    blockSites : CoarseBond → List FineSite
    blockWeight : CoarseBond → Scalar

    zeroLie : Lie
    addLie : Lie → Lie → Lie
    scaleLie : Scalar → Lie → Lie

    multiplyGroup : Group → Group → Group
    sourceAveragedContour : Field → CoarseBond → FineSite → Group
    crossingValue : Field → CoarseBond → FineSite → Group
    targetAveragedContourReverse : Field → CoarseBond → FineSite → Group
    reversedCoarseBondValue : Field → CoarseBond → Group
    coarseBondValue : Field → CoarseBond → Group

    antiHermitianLogCoordinate : Group → Lie
    outerExponential : Lie → Group

open PrintedCMP109Equation012Data public

printedEquation012RelativeProduct :
  ∀ {Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar) →
  Field → CoarseBond → FineSite → Group
printedEquation012RelativeProduct dataSet coarseField coarse fine =
  multiplyGroup dataSet
    (sourceAveragedContour dataSet coarseField coarse fine)
    (multiplyGroup dataSet
      (crossingValue dataSet coarseField coarse fine)
      (multiplyGroup dataSet
        (targetAveragedContourReverse dataSet coarseField coarse fine)
        (reversedCoarseBondValue dataSet coarseField coarse)))

printedEquation012LieAverage :
  ∀ {Field CoarseBond FineSite Group Lie Scalar} →
  PrintedCMP109Equation012Data
    Field CoarseBond FineSite Group Lie Scalar →
  Field → CoarseBond → Lie
printedEquation012LieAverage dataSet coarseField coarse =
  sumList _ _ (zeroLie dataSet) (addLie dataSet)
    (blockSites dataSet coarse)
    (λ fine →
      scaleLie dataSet (blockWeight dataSet coarse)
        (antiHermitianLogCoordinate dataSet
          (printedEquation012RelativeProduct dataSet coarseField coarse fine)))

printedEquation012Map :
  ∀ {Field CoarseBond FineSite Group Lie Scalar} →
  PrintedCMP109Equation012Data
    Field CoarseBond FineSite Group Lie Scalar →
  Field → CoarseBond → Group
printedEquation012Map dataSet coarseField coarse =
  multiplyGroup dataSet
    (outerExponential dataSet
      (printedEquation012LieAverage dataSet coarseField coarse))
    (coarseBondValue dataSet coarseField coarse)

implementedEquation012Map :
  ∀ {Field CoarseBond FineSite Group Lie Scalar} →
  PrintedCMP109Equation012Data
    Field CoarseBond FineSite Group Lie Scalar →
  Field → CoarseBond → Group
implementedEquation012Map = printedEquation012Map

implementedEquation012MatchesPrinted :
  ∀ {Field CoarseBond FineSite Group Lie Scalar}
    (dataSet : PrintedCMP109Equation012Data
      Field CoarseBond FineSite Group Lie Scalar) →
  implementedEquation012Map dataSet ≡ printedEquation012Map dataSet
implementedEquation012MatchesPrinted dataSet = refl

data CMP109PrintedMapVariant : Set where
  contourPairAverage04 : CMP109PrintedMapVariant
  euclideanAveragedContour012 : CMP109PrintedMapVariant

selectedCMP109PrintedMapVariant : CMP109PrintedMapVariant
selectedCMP109PrintedMapVariant = euclideanAveragedContour012

cmp109StraightCrossingPathConstructionLevel : ProofLevel
cmp109StraightCrossingPathConstructionLevel = computed

cmp109RelativeLoopClosureAssemblyLevel : ProofLevel
cmp109RelativeLoopClosureAssemblyLevel = machineChecked

cmp109Equation04OrderedPathSyntaxLevel : ProofLevel
cmp109Equation04OrderedPathSyntaxLevel = computed

cmp109Equation04LiteralMapEqualityLevel : ProofLevel
cmp109Equation04LiteralMapEqualityLevel = machineChecked

cmp109Equation012LiteralMapEqualityLevel : ProofLevel
cmp109Equation012LiteralMapEqualityLevel = machineChecked

cmp109EuclideanAveragedContourVariantSelectionLevel : ProofLevel
cmp109EuclideanAveragedContourVariantSelectionLevel = computed

physicalCMP109ContourEndpointInputsLevel : ProofLevel
physicalCMP109ContourEndpointInputsLevel = conditional

physicalCMP109BlockProjectionTranslationInputsLevel : ProofLevel
physicalCMP109BlockProjectionTranslationInputsLevel = conditional

physicalCMP109GroupAverage011InputsLevel : ProofLevel
physicalCMP109GroupAverage011InputsLevel = conditional
