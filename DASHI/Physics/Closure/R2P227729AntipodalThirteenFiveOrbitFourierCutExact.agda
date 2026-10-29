module DASHI.Physics.Closure.R2P227729AntipodalThirteenFiveOrbitFourierCutExact where

------------------------------------------------------------------------
-- EXISTING 13-IN-27 / 5-IN-9 ANTIPODAL ORBIT OWNERS -> FOURIER CUT
--
-- Serre (1977), finite group representations and orbit-count method.
-- Existing mathematical source/PR ownership:
--   BalancedTernaryAntipodalOrbitExact       strict global sign C2
--   BalancedTernaryAntipodal369OrbitHierarchyExact
--   BalancedTernaryHypercubeAntipodalOrbitCountExact
--   TernaryNineAntipodalD4SeparationExact   5 classes != D4 irreps
--   R2P227729FourierObserverIncidenceExact  true 27 integer modes
--   R2P227729FiniteQuadraticConvolutionExact true 729 ordered pairs
--   Core.IntersectionalNonFactorability     collision/no decoding
--
-- 9 = 1 + 4*2 (5 classes), 27 = 1 + 13*2 (14 classes).
-- A *real-valued* Fourier field may store centre real + 13 conjugate
-- coefficient pairs, i.e. 27 real degrees of freedom. The quotient
-- alone is NOT an arbitrary-complex amplitude codec; orientation
-- remains necessary for reconstructing and convolving input modes.
--
-- This module proves a concrete operator counterexample: even knowing
-- antipodal classes of BOTH ordered inputs cannot determine their true
-- integer sum, or even their three-grid cyclic sum, because the pair
-- (+x,+x) and (-x,+x) have the same pair-of-classes but different sums.
--
-- No GF729, Monster 3B, D4 irrep, NS Clay or Yb clock identification.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Foundations.SSPTritCarrier as SSP
import DASHI.Foundations.BalancedTernaryAntipodalOrbitExact as Orbit
import DASHI.Foundations.BalancedTernaryAntipodal369OrbitHierarchyExact as Hierarchy
import DASHI.Foundations.BalancedTernaryHypercubeAntipodalOrbitCountExact as Generic
import DASHI.Foundations.TernaryNineAntipodalD4SeparationExact as D4Guard
import DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact as M
import DASHI.Physics.Closure.R2P227729FourierObserverIncidenceExact as I
import DASHI.Physics.Closure.R2P227729FiniteQuadraticConvolutionExact as Conv
import DASHI.Core.IndexedRelationalHyperfabricSpineExact as Core
import DASHI.Core.IntersectionalNonFactorability as NF

negateMode : M.ThreeMode → M.ThreeMode
negateMode M.modeMinus = M.modePlus
negateMode M.modeZero = M.modeZero
negateMode M.modePlus = M.modeMinus

negateModeInvolution :
  (mode : M.ThreeMode) → negateMode (negateMode mode) ≡ mode
negateModeInvolution M.modeMinus = refl
negateModeInvolution M.modeZero = refl
negateModeInvolution M.modePlus = refl

negateModeSSPCompatibility :
  (mode : M.ThreeMode) →
  M.modeToBalancedSSP (negateMode mode)
    ≡ Orbit.strictAntipode (M.modeToBalancedSSP mode)
negateModeSSPCompatibility M.modeMinus = refl
negateModeSSPCompatibility M.modeZero = refl
negateModeSSPCompatibility M.modePlus = refl

negateCube : I.ModeCube27 → I.ModeCube27
negateCube (I.modeCube a b c) =
  I.modeCube (negateMode a) (negateMode b) (negateMode c)

negateCubeInvolution :
  (mode : I.ModeCube27) →
  negateCube (negateCube mode) ≡ mode
negateCubeInvolution (I.modeCube a b c)
  rewrite negateModeInvolution a
        | negateModeInvolution b
        | negateModeInvolution c = refl

cubeToAntipodalTriple : I.ModeCube27 → Orbit.TritTriple
cubeToAntipodalTriple (I.modeCube a b c) =
  M.threeAxisBalancedModeCube a b c

negatedCubeMatchesOriginalAntipode :
  (mode : I.ModeCube27) →
  cubeToAntipodalTriple (negateCube mode)
    ≡ Orbit.strictAntipodeTriple (cubeToAntipodalTriple mode)
negatedCubeMatchesOriginalAntipode (I.modeCube a b c)
  rewrite negateModeSSPCompatibility a
        | negateModeSSPCompatibility b
        | negateModeSSPCompatibility c = refl

-- The original 14-element quotient, not a new incompatible carrier.
antipodalClass27 : I.ModeCube27 → Orbit.AntipodalClass27
antipodalClass27 mode =
  Orbit.classifyAntipodal27 (cubeToAntipodalTriple mode)

antipodalClass27Invariant :
  (mode : I.ModeCube27) →
  antipodalClass27 (negateCube mode) ≡ antipodalClass27 mode
antipodalClass27Invariant mode
  rewrite negatedCubeMatchesOriginalAntipode mode =
  Orbit.classifyAntipodal27Invariant (cubeToAntipodalTriple mode)

-- 2D coordinate plane: nine signed modes under the SAME global antipode.
Plane9 : Set
Plane9 = M.ThreeMode × M.ThreeMode

antipodalClass9 : Plane9 → Orbit.AntipodalClass9
antipodalClass9 (a , b) =
  Orbit.classifyAntipodal9 (M.modeToBalancedSSP a) (M.modeToBalancedSSP b)

negatePlane9 : Plane9 → Plane9
negatePlane9 (a , b) = negateMode a , negateMode b

antipodalClass9Invariant :
  (plane : Plane9) →
  antipodalClass9 (negatePlane9 plane) ≡ antipodalClass9 plane
antipodalClass9Invariant (a , b)
  rewrite negateModeSSPCompatibility a
        | negateModeSSPCompatibility b =
  Orbit.antipodal9Invariant (M.modeToBalancedSSP a) (M.modeToBalancedSSP b)

plane9ToCube27 : Plane9 → I.ModeCube27
plane9ToCube27 (a , b) = I.modeCube a b M.modeZero

-- A typed embedding of FIVE plane orbit classes into the pre-existing
-- FOURTEEN cube classes. This is a plane-in-cube rechart, not D4 irreps.
planeOrbitClassToCubeOrbit :
  Orbit.AntipodalClass9 → Orbit.AntipodalClass27
planeOrbitClassToCubeOrbit Orbit.centre9 = Orbit.centre27
planeOrbitClassToCubeOrbit Orbit.firstAxis9 =
  Orbit.firstPositive27 SSP.sspZero SSP.sspZero
planeOrbitClassToCubeOrbit Orbit.secondAxis9 =
  Orbit.secondPositive27 SSP.sspZero
planeOrbitClassToCubeOrbit Orbit.sameSignDiagonal9 =
  Orbit.firstPositive27 SSP.sspPosOne SSP.sspZero
planeOrbitClassToCubeOrbit Orbit.oppositeSignDiagonal9 =
  Orbit.firstPositive27 SSP.sspNegOne SSP.sspZero

planeClassInclusionCommutes :
  (plane : Plane9) →
  antipodalClass27 (plane9ToCube27 plane)
    ≡ planeOrbitClassToCubeOrbit (antipodalClass9 plane)
planeClassInclusionCommutes (M.modeMinus , M.modeMinus) = refl
planeClassInclusionCommutes (M.modeMinus , M.modeZero) = refl
planeClassInclusionCommutes (M.modeMinus , M.modePlus) = refl
planeClassInclusionCommutes (M.modeZero , M.modeMinus) = refl
planeClassInclusionCommutes (M.modeZero , M.modeZero) = refl
planeClassInclusionCommutes (M.modeZero , M.modePlus) = refl
planeClassInclusionCommutes (M.modePlus , M.modeMinus) = refl
planeClassInclusionCommutes (M.modePlus , M.modeZero) = refl
planeClassInclusionCommutes (M.modePlus , M.modePlus) = refl

sourceFiveNineOrbitCount :
  Orbit.antipodalClass9Count ≡ 5
sourceFiveNineOrbitCount = Orbit.antipodalClass9CountIsFive

sourceFourteenTwentySevenOrbitCount :
  Orbit.antipodalClass27Count ≡ 14
sourceFourteenTwentySevenOrbitCount = Orbit.antipodalClass27CountIsFourteen

sourceThirteenNonzeroPairs :
  27 ≡ 1 + 13 * 2
sourceThirteenNonzeroPairs =
  Orbit.ternaryCubeCountDecomposesAsCentrePlusThirteenPairs

sourceFourNonzeroPlanePairs :
  9 ≡ 1 + 4 * 2
sourceFourNonzeroPlanePairs =
  Orbit.nineDecomposesAsCentrePlusFourPairs

sourceAntipodalRankThreePairCount :
  Hierarchy.pairedOrbitCount Hierarchy.rank3 ≡ 13
sourceAntipodalRankThreePairCount = refl

sourceAntipodalSixDimPairCount :
  Generic.antipodalPairCount 6 ≡ 364
sourceAntipodalSixDimPairCount = refl

ordered729PairsSplitAsCentrePlus364Pairs :
  729 ≡ 1 + 364 * 2
ordered729PairsSplitAsCentrePlus364Pairs = refl

-- Original D4 representation guard. Five orbit classes are NOT five
-- D4 irreps, and a nine-dimensional permutation is NOT the J4 restriction.
fiveAntipodalClassesAreNotEstablishedD4Irreps :
  D4Guard.TernaryNineAntipodalD4Boundary.fiveAntipodalOrbitClassesAreFiveD4IrrepSpecies
    D4Guard.canonicalTernaryNineAntipodalD4Boundary ≡ false
fiveAntipodalClassesAreNotEstablishedD4Irreps = refl

------------------------------------------------------------------------
-- High-alpha nonfactorability: quotienting signed Fourier INDEX inputs
-- does not preserve even the quadratic pair sum.
------------------------------------------------------------------------

positiveX : I.ModeCube27
positiveX = I.modeCube M.modePlus M.modeZero M.modeZero

negativeX : I.ModeCube27
negativeX = I.modeCube M.modeMinus M.modeZero M.modeZero

positiveInputPair : I.ModePair729
positiveInputPair = positiveX , positiveX

mixedInputPair : I.ModePair729
mixedInputPair = negativeX , positiveX

pairOfOrbitClasses :
  I.ModePair729 → Orbit.AntipodalClass27 × Orbit.AntipodalClass27
pairOfOrbitClasses (p , q) = antipodalClass27 p , antipodalClass27 q

twoPairsHaveSameAntipodalObservations :
  pairOfOrbitClasses positiveInputPair
    ≡ pairOfOrbitClasses mixedInputPair
twoPairsHaveSameAntipodalObservations = refl

positivePairReallyOutputsPlusTwo :
  Conv.exactPairOutput positiveX positiveX
    ≡ Conv.wideCube M.widePlusTwo M.wideZero M.wideZero
positivePairReallyOutputsPlusTwo = refl

mixedPairReallyOutputsZero :
  Conv.exactPairOutput negativeX positiveX
    ≡ Conv.wideCube M.wideZero M.wideZero M.wideZero
mixedPairReallyOutputsZero = refl

realPairOutputsDiffer :
  Conv.exactPairOutput positiveX positiveX
    ≡ Conv.exactPairOutput negativeX positiveX → ⊥
realPairOutputsDiffer ()

orbitQuotientCannotDetermineIntegerPairOutput :
  Core.ConsumerCollision pairOfOrbitClasses
    (λ pair → Conv.exactPairOutput
      (proj₁ pair) (proj₂ pair))
orbitQuotientCannotDetermineIntegerPairOutput =
  NF.nonFactorabilityWitness
    positiveInputPair mixedInputPair
    twoPairsHaveSameAntipodalObservations
    realPairOutputsDiffer

noIntegerPairOutputFromOnlyOrbitLabels :
  Core.ConsumerSufficient pairOfOrbitClasses
    (λ pair → Conv.exactPairOutput
      (proj₁ pair) (proj₂ pair)) → ⊥
noIntegerPairOutputFromOnlyOrbitLabels =
  Core.collisionRefutesSufficiency
    orbitQuotientCannotDetermineIntegerPairOutput

noRechartOfOnlyOrbitLabelsRecoversIntegerPairOutput :
  ∀ {Chart : Set} →
  (chart : Orbit.AntipodalClass27 × Orbit.AntipodalClass27 → Chart) →
  Core.ConsumerSufficient
    (λ pair → chart (pairOfOrbitClasses pair))
    (λ pair → Conv.exactPairOutput
      (proj₁ pair) (proj₂ pair)) → ⊥
noRechartOfOnlyOrbitLabelsRecoversIntegerPairOutput chart =
  Core.collisionSurvivesRechart chart
    orbitQuotientCannotDetermineIntegerPairOutput


------------------------------------------------------------------------
-- Exact negation covariance of the TRUE integer quadratic Fourier sum.
-- This is the operator-level input for real-field Hermitian coefficients;
-- it does not prove the amplitude-level conjugation sum on its own.
------------------------------------------------------------------------

negateWideAxis : M.FiveMode → M.FiveMode
negateWideAxis M.wideMinusTwo = M.widePlusTwo
negateWideAxis M.wideMinusOne = M.widePlusOne
negateWideAxis M.wideZero = M.wideZero
negateWideAxis M.widePlusOne = M.wideMinusOne
negateWideAxis M.widePlusTwo = M.wideMinusTwo

negateWideInvolution :
  (k : M.FiveMode) → negateWideAxis (negateWideAxis k) ≡ k
negateWideInvolution M.wideMinusTwo = refl
negateWideInvolution M.wideMinusOne = refl
negateWideInvolution M.wideZero = refl
negateWideInvolution M.widePlusOne = refl
negateWideInvolution M.widePlusTwo = refl

trueSignedAxisSumNegatesCovariantly :
  (a b : M.ThreeMode) →
  M.exactQuadraticModeSum (negateMode a) (negateMode b)
    ≡ negateWideAxis (M.exactQuadraticModeSum a b)
trueSignedAxisSumNegatesCovariantly M.modeMinus M.modeMinus = refl
trueSignedAxisSumNegatesCovariantly M.modeMinus M.modeZero = refl
trueSignedAxisSumNegatesCovariantly M.modeMinus M.modePlus = refl
trueSignedAxisSumNegatesCovariantly M.modeZero M.modeMinus = refl
trueSignedAxisSumNegatesCovariantly M.modeZero M.modeZero = refl
trueSignedAxisSumNegatesCovariantly M.modeZero M.modePlus = refl
trueSignedAxisSumNegatesCovariantly M.modePlus M.modeMinus = refl
trueSignedAxisSumNegatesCovariantly M.modePlus M.modeZero = refl
trueSignedAxisSumNegatesCovariantly M.modePlus M.modePlus = refl

negateWideCube : Conv.WideCube125 → Conv.WideCube125
negateWideCube (Conv.wideCube a b c) =
  Conv.wideCube (negateWideAxis a) (negateWideAxis b) (negateWideAxis c)

negateWideCubeInvolution :
  (k : Conv.WideCube125) →
  negateWideCube (negateWideCube k) ≡ k
negateWideCubeInvolution (Conv.wideCube a b c)
  rewrite negateWideInvolution a
        | negateWideInvolution b
        | negateWideInvolution c = refl

trueIntegerQuadraticPairSumNegationEquivariance :
  (p q : I.ModeCube27) →
  Conv.exactPairOutput (negateCube p) (negateCube q)
    ≡ negateWideCube (Conv.exactPairOutput p q)
trueIntegerQuadraticPairSumNegationEquivariance
  (I.modeCube a b c) (I.modeCube d e f)
  rewrite trueSignedAxisSumNegatesCovariantly a d
        | trueSignedAxisSumNegatesCovariantly b e
        | trueSignedAxisSumNegatesCovariantly c f = refl

-- Nonzero wide frequency pairs are 62, with one centre:
-- 125 = 1 + 62×2, corresponding to 63 antipodal output classes.
wideQuadraticOrbitCount : 125 ≡ 1 + 62 * 2
wideQuadraticOrbitCount = refl

-- The simultaneous-input negation action on the 729 pair addresses
-- has one fixed zero/zero pair. This is not pair-swap symmetrisation.
simultaneouslyNegateOrderedPair : I.ModePair729 → I.ModePair729
simultaneouslyNegateOrderedPair (p , q) = negateCube p , negateCube q

simultaneousPairNegationInvolution :
  (pair : I.ModePair729) →
  simultaneouslyNegateOrderedPair (simultaneouslyNegateOrderedPair pair)
    ≡ pair
simultaneousPairNegationInvolution (p , q)
  rewrite negateCubeInvolution p
        | negateCubeInvolution q = refl

orderedPairOutputCovariantUnderSimultaneousNegation :
  (pair : I.ModePair729) →
  let output : I.ModePair729 → Conv.WideCube125
      output (p , q) = Conv.exactPairOutput p q
  in
  output (simultaneouslyNegateOrderedPair pair)
    ≡ negateWideCube (output pair)
orderedPairOutputCovariantUnderSimultaneousNegation (p , q) =
  trueIntegerQuadraticPairSumNegationEquivariance p q
