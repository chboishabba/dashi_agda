module DASHI.Physics.YangMills.BalabanClayT2EightWayFernandezProcacciExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_; NonNegative)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Physics.YangMills.BalabanBoolean4BlockPoincareExact using
  (baseBelowBasePlusRemainder)

------------------------------------------------------------------------
-- Sharper eight-way convergence insurance.
--
-- R. Fernández and A. Procacci,
-- "Cluster expansion for abstract polymer models. New bounds from an old
-- approach",
-- Communications in Mathematical Physics 274 (2007), 123--140.
-- DOI: 10.1007/s00220-007-0279-2
--
-- R. Bissacot, R. Fernández and A. Procacci,
-- "On the convergence of cluster expansions for polymer gases",
-- Journal of Statistical Physics 139 (2010), 598--617.
-- DOI: 10.1007/s10955-010-9956-1
--
-- If the eight alternative rooted extensions form an incompatibility clique,
-- the compatible-subset partition function contains only the empty subset and
-- the eight singleton subsets.  For equal auxiliary weight mu this gives
--
--   phi_FP = 1 + 8 mu.
--
-- At mu = 1/4, activity rho = 1/12 saturates
--
--   rho (1 + 8 mu) = mu.
--
-- Thus the FP clique lane permits 1/12 per extension, while the conservative
-- shell-counting lane still requires 1/16 to obtain the stronger pointwise
-- estimate rootedShell_n <= (1/4) 2^{-n}.  The two statements are deliberately
-- not conflated: FP supplies convergence insurance, not the same shell decay.
------------------------------------------------------------------------

eight quarter oneSixteenth oneTwelfth oneFortyEighth : ℚ
eight = + 8 / 1
quarter = + 1 / 4
oneSixteenth = + 1 / 16
oneTwelfth = + 1 / 12
oneFortyEighth = + 1 / 48

fpCliqueMajorantAtQuarter : ℚ
fpCliqueMajorantAtQuarter = 1ℚ + eight * quarter

fpCliqueMajorantAtQuarterIsThree :
  fpCliqueMajorantAtQuarter ≡ + 3 / 1
fpCliqueMajorantAtQuarterIsThree = ℚRing.solve-∀

oneTwelfthSaturatesCliqueFP :
  oneTwelfth * fpCliqueMajorantAtQuarter ≡ quarter
oneTwelfthSaturatesCliqueFP = ℚRing.solve-∀

oneSixteenthPlusFPSlackIsOneTwelfth :
  oneSixteenth + oneFortyEighth ≡ oneTwelfth
oneSixteenthPlusFPSlackIsOneTwelfth = ℚRing.solve-∀

oneFortyEighthNonnegative : 0ℚ ≤ oneFortyEighth
oneFortyEighthNonnegative =
  let
    instance
      slackNonnegative : NonNegative oneFortyEighth
      slackNonnegative = ℚP.normalize-nonNeg 1 48
  in
  ℚP.nonNegative⁻¹ oneFortyEighth

oneSixteenthBelowOneTwelfth : oneSixteenth ≤ oneTwelfth
oneSixteenthBelowOneTwelfth =
  subst
    (λ upper → oneSixteenth ≤ upper)
    oneSixteenthPlusFPSlackIsOneTwelfth
    (baseBelowBasePlusRemainder
      oneSixteenth oneFortyEighth oneFortyEighthNonnegative)

record EightWayCliqueFPData (Scale Root : Set) : Set₁ where
  field
    extensionActivity : Scale → Root → ℚ

    EightExtensionsFormIncompatibilityClique : Scale → Root → Set
    eightExtensionsFormIncompatibilityClique : ∀ scale root →
      EightExtensionsFormIncompatibilityClique scale root

    reflexive : ∀ value → value ≤ value
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right

    -- The multiplier is the fixed positive value 1 + 8(1/4) = 3.  We do not
    -- assume monotonicity for arbitrary rational multipliers, which would be
    -- false for negative factors.
    multiplyByCliqueMajorantMonotone : ∀ {left right} →
      left ≤ right →
      left * fpCliqueMajorantAtQuarter
      ≤ right * fpCliqueMajorantAtQuarter

    activityBelowOneTwelfth : ∀ scale root →
      extensionActivity scale root ≤ oneTwelfth

open EightWayCliqueFPData public

record ExtensionCliqueGeometry (Scale Root Extension Direction Polymer : Set) : Set₁ where
  field
    validExtensionCount : Root → ℚ
    polymerIncompatibilitySymmetric : Polymer → Polymer → Set
    polymerSelfIncompatibleForNonemptySupport : Polymer → Set
    extensionPolymerNonempty : Extension → Set
    extensionPreservesRootWitness : Root → Extension → Set
    distinctDirectionsGiveDistinctExtensions : Direction → Direction → Root → Set
    distinctExtensionsShareIncompatibilityCore : Extension → Extension → Set
    sharedCoreImpliesIncompatible : Extension → Extension → Set
    distinctRootedExtensionsIncompatible : Extension → Extension → Set
    
    neighbourhoodPartitionFunction : Root → ℚ → ℚ
    extensionCliquePartitionFunctionExact : ∀ root μ →
      neighbourhoodPartitionFunction root μ ≡ 1ℚ + validExtensionCount root * μ

    allEightExtensionsValid : ∀ root → validExtensionCount root ≡ eight

open ExtensionCliqueGeometry public

cliquePartitionFunctionAtEight :
  ∀ {Scale Root Extension Direction Polymer} →
  (geom : ExtensionCliqueGeometry Scale Root Extension Direction Polymer) →
  (root : Root) (μ : ℚ) →
  neighbourhoodPartitionFunction geom root μ ≡ 1ℚ + eight * μ
cliquePartitionFunctionAtEight geom root μ =
  subst
    (λ count → neighbourhoodPartitionFunction geom root μ ≡ 1ℚ + count * μ)
    (allEightExtensionsValid geom root)
    (extensionCliquePartitionFunctionExact geom root μ)

activityTimesCliqueMajorantBelowQuarter :
  ∀ {Scale Root}
    (dataSet : EightWayCliqueFPData Scale Root)
    scale root →
  extensionActivity dataSet scale root * fpCliqueMajorantAtQuarter
  ≤ quarter
activityTimesCliqueMajorantBelowQuarter dataSet scale root =
  transitive dataSet
    (multiplyByCliqueMajorantMonotone dataSet
      (activityBelowOneTwelfth dataSet scale root))
    (subst
      (λ upper → oneTwelfth * fpCliqueMajorantAtQuarter ≤ upper)
      oneTwelfthSaturatesCliqueFP
      (reflexive dataSet
        (oneTwelfth * fpCliqueMajorantAtQuarter)))

record ConservativeActivityImpliesFPSlack (Scale Root : Set) : Set₁ where
  field
    activity : Scale → Root → ℚ
    transitive : ∀ {left middle right} →
      left ≤ middle → middle ≤ right → left ≤ right
    activityBelowOneSixteenth : ∀ scale root →
      activity scale root ≤ oneSixteenth

open ConservativeActivityImpliesFPSlack public

conservativeActivityBelowFPThreshold :
  ∀ {Scale Root}
    (dataSet : ConservativeActivityImpliesFPSlack Scale Root)
    scale root →
  activity dataSet scale root ≤ oneTwelfth
conservativeActivityBelowFPThreshold dataSet scale root =
  transitive dataSet
    (activityBelowOneSixteenth dataSet scale root)
    oneSixteenthBelowOneTwelfth

eightWayFPCliqueArithmeticLevel : ProofLevel
eightWayFPCliqueArithmeticLevel = computed

oneSixteenthHasOneFortyEighthFPSlackLevel : ProofLevel
oneSixteenthHasOneFortyEighthFPSlackLevel = machineChecked

activityTimesFPCliqueMajorantLevel : ProofLevel
activityTimesFPCliqueMajorantLevel = machineChecked

-- The literal Wilson application must prove that the eight alternatives used at
-- each rooted extension really form the required incompatibility clique.  If
-- that geometry fails, the 1/12 threshold is unavailable and the 1/16 KP/shell
-- lane remains the valid conservative certificate.
physicalEightExtensionCliqueIdentificationLevel : ProofLevel
physicalEightExtensionCliqueIdentificationLevel = conditional

