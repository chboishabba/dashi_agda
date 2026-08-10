module DASHI.Physics.YangMills.BalabanSelectedGaugeStabilizerStratificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions", Communications in Mathematical Physics 99 (1985),
-- 75--102. DOI: 10.1007/BF01466594.
--
-- Brian C. Hall,
-- "Lie Groups, Lie Algebras, and Representations: An Elementary
-- Introduction", second edition, Springer, 2015.
-- DOI: 10.1007/978-3-319-13467-3.
--
-- DASHI CONTRIBUTION
--
-- Turn the Round-42 holonomy no-go into an explicit stabilizer-stratification
-- theorem.  The intrinsic infinitesimal redundancy datum is the fixed set of
-- the adjoint holonomy action.  At the flat identity holonomy all three pure
-- quaternion Lie basis directions are fixed.  At the literal rational
-- near-identity noncentral holonomy already used by the selected-radius guard,
-- the rotation-axis direction survives while both transverse directions move.
--
-- Thus the flat three-dimensional constant stabilizer is not a background-
-- independent product fibre.  This is a concrete orbit/stabilizer statement,
-- not a rank-continuity inference and not a supplied abstract bundle.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base as ℚ using (0ℚ; _<_; -_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33QuaternionAdjointPerturbationExact as Adjoint
import DASHI.Physics.YangMills.BalabanSelectedGaugeRedundancyHolonomyGuardExact as Guard

AdjointFixed : Q.RationalQuaternion → Q.RationalQuaternion → Set
AdjointFixed unit direction =
  Adjoint.adjointTransport unit direction ≡ direction

xDirection yDirection zDirection : Q.RationalQuaternion
xDirection = Q.quat 0ℚ (+ 1 / 1) 0ℚ 0ℚ
yDirection = Guard.yDirection
zDirection = Q.quat 0ℚ 0ℚ 0ℚ (+ 1 / 1)

identityAdjointFixes : ∀ direction → AdjointFixed Q.oneQ direction
identityAdjointFixes (Q.quat x0 x1 x2 x3) =
  Q.quaternionExt
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)
    (ℚRing.solve-∀ x0 x1 x2 x3)

flatIdentityFixesX : AdjointFixed Q.oneQ xDirection
flatIdentityFixesX = identityAdjointFixes xDirection

flatIdentityFixesY : AdjointFixed Q.oneQ yDirection
flatIdentityFixesY = identityAdjointFixes yDirection

flatIdentityFixesZ : AdjointFixed Q.oneQ zDirection
flatIdentityFixesZ = identityAdjointFixes zDirection

nearIdentityHolonomyFixesX :
  AdjointFixed Guard.nearIdentityUnit xDirection
nearIdentityHolonomyFixesX =
  Q.quaternionExt
    (ℚRing.solve [])
    (ℚRing.solve [])
    (ℚRing.solve [])
    (ℚRing.solve [])

nearIdentityHolonomyMovesY :
  ¬ AdjointFixed Guard.nearIdentityUnit yDirection
nearIdentityHolonomyMovesY =
  Guard.flatConstantRedundancyNotAutomaticallyTransported

rotatedZ : Q.RationalQuaternion
rotatedZ = Adjoint.adjointTransport Guard.nearIdentityUnit zDirection

rotatedZQ2IsNegativeRotatedYQ3 :
  Q.q2 rotatedZ ≡ - Q.q3 Guard.rotatedY
rotatedZQ2IsNegativeRotatedYQ3 = ℚRing.solve []

rotatedZQ2Negative : Q.q2 rotatedZ < 0ℚ
rotatedZQ2Negative =
  subst
    (λ selected → selected < 0ℚ)
    (sym rotatedZQ2IsNegativeRotatedYQ3)
    (ℚP.neg-mono-< Guard.rotatedYQ3Positive)

nearIdentityHolonomyMovesZ :
  ¬ AdjointFixed Guard.nearIdentityUnit zDirection
nearIdentityHolonomyMovesZ equality =
  let
    q2Zero : Q.q2 rotatedZ ≡ 0ℚ
    q2Zero = trans (cong Q.q2 equality) (ℚRing.solve [])
  in
  ℚP.<-irrefl 0ℚ
    (subst (λ selected → selected < 0ℚ) q2Zero rotatedZQ2Negative)

record StabilizerStratumWitness : Set where
  constructor stabilizerStratumWitness
  field
    direction : Q.RationalQuaternion
    flatFixed : AdjointFixed Q.oneQ direction
    nearbyNotFixed : ¬ AdjointFixed Guard.nearIdentityUnit direction

open StabilizerStratumWitness public

selectedBackgroundStabilizerNeedNotEqualFlat : StabilizerStratumWitness
selectedBackgroundStabilizerNeedNotEqualFlat =
  stabilizerStratumWitness yDirection flatIdentityFixesY nearIdentityHolonomyMovesY

record NearIdentityStabilizerProfile : Set where
  constructor nearIdentityStabilizerProfile
  field
    axisSurvives : AdjointFixed Guard.nearIdentityUnit xDirection
    firstTransverseBreaks : ¬ AdjointFixed Guard.nearIdentityUnit yDirection
    secondTransverseBreaks : ¬ AdjointFixed Guard.nearIdentityUnit zDirection

open NearIdentityStabilizerProfile public

nearIdentityStabilizerProfileExact : NearIdentityStabilizerProfile
nearIdentityStabilizerProfileExact =
  nearIdentityStabilizerProfile
    nearIdentityHolonomyFixesX
    nearIdentityHolonomyMovesY
    nearIdentityHolonomyMovesZ

selectedGaugeStabilizerStratificationLevel : ProofLevel
selectedGaugeStabilizerStratificationLevel = machineChecked

selectedGaugeFlatProductFibreNoGoLevel : ProofLevel
selectedGaugeFlatProductFibreNoGoLevel = machineChecked
