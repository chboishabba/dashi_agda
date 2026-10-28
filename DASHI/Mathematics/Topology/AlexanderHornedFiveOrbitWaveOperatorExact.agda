module DASHI.Mathematics.Topology.AlexanderHornedFiveOrbitWaveOperatorExact where

------------------------------------------------------------------------
-- Cross-domain wave consumer: five orbit-dependent wave operators
-- on the native 27-address C3 x Trit^2 carrier.
--
-- REUSE FIRST:
-- - #1244 AlexanderHornedDepthTwoFiveOrbitFibreExact: the five
--   sector/sign orbit classifier and proof of orbitReflect.
-- - Existing DASHI.Physics.ShiftDiscreteWaveStep: DiscreteWave.
-- - #1405 GoodmanSonicWaveC3EquivarianceExact: original T15
--   homogeneous C3 and T16 HETEROGENEOUS operator covariance,
--   still on an UNMERGED branch. We do not copy or import it here.
--
-- NEW: for any five arbitrary wave operators (one per orbit),
-- pointwise evolution on 27 cells COMMUTES WITH BOTH original
-- sector rotation and balanced-sign reflection. More generally,
-- transporting the operators themselves yields heterogeneous
-- covariance for any (not necessarily invariant) operator field.
--
-- NO claims about physical acoustics, actual embedded wild
-- satellite, eigenmodes/RH, wave-energy conservation, or
-- Ibrahim Monster 3B same-object representation. Source-written,
-- Agda kernel proof receipt still outstanding.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_,_)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Algebra.BalancedTernary as Trit
import DASHI.Core.FiniteC3OrbitStabilizerExact as C3
import DASHI.Physics.ShiftDiscreteWaveStep as Wave
import DASHI.Mathematics.Topology.AlexanderHornedNativeBalancedTernaryEndTowerExact as End
import DASHI.Mathematics.Topology.AlexanderHornedDepthTwoFiveOrbitFibreExact as Five

Address : Set
Address = End.BalancedLevel 2

WaveField : Set
WaveField = Address → Wave.DiscreteWave

WaveOperator : Set
WaveOperator = Wave.DiscreteWave → Wave.DiscreteWave

OperatorField : Set
OperatorField = Address → WaveOperator

FiveWaveField : Set
FiveWaveField = Five.FiveOrbit → Wave.DiscreteWave

FiveOperatorField : Set
FiveOperatorField = Five.FiveOrbit → WaveOperator

orbitOfAddress : Address → Five.FiveOrbit
orbitOfAddress (c , (a ∷ b ∷ [])) = Five.orbit a b

inflateWave : FiveWaveField → WaveField
inflateWave f x = f (orbitOfAddress x)

inflateOperator : FiveOperatorField → OperatorField
inflateOperator op x = op (orbitOfAddress x)

evolve : OperatorField → WaveField → WaveField
evolve op f x = op x (f x)

evolveFive : FiveOperatorField → FiveWaveField → FiveWaveField
evolveFive op f o = op o (f o)

-- This is a genuine orbit-domain -> 27-domain operator square,
-- with no assumption that different orbit operators are equal.
inflateEvolutionSquare : ∀ op f x →
  evolve (inflateOperator op) (inflateWave f) x ≡
  inflateWave (evolveFive op f) x
inflateEvolutionSquare op f x = refl

-- External C3 acts on sector only; orbit labels ignore sector.
orbitSectorInvariant : ∀ x →
  orbitOfAddress (End.rotateBalancedLevel 2 x) ≡ orbitOfAddress x
orbitSectorInvariant (c , (a ∷ b ∷ [])) = refl

-- Simultaneous signed reversal preserves all FIVE orbits.
orbitSignInvariant : ∀ x →
  orbitOfAddress (End.reflectBalancedLevel 2 x) ≡ orbitOfAddress x
orbitSignInvariant (c , (a ∷ b ∷ [])) = Five.orbitReflect a b

waveSectorInvariant : ∀ f x →
  inflateWave f (End.rotateBalancedLevel 2 x) ≡ inflateWave f x
waveSectorInvariant f x = cong f (orbitSectorInvariant x)

waveSignInvariant : ∀ f x →
  inflateWave f (End.reflectBalancedLevel 2 x) ≡ inflateWave f x
waveSignInvariant f x = cong f (orbitSignInvariant x)

operatorSectorInvariant : ∀ op x →
  inflateOperator op (End.rotateBalancedLevel 2 x) ≡
  inflateOperator op x
operatorSectorInvariant op x = cong op (orbitSectorInvariant x)

operatorSignInvariant : ∀ op x →
  inflateOperator op (End.reflectBalancedLevel 2 x) ≡
  inflateOperator op x
operatorSignInvariant op x = cong op (orbitSignInvariant x)

-- Heterogeneous FIVE-orbit operators are allowed; both phase and
-- operator fields are H-invariant after inflation.
waveEvolutionSectorInvariant : ∀ op f x →
  evolve (inflateOperator op) (inflateWave f)
    (End.rotateBalancedLevel 2 x) ≡
  evolve (inflateOperator op) (inflateWave f) x
waveEvolutionSectorInvariant op f x =
  cong (λ o → op o (f o)) (orbitSectorInvariant x)

waveEvolutionSignInvariant : ∀ op f x →
  evolve (inflateOperator op) (inflateWave f)
    (End.reflectBalancedLevel 2 x) ≡
  evolve (inflateOperator op) (inflateWave f) x
waveEvolutionSignInvariant op f x =
  cong (λ o → op o (f o)) (orbitSignInvariant x)

-- T16's general theorem in #1405 is already owned there.
-- The following general operator/field transport square is
-- merely the new ADDRESS-indexed analogue, not a second theorem
-- about the particular finite wave implementation.
relabelField : (r : Address → Address) → WaveField → WaveField
relabelField r f x = f (r x)

relabelOperator : (r : Address → Address) → OperatorField → OperatorField
relabelOperator r op x = op (r x)

operatorRelabelNaturality : ∀ r op f x →
  evolve (relabelOperator r op) (relabelField r f) x ≡
  relabelField r (evolve op f) x
operatorRelabelNaturality r op f x = refl

-- The existing 3-phase local C3 fields belong to a separate
-- abelian action object. This wave bridge changes the *value type*
-- and does not postulate an intertwinining phase->pressure map.
