module DASHI.Physics.YangMills.BalabanP33PlaquetteLinearCurlIdentificationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks".
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Balaban,
-- "Spaces of Regular Gauge Field Configurations on a Lattice and Gauge
-- Fixing Conditions".
-- DOI: 10.1007/BF01466594.
--
-- Tadeusz Balaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories".
-- DOI: 10.1007/BF01229381.
--
-- DASHI CONTRIBUTION
--
-- Identify the scalar first-order plaquette obstruction with a genuine
-- discrete curl.  For the oriented boundary values
--
--   A_mu(x), A_nu(x+mu), -A_mu(x+nu), -A_nu(x),
--
-- the linear Wilson term is exactly
--
--   [A_nu(x+mu)-A_nu(x)] - [A_mu(x+nu)-A_mu(x)].
--
-- Therefore four independent link-radius bounds miss the relevant correlated
-- quantity: the selected-background proof should bound the lattice curvature
-- itself.  We also prove that an exact scalar lattice gradient has zero
-- plaquette curl, the discrete pure-gauge cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _-_; -_; _≤_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (subst; sym)

record ScalarPlaquetteField : Set where
  constructor scalarPlaquetteField
  field
    muAtBase : ℚ
    muAtNuShift : ℚ
    nuAtBase : ℚ
    nuAtMuShift : ℚ

open ScalarPlaquetteField public

orientedBoundaryLinear : ScalarPlaquetteField → ℚ
orientedBoundaryLinear field =
  muAtBase field
  + nuAtMuShift field
  - muAtNuShift field
  - nuAtBase field

forwardMuOfNu : ScalarPlaquetteField → ℚ
forwardMuOfNu field = nuAtMuShift field - nuAtBase field

forwardNuOfMu : ScalarPlaquetteField → ℚ
forwardNuOfMu field = muAtNuShift field - muAtBase field

discreteCurl : ScalarPlaquetteField → ℚ
discreteCurl field = forwardMuOfNu field - forwardNuOfMu field

plaquetteLinearEqualsDiscreteCurl :
  (field : ScalarPlaquetteField) →
  orientedBoundaryLinear field ≡ discreteCurl field
plaquetteLinearEqualsDiscreteCurl
    (scalarPlaquetteField mu0 muNu nu0 nuMu) =
  solve (mu0 ∷ muNu ∷ nu0 ∷ nuMu ∷ [])

curvatureLowerTransfersToPlaquetteLinear :
  (field : ScalarPlaquetteField) →
  (budget : ℚ) →
  - budget ≤ discreteCurl field →
  - budget ≤ orientedBoundaryLinear field
curvatureLowerTransfersToPlaquetteLinear field budget curvatureLower =
  subst
    (λ selected → - budget ≤ selected)
    (sym (plaquetteLinearEqualsDiscreteCurl field))
    curvatureLower

record ScalarVertexPotential : Set where
  constructor scalarVertexPotential
  field
    potential00 : ℚ
    potentialMu : ℚ
    potentialNu : ℚ
    potentialMuNu : ℚ

open ScalarVertexPotential public

gradientPlaquetteField : ScalarVertexPotential → ScalarPlaquetteField
gradientPlaquetteField potential =
  scalarPlaquetteField
    (potentialMu potential - potential00 potential)
    (potentialMuNu potential - potentialNu potential)
    (potentialNu potential - potential00 potential)
    (potentialMuNu potential - potentialMu potential)

exactGradientHasZeroDiscreteCurl :
  (potential : ScalarVertexPotential) →
  discreteCurl (gradientPlaquetteField potential) ≡ 0ℚ
exactGradientHasZeroDiscreteCurl
    (scalarVertexPotential value00 valueMu valueNu valueMuNu) =
  solve (value00 ∷ valueMu ∷ valueNu ∷ valueMuNu ∷ [])

exactGradientHasZeroPlaquetteLinearTerm :
  (potential : ScalarVertexPotential) →
  orientedBoundaryLinear (gradientPlaquetteField potential) ≡ 0ℚ
exactGradientHasZeroPlaquetteLinearTerm
    (scalarVertexPotential value00 valueMu valueNu valueMuNu) =
  solve (value00 ∷ valueMu ∷ valueNu ∷ valueMuNu ∷ [])

record PhysicalSU2CurlControlTarget : Set₁ where
  field
    Background Plaquette : Set
    selectedBackground : Background
    linearizedPlaquetteCurvature : Background → Plaquette → Set
    regularityControlsCurvature :
      (plaquette : Plaquette) →
      linearizedPlaquetteCurvature selectedBackground plaquette

-- The scalar discrete-Stokes identity is fully proved.  The physical target is
-- deliberately uninhabited until the actual SU(2) logarithms, adjoint transports
-- and Bałaban regularity estimates supply the noncommutative curvature bound.
