module DASHI.Physics.YangMills.BalabanSelectedBackgroundCovariantCurlInstantiationExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "The Variational Problem and Background Fields in Renormalization Group
-- Method for Lattice Gauge Theories",
-- Communications in Mathematical Physics 102 (1985), 605--636.
-- DOI: 10.1007/BF01229381.
--
-- Tadeusz Bałaban,
-- "Propagators for Lattice Gauge Theories in a Background Field",
-- Communications in Mathematical Physics 99 (1985), 389--434.
-- DOI: 10.1007/BF01240355.
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- DASHI CONTRIBUTION
--
-- Transport the exact plaquette first-variation/covariant-curl theorem onto
-- the same selected variational background and the same perturbation object
-- already consumed by the terminal Hessian theorem.  This prevents a later
-- curvature estimate from proving a theorem about one background while the
-- coercivity endpoint uses another.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational
import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Selected
import DASHI.Physics.YangMills.BalabanSelectedBackgroundPhysicalRadiusInstantiationExact as Instantiation
import DASHI.Physics.YangMills.BalabanP33SelectedBackgroundFiniteCoercivityExact as Coercivity
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionWilsonSecondVariationExact as Q
import DASHI.Physics.YangMills.BalabanP33PhysicalRationalWilsonPlaquetteJetExact as Physical
import DASHI.Physics.YangMills.BalabanP33PhysicalPlaquetteFirstVariationExact as First
import DASHI.Physics.YangMills.BalabanP33PhysicalCovariantPlaquetteCurlExact as Curl
import DASHI.Physics.YangMills.BalabanP33CovariantCurlDefectFactorizationExact as Defect

selectedVariationalFirstVariationIsCovariantCurl :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h plaquette →
  First.plaquetteFirstVariation
      (Coercivity.backgroundOf (Instantiation.model family) h)
      (Coercivity.physicalFieldOf (Instantiation.model family) h)
      plaquette
    Q.*q Curl.physicalPlaquetteRightInverse
      (Coercivity.backgroundOf (Instantiation.model family) h)
      plaquette
  ≡ Curl.physicalCovariantPlaquetteCurl
      (Coercivity.backgroundOf (Instantiation.model family) h)
      (Coercivity.physicalFieldOf (Instantiation.model family) h)
      plaquette
selectedVariationalFirstVariationIsCovariantCurl family h plaquette =
  Curl.physicalPlaquetteFirstVariationIsCovariantCurl
    (Coercivity.backgroundOf (Instantiation.model family) h)
    (Coercivity.physicalFieldOf (Instantiation.model family) h)
    plaquette

selectedBackgroundFirstVariationIsCovariantCurl :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h plaquette →
  First.plaquetteFirstVariation
      (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
      (Coercivity.physicalFieldOf (Instantiation.model family) h)
      plaquette
    Q.*q Curl.physicalPlaquetteRightInverse
      (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
      plaquette
  ≡ Curl.physicalCovariantPlaquetteCurl
      (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
      (Coercivity.physicalFieldOf (Instantiation.model family) h)
      plaquette
selectedBackgroundFirstVariationIsCovariantCurl
    {inputs = inputs} {coarse} {small} family h plaquette =
  subst
    (λ background →
      First.plaquetteFirstVariation background
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
          plaquette
        Q.*q Curl.physicalPlaquetteRightInverse background plaquette
      ≡ Curl.physicalCovariantPlaquetteCurl background
          (Coercivity.physicalFieldOf (Instantiation.model family) h)
          plaquette)
    (Instantiation.backgroundMatchesSelected family h)
    (selectedVariationalFirstVariationIsCovariantCurl family h plaquette)

selectedBackgroundCovariantCurlDefectFactorization :
  ∀ {CoarseField Lie Perturbation ConstraintIndex}
    {inputs : Instantiation.SelectedPhysicalBackgroundInstantiation
      CoarseField Lie}
    {coarse}
    {small : Variational.CoarseSmallField
      (Selected.variational (Instantiation.bridge inputs)) coarse}
    (family : Instantiation.SelectedVariationalPerturbationFamily
      {Perturbation = Perturbation}
      {ConstraintIndex = ConstraintIndex}
      inputs coarse small)
    h plaquette →
  Defect.physicalCovariantCurlDefect
      (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
      (Coercivity.physicalFieldOf (Instantiation.model family) h)
      plaquette
  ≡ Defect.factorizedAdjointDefectCurlSum
      (Curl.physicalFactorA
        (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
        plaquette)
      (Curl.physicalFactorB
        (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
        plaquette)
      (Curl.physicalPositiveFactorC
        (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
        plaquette)
      (Curl.physicalInsertion0
        (Coercivity.physicalFieldOf (Instantiation.model family) h) plaquette)
      (Curl.physicalInsertion1
        (Coercivity.physicalFieldOf (Instantiation.model family) h) plaquette)
      (Curl.physicalInsertion2
        (Coercivity.physicalFieldOf (Instantiation.model family) h) plaquette)
      (Curl.physicalInsertion3
        (Coercivity.physicalFieldOf (Instantiation.model family) h) plaquette)
selectedBackgroundCovariantCurlDefectFactorization
    {inputs = inputs} {coarse} {small} family h plaquette =
  Defect.physicalCovariantCurlDefectFactorizationExact
    (Selected.selectedBackground (Instantiation.bridge inputs) coarse small)
    (Coercivity.physicalFieldOf (Instantiation.model family) h)
    plaquette

selectedBackgroundCovariantCurlInstantiationLevel : ProofLevel
selectedBackgroundCovariantCurlInstantiationLevel = machineChecked

selectedBackgroundCurvatureLowerProducerLevel : ProofLevel
selectedBackgroundCurvatureLowerProducerLevel = conditional
