module DASHI.Physics.Closure.NSTriadKNPhysicalTriadFrontierProgram where

------------------------------------------------------------------------
-- Physical-first Stage-3 frontier aggregate.
--
-- Machine-constructed or exactly reduced here:
--   * literal cutoff-cube resonant-triad enumeration;
--   * executable, sound and complete output-indexed physical fibres;
--   * exact swap, reality and three-leg energy-orbit constructions;
--   * enumeration closure under swap and conjugation up to lattice equality;
--   * exact max-norm triangle and reverse-triangle geometry;
--   * literal ceil-log dyadic shell function and explicit constants
--       Csep = 3, Cout = 2, Cin = 2;
--   * proved ceil-log upper/lower shell boundaries;
--   * proved factor-two norm comparison implies shell distance at most one;
--   * proved low-high, high-low and high-high-to-low consequences, each with
--     the sharper distance-one bound and hence the selected distance-two bound;
--   * the complex-number and complex-three-vector algebra over an explicit
--     real-field law package;
--   * bilinear and Hermitian products, conjugation, integer wavevectors and
--     the literal Leray formula;
--   * instantiation of the exact signed velocity-form coefficient on C^3;
--   * exact resonant null identities u_p·q = u_p·k and u_q·p = u_q·k;
--   * the concrete C^3 bridge for those null identities;
--   * reduction of the phase formula to sesquilinear scalar algebra;
--   * exact output-indexed projected Galerkin sums and factor/orbit audits;
--   * executable coarse FT/transition/adversarial diagnostics;
--   * a quantitative refinement carrier recording scale, angle,
--     polarisation, cancellation orbit and multiplicity gains;
--   * validated sparse codes and a falsifiable legacy-coordinate audit;
--   * constructive assembly of concrete class estimates into one error bound;
--   * positive-majorant, signed-block and modified-energy uniform-gap routes;
--   * composition of a strict gap and global scalar comparison into an
--     arbitrary-data uniform a-priori estimate;
--   * the Fourier diagonal-subsequence/tail route to the global limit;
--   * exact derivation of the periodic Clay endpoint from any completed
--     Galerkin compactness/smoothness/continuation package.
--
-- Remaining mathematical leaves are deliberately local rather than hidden in
-- an authority record:
--   * a concrete ordered/square-root real-field instance and normalised frame;
--   * scalar/vector distributivity instances for the phase and null bridges;
--   * the signed three-leg cancellation algebra after Leray removal;
--   * physical-space/Fourier projected-equation equivalence;
--   * concrete cutoff-independent FT/transition/adversarial constants;
--   * a strict numerical comparison with the dissipative base constant;
--   * a global scalar comparison ruling out finite-time blow-up;
--   * compactness, nonlinear limit passage, bootstrap and continuation
--     instantiated for the official periodic problem.
------------------------------------------------------------------------

open import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration public
open import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber public
open import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry public
open import DASHI.Physics.Closure.NSTriadKNPhysicalSymmetryEnumerationClosure public
open import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction public
open import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle public
open import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants public
open import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds public
open import DASHI.Physics.Closure.NSTriadKNShellFactorTwo public
open import DASHI.Physics.Closure.NSTriadKNLiteralDyadicConsequencesClosed public
open import DASHI.Physics.Closure.NSTriadKNPhysicalScaleTrichotomy public
open import DASHI.Physics.Closure.NSTriadKNPhysicalStage3Allocation public
open import DASHI.Physics.Closure.NSTriadKNPhysicalScaleStage3Compatibility public
open import DASHI.Physics.Closure.NSTriadKNConcreteCoarseStage3Geometry public

open import DASHI.Physics.Closure.NSTriadKNExactSignedGalerkinCoefficient public
open import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier public
open import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit public
open import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit public
open import DASHI.Physics.Closure.NSTriadKNPositivePartCancellationNoGo public
open import DASHI.Physics.Closure.NSTriadKNResonantNullGain public
open import DASHI.Physics.Closure.NSTriadKNComplex3NullGainBridge public
open import DASHI.Physics.Closure.NSTriadKNPhaseFactorizationReduction public

open import DASHI.Physics.Closure.NSTriadKNCoarseGainDiagnostics public
open import DASHI.Physics.Closure.NSTriadKNRefinedQuantitativeClassification public

open import DASHI.Physics.Closure.NSTriadKNPhysicalClassEncoding public
open import DASHI.Physics.Closure.NSTriadKNExactCoefficientToPhysicalWeight public
open import DASHI.Physics.Closure.NSTriadKNValidatedPhysicalClassCode public
open import DASHI.Physics.Closure.NSTriadKNValidatedPhysicalFiberImage public
open import DASHI.Physics.Closure.NSTriadKNLegacyCoordinateInterpretationAudit public

open import DASHI.Physics.Closure.NSTriadKNPhysicalClassWeightEnvelopes public
open import DASHI.Physics.Closure.NSTriadKNClasswiseSignedEnvelopeAssembly public
open import DASHI.Physics.Closure.NSTriadKNCutoffUniformClasswiseEstimateProgram public
open import DASHI.Physics.Closure.NSTriadKNClasswiseAnalyticCutset public
open import DASHI.Physics.Closure.NSTriadKNExactPhysicalKernelIdentification public

open import DASHI.Physics.Closure.NSTriadKNPhysicalSpectralFrontier public
open import DASHI.Physics.Closure.NSTriadKNFiniteSpectralDoesNotImplyUniform public
open import DASHI.Physics.Closure.NSTriadKNSignedUniformGapProgram public

open import DASHI.Physics.Closure.NSTriadKNArbitraryDataAprioriProgram public
open import DASHI.Physics.Closure.NSTriadKNSignedGapAprioriComposition public
open import DASHI.Physics.Closure.NSTriadKNFourierLimitCompletionComposition public
open import DASHI.Physics.Closure.NSTriadKNGalerkinGlobalRegularityCompletion public
open import DASHI.Physics.Closure.NSTriadKNGalerkinCompletionEndpoint public
