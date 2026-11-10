# Original TSVF/OS shifted-resolvent and strong spectral-calculus maximum cut — 2026-11-10

## Provenance and source ownership
Stacked on #1492, itself stacked on #1460. Modify the ORIGINAL
\`DASHI/Physics/Foundations/TSVFOSRealTimeDifferenceQuotientGeneratorWeldExact.agda\`:
existing source: OriginalTSVFToOSClock, its same J/decode, original OS.hamiltonian reconstruction,
RealTimeDerivativeBridge, PhysicalHbarEnergyConversion,
OriginalIsometricStrongLimitSource, originalMatchedPhysicalEnergyGraphsBidi,
OriginalInvariantPhysicalEnergyCore and originalSelectedScalarEigenmodesBidi.
This is **not** a second physical Hilbert/Hamiltonian.

## New derived source-native mathematical results
- \`OriginalObserverAffineShiftEquation\`, \`OriginalOSAffineShiftEquation\`: original-domain equations (H-s I)x=y with original RealStep scalar action.
- \`originalSelectedAffineShiftIntertwines\`: derivation via original complex-energy H intertwiner, linearSubtract and linearScale. No new intertwiner axiom.
- \`originalSelectedAffineShiftGraphsBidi\`: both directions, reverse using the ORIGINAL decode and physical-domain metric producer.
- \`OriginalOSSelectedShiftInverse\`: source-specific nonresonant OS shift solver, right equation, domain, and explicit injectivity. This is a required independent source, not a constructed inverse.
- \`originalOSShiftInverseLeft\`: derives the left-inverse equation from the right equation and source injectivity.
- \`originalSelectedObserverShiftInverse\`: the observer inverse is derived from the chosen OS solution through original decode.
- \`originalSelectedObserverShiftInverseSolves\`: proves observer right equation, not merely a new name for OS inverse.
- \`originalObserverShiftSolutionsUnique\`, \`originalSelectedObserverShiftInverseLeft\`: uniqueness and full inverse-on-domain, reflecting the OS uniqueness through J.
- \`OriginalEnergyExpression\`: typed finite expression grammar (state, selected original H, original subtraction and scalar action).
- \`originalExpressionDomain\`: source-required domain invariance for each expression.
- \`originalEnergyExpressionIntertwines\`: structural induction, exact original J transport for every expression.
- \`originalSelectedStrongFunctionalLimitIntertwines\`: derives equality of any selected strong operator limit whose *same expression sequence* is actually convergent on both original source carriers; no direct f(H) equality assumed.
- \`originalSelectedStrongLimitCorrelationTransport\`: a physically selected correlation pairing transported through that strong functional limit.

These are proposed Agda proofs committed as source. **No Agda executable or Nix toolchain was present locally; kernel acceptance is pending.** A source-typed theorem with uninhabited physical records does not make experimental physics true.

## What the full mathematical spectral theorem would provide
If the ORIGINAL observer and OS records are inhabited by actual complex Hilbert spaces,
J is a surjective *unitary*, H_obs and H_OS are self-adjoint with matched domains,
and J H_obs = H_OS J on the full domains, then standard spectral theory proves

- J (H_obs-zI)^{-1} = (H_OS-zI)^{-1} J for z outside the real spectra.
- J E_obs(B) = E_OS(B) J for all Borel real energy sets B.
- J f(H_obs) = f(H_OS) J for bounded Borel f; for unbounded f, matched domains.
- In particular, for H≥0, J exp(-t H_obs)= exp(-t H_OS) J for t≥0.
- If exp(-tH) is trace-class for t>0, the *full* heat trace is invariant under unitary equivalence, and sector traces need also be symmetry-projection compatible.
- Spectral zeta and Mellin representation additionally need positive spectrum/zero-mode treatment, convergence or analytic continuation, and a specified normalisation.

These are well-known spectral theorem consequences. The committed Agda extension derives the affine shift and approximation-level transport, **not** the full theorem above for independently constructed physical operators. In particular, RealStep is not a complex off-real z, and no Borel functional-calculus owner is inhabited here.

## Real-world observable plan: falsifiability
1. **Liquid helium-4**: choose one measured interatomic Hamiltonian, compare dynamic structure factor S(q,ω), phonon-maxon-roton dispersion, temperature/pressure dependence and multiphonon thresholds against inelastic-neutron datasets. Sources: Godfrin et al., Phys Rev B 97 (2018) 184520; Beauvois et al., Phys Rev B 94 (2016) 024504. Physical Hamiltonian remains OPEN.
2. **Ultracold BEC/supersolid**: choose Rb-87 or dipolar Dy-164, and use Bragg excitation, roton softening, condensate fraction, superfluid response/stiffness and density contrast as *independent* observables. A single shared spectral shape alone does not show phase coherence/superfluidity.
3. **YM/OS**: selected original Wilson observables and all-word reflection positivity, continuum measure, covariance decay and genuine same OS H. Positive finite samples do not imply full reflection positivity or uniform continuum mass gap.
4. **Gravitational effects**: observe source-specific renormalised stress tensor (not just trace), Einstein/KK field equations, gravitational redshift/lensing/force or calibrated local acceleration with uncertainties; compare positive-G effective stress and hypothetical universal negative-G as distinct hypotheses. Casimir vacuum energy alone does not demonstrate propulsion or antigravity.
5. **RH**: original full Hilbert–Pólya constructed spectral operator (not a 2×2 fixture), actual completed-ξ zero relation in both directions, multiplicity and exhaustion of zeros; no zero-location theorem imported from this OS result.
6. **BSD**: separately selected modular elliptic L-function, analytic continuation, local Euler factors and rank comparison. Do not coerce ordinary spectral zeta into L(E,s).
7. **Monster/gravity**: selected VOA representation and modular partition function on the literal state space; independent gravitational dynamics/AdS3 duality. C3 root-of-unity transport or 196884 component counts alone are not physical gravity.

## Present maximum-cut gates, source first
P0. Agda kernel-check #1492 and this Agda extension on Nix/Agda environment used by the repository (no CI dependency).
P0. Inhabit physically non-vacuous OriginalIsometricStrongLimitSource, RealTimeDerivativeBridge, PhysicalHbarEnergyConversion on completed physical Hilbert spaces; identify actual original OS.hamiltonian as self-adjoint Stone generator.
P0. Produce original-source complex spectral parameter/true off-real resolvent with boundedness; prove domain equality, adjoints and resolvent identity.
P1. Attach spectral theorem and Borel functional calculus with projection measures, including continuous spectrum and full domain control.
P1. Certify trace-class heat semigroup or explicitly select local/relative trace and counterterms where infinite-volume trace diverges.
P1. Bind momentum-density/response observables under J; calculate S(q,ω) with real experimental uncertainty and finite-volume/thermodynamic limits.
P1. Pay original KK measured cone/source-gravity action and antigravity same-tensor physically calibrated stress leaves.
P2. Independently discharge actual RH completed-ξ, BSD rank, Monster VOA↔gravity dual, and Yang–Mills continuum mass-gap claims.

## Attribution
Osterwalder–Schrader reconstruction: Osterwalder and Schrader (1973, 1975). Strong generators and one-parameter unitary groups: Stone. Spectral theorem, resolvent, Borel calculus and trace invariance: standard functional analysis. Bose occupation: Bose/Einstein; helium collective dynamics: Landau and experimental neutron-scattering literature. Hilbert–Pólya: conjectural RH route; Monster/AdS3: Witten's proposed duality. This Agda module's source-native transport construction is an integration, not an independent physical discovery or claim that these conjectures are solved.


## Executable finite donor regression, independent of Agda kernel
\`scripts/tsvf_os_finite_resolvent_donor_regression.py\` mirrors the existing exact 2×2 spectral donor \`RationalTwoByTwoSelfAdjointSpectralExact.agda\` (diagonal 2 and 5; conjugated observer frame, not a second independent source). Five unittest cases covering complex off-real resolvents, conjugacy, finite spectral projections, semigroup/zeta traces, and resonant-shift/one-mode negative controls were replayed locally on 2026-11-10 and **5/5 passed**. The Python regression is a numerical/algebraic consistency test; it is not Agda kernel acceptance, continuum spectrum, Hilbert–Pólya physical identification or empirical validation. Command: \`python scripts/tsvf_os_finite_resolvent_donor_regression.py -v\`.
