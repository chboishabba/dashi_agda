# Periodic Navier–Stokes Wall-I research surface

This tranche treats Wall I as a falsifiable harmonic-analysis programme rather than a record-inhabitation exercise. It freezes one executable finite Galerkin model, adds exact finite combinatorics in Agda, and leaves the genuinely cutoff-uniform inequalities fail-closed.

## Frozen executable model

`scripts/ns_periodic_wall_i_lab.py` uses the following conventions.

- Domain: \((\mathbb R/2\pi\mathbb Z)^3\).
- Fourier series: \(u(x)=\sum_{k\in\mathbb Z^3}\widehat u(k)e^{ik\cdot x}\), so \(\widehat{\partial_j u}(k)=ik_j\widehat u(k)\).
- Galerkin carrier: the duplicate-free max-coordinate cube \(|k|_\infty\le N\), matching `NSPeriodicConcreteCutoffCubeCarrier`.
- Reality condition: optional exact conjugate pairing in state experiments.
- Zero mode: enumerated exactly once; the Biot–Savart multiplier is zero there.
- Coefficient norm: Euclidean norm on \(\mathbb C^3\).
- Leray multiplier: \(\Pi_k=I-k\otimes k/|k|_2^2\) for \(k\ne0\), and \(I\) at zero.
- Biot–Savart multiplier: \(i k\times/|k|_2^2\) for \(k\ne0\), and zero at zero.
- Shell radius: the exact integer surrogate \(\rho(k)=|k|_\infty\).
- Shell profile: a rational dyadic hat centred at \(2^j\), with exact partition sum one and no more than two active adjacent shells.

The max-coordinate radius is intentional: it makes support, finite differences, and cube membership decidable with rational arithmetic. It is not silently identified with the smooth Euclidean radial profile. Any later Euclidean-profile theorem must include an explicit comparison.

## What the laboratory computes

The executable performs four separate tasks.

1. It verifies the rational shell partition and overlap count exactly with `Fraction`.
2. It enumerates literal resonant triads \(p+q=k\), classifies them into near LH/HL/HH, oriented far-low, and far-high lanes, and computes finite Hilbert–Schmidt geometry majorants.
3. It constructs a support-masked rational far-low commutator majorant and calculates literal weighted row and column folds.
4. It computes the Sobolev/geometric far-high tail from the actual surplus \(s-5/2\), rather than inserting a desired constant.

It also runs floating-point state experiments for arbitrary, divergence-free, real-conjugate-symmetric, and shell-concentrated states. The same state shape is rescaled through amplitudes \(1/4,1/2,1,2\). This exposes the cubic scaling of the nonlinear term against the quadratic scaling of dissipation.

## First exact reconnaissance result

The command

```bash
python scripts/ns_periodic_wall_i_lab.py \
  --cutoff 4 \
  --output-shell 2 \
  --separation 2 \
  --target-separation 8 \
  --sobolev-twice 7 \
  --skip-state-experiments
```

produces the following finite facts for this deliberately small model.

- The cube contains exactly \((2N+1)^3=729\) modes.
- There are 167,662 target-shell resonant triads.
- The oriented far-low supports contain 12,250 triads in each placement.
- The conservative absolute \(\ell^1\) Schur surrogate has row maximum `260`, column maximum `109712267774741/28832328525`, and product approximately `989347.41`.
- For \(s=7/2\), the derivative surplus is one. At \(R=8\), the exact one-placement infinite tail is \(1/128\), while the literal two-placement sum is \(1/64\). Thus this bare geometric factor fits both \(1/16\) and \(1/8\); the remaining issue is the structural product constant, not the geometric series itself.

The far-low number is not a theorem about the official operator. It is a useful negative result: taking absolute values before exploiting the full cancellation and weight geometry is catastrophically wasteful. A successful `farLowRadiusEightFitsEighth` proof must improve the kernel before Schur, change the weight factorisation, or use a sharper norm than this raw surrogate.

## Structural near-lane result

For a fixed state shape, scaling \(u\mapsto\lambda u\) sends the tested trilinear contribution to \(\lambda^3\) and dissipation to \(\lambda^2\). The executable therefore reports amplitude-doubling ratios for \(N_{\mathrm{lane}}/D\). Ratios near two are expected and observed whenever the lane is populated.

Consequently, no estimate of the form

\[
N_{\mathrm{lane}}(u)\le \varepsilon D(u)
\]

can hold uniformly over arbitrary amplitudes. The final near proof must visibly use a dimensionless smallness source: compact-\(\Gamma\) boundary control, first-exit data, high-frequency smallness, angular depletion, or a residual charged by Wall II. This is now an executable falsification criterion, not merely a warning in prose.

## Agda modules added

The finite, decidable layer is split into the requested owners.

### Near

- `NSPeriodicConcreteNearTriadSums`
- `NSPeriodicNearTriadClassification`
- `NSPeriodicNearTriadPartitionCorrectness`
- `NSPeriodicNearShellOverlapCount`
- `NSPeriodicNearConvolutionMultiplicity`

These define literal resonant triads, an executable dyadic-gap Bony classifier, exact LH/HL/HH folds, a machine-checked partition identity, a structural two-shell overlap carrier, and duplicate-free Cartesian convolution multiplicity.

### Far-low

- `NSPeriodicConcreteFarLowKernel`
- `NSPeriodicFarLowSupportGeometry`
- `NSPeriodicFarLowKernelZeroExtension`
- `NSPeriodicFarLowShellIntersectionCount`
- `NSPeriodicFarLowRowMajorantFold`
- `NSPeriodicFarLowColumnMajorantFold`

The kernel is support-masked by construction, so unsupported entries reduce definitionally to zero. Row and column folds share that owner, append exactly, and remain invariant under zero extensions. Shell-intersection counts are literal filtered-list counts bounded by the original enumeration length.

### Far-high

- `NSPeriodicConcreteFarHighPlacements`
- `NSPeriodicFarHighShellSeparation`
- `NSPeriodicFarHighFiniteTail`
- `NSPeriodicFarHighTailReindexing`

These provide the exact two-placement owner, constructive shell separation, literal finite tail indices and lengths, and successor reindexing of the tail fold.

## Honest theorem boundary

This tranche does **not** mark the following as inhabited:

- the three cutoff-uniform near product inequalities;
- the official far-low row and column constants;
- the complete far-high product/Sobolev structural constant;
- `concreteWallIHarmonicInputs`;
- Wall I, Wall II, the BKM gate, or global regularity.

The new code narrows and tests those leaves without assuming any statement equivalent to the desired conclusion. The status booleans remain false until the analytic estimates are actually proved and typechecked.
