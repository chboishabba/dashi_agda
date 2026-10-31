# Existing Hardy and Littlewood–Paley owners → twin-correlation max-cut audit

Date: 2026-10-31. This is an audit and precise reuse plan, not an unconditional twin-prime proof.

## Actual source owners inspected
- `DASHI.Physics.Closure.NSTriadKNPeriodicLittlewoodPaleyBonyExact`: finite periodic Z³ Fourier hard shell/low-pass projectors, mode-local derivative and curl commutation, exact triad classification. Do not claim a scalar arithmetic Fourier prime-correlation theorem from this.
- `DASHI.Physics.Closure.NSTriadKNLittlewoodPaleyInfrastructureInventory`: explicit finite periodic hard shell, Bernstein and Bony/Tao parts; smooth-projector norm comparison, continuum passage and time-integral identification remain separately typed.
- `DASHI.Physics.Closure.PrimeBandLPDefinitionReceipt`: bases 2,3,5 as frequency-band labels, not the set of all arithmetic primes. Existing receipt explicitly identifies unproved smooth multiplier and Besov norm stages.
- `DASHI.Physics.Closure.NSSprint111LPGrafakosInfrastructureAndStrainRefocus`: marks classical imported LP/Grafakos/Rudin authority scoped to an NS strain argument, and leaves the actual strain correlation false.
- `DASHI.Mathematics.NumberTheory.PartitionHardyRamanujanErdosBridgeExact`: Hardy–Ramanujan *partition* asymptotics, not Hardy–Littlewood twin-prime conjecture.
- `DASHI.Arithmetic.TwinPrimeMangoldtPrimeErrorFiniteSplitExact`, `TwinPrimeMangoldtNonzeroPrimeSumWitnessExact`, `TwinPrimeSOTABoundedGapBidiExact`: actual arithmetic owners to reuse, not bypass.

GitHub default-branch content search for `HardyLittlewood` did not return a precise owner by that name; this is a *search limitation*, not proof of absence in other branches/repositories. Do not assert all existing Hardy–Littlewood work has been checked.

## Exact arithmetic Fourier transport task

Let f_X(n)=Lambda(n)1_{2<=n<=X} with zero extension on a finite cyclic ring of modulus M>2X+2. The finite cyclic correlation identity for the zero-extended values is:

C_X(2) = sum_{n in Z/M} f_X(n) f_X(n+2)
       = (1/M) sum_{r in Z/M} |F_X(r)|² exp(2 pi i *2r/M),

with a consistent Fourier-transform sign convention and real-valued f_X. For **precise** endpoint convention `S(X)=sum_{n+2<=X} Lambda(n)Lambda(n+2)`, extend n<=X and use M>2X+2 to avoid wraparound. This is an exact *finite algebraic identity*, not a prime-specific lower bound.

CAUTION: the RHS is a signed cosine sum, even though |F|²>=0. Neither Parseval nor Littlewood–Paley shell energy positivity yields a positive C_X(2) by itself. Any symmetrisation or dyadic shell averaging must retain phase and cross-shell terms and verify no aliasing.

One arithmetic Fourier bridge should provide:
1. finite cyclic additive characters, transform and exact inverse;
2. explicit zero-extension and no-wrap lemma;
3. shift-2 Fourier correlation identity, with sign convention tested;
4. one-dimensional frequency LP shell partition and cross-term budget, **not** reinterpret the Z³ Navier–Stokes mode carrier as Z/M without a typed map;
5. prime-power error decomposition and real log comparison;
6. **open** nontrivial arithmetic major/minor arc or signed correlation estimate proving C_X(2) >= cX (or weak unbounded P), rather than adding it as an implicit field.
 
## New max-cut
Finite Fourier/LP is a powerful exact change of coordinates but cannot alone overcome sieve parity. The hardest lemma becomes **signed shift-two phase cancellation** of the nonzero frequencies sufficiently sharp to leave a positive main term. Hardy–Littlewood singular series 2C2 and R(X)=o(X) remain a separate conjectural target. Do not confuse Hardy–Littlewood maximal functions with the Hardy–Littlewood prime-pair conjecture or Hardy–Ramanujan asymptotics.

**Status:** documented owner reuse and discriminator; no Agda kernel run or new analytic theorem; no ESD edits. All original mathematical and in-repo owners remain attributed.


## Executed arithmetic Fourier bridge test (31 October)

New independent finite regression `scripts/check_twin_prime_fourier_signed_shell_maxcut.py` computes the *actual* finite classical von Mangoldt sequence on zero-extended cyclic domains, directly reconstructs shift-two correlation through the DFT, and divides the frequency sum into disjoint signed shells. Ran with local Python: PASS.

| X | M | original correlation | signed LP-like shell contributions |
|---:|---:|---:|---|
|10|32|7.51822365|4.82568794, 0.93643475, 1.75610096|
|20|64|24.64528461|14.25092113, 2.03913758, 8.35522590|
|40|128|46.72241952|25.80865086, 2.47086861, 18.44290004|

For positive-support adversarial sequences `[1,0,0,0,0,0,0,0]` and `[1,1,0,0,0,0,0,0]`, each total shift-two correlation is zero despite positive total Fourier energy. Signed shell contributions are `[0.125,-0.25,0.125]` and `[0.5,-0.5,0]`, respectively. A shell norm/energy bound by itself therefore cannot yield shifted-prime positivity. No Fourier phase is dropped. All computations are float-based sanity checks, not certified Fourier theorems.

**Remaining maximal cut:** exact Agda finite cyclic transform and signed-shell identity (finite algebra), followed by a *new unconditional prime-specific signed remainder bound* (hard number theory). Existing Z^3 Navier–Stokes Littlewood–Paley source cannot be silently treated as scalar Z/M arithmetic analysis. No kernel proof, no twin-prime infinitude proof. Reuse and attribution of all source owners preserved.
