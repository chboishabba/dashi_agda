# Radix-2 vs C3 in certified Machin pi — 18 November 2026

## Exact rational identity
For a=1/8,b=3/41, (a+b)/(1-ab)=1/5 exactly. Both angles
are positive and their sum is less than pi/2, so on the usual positive branch
atan(1/5)=atan(1/8)+atan(3/41). Formal same-original-Bishop-real
identification still requires the source arctangent addition/branch theorem.
Do not promote a tangent identity or finite-precision interval agreement
to a Bishop limit equality.

## Actual tested computation
The companion check_bishop_fast_pi_power_two_split.py implements arbitrary
positive rational p/q arctangent P/Q/T terms, and a binary-shift variant
for p=1 and q=2^s. Each split node represents its denominator as
Q_odd * 2^exponent, so its merge uses
T = (T_left * Q_odd_right << exp_right) + P_left * T_right.
The routine was tested for q=8,16,32,64 and 35 prefixes against the
ordinary rational recurrence. Independent direct Fraction sums for
p/q=3/41,1/5,1/239 and finite certified interval intersections were
also tested. The per-term certification uses the actual alternating
series next-term magnitude. These are finite reference tests, not Agda.

| Decimal digits | Original Machin P/Q/T | Decomposed ordinary | Decomposed with 2-shifts |
|---:|---:|---:|---:|
| 100 | 0.046 ms | 0.056 ms | 0.055 ms |
| 1,000 | 0.769 ms | 1.030 ms | 0.998 ms |
| 3,000 | 4.439 ms | 5.925 ms | 5.787 ms |
| 10,000 | 35.584 ms | 49.159 ms | 47.487 ms |

Local Python built-in arbitrary-precision integers, seven-run median,
finite-sum evaluation only. No Agda compilation or GMP/gmpy2 benchmarking.
The proposed speed claim of under 2 ms at 10k digits is unsupported.
At 10k digits original formula needs 9,253 terms, split formula 12,039
terms (certified independent cutoffs). Shifting saves about 3.4% relative
to the decomposed calculation but the decomposition loses about 33.4%
relative to original Machin.

## Complexity and representation caveats
The binary P/Q/T tree already evaluates the q² factor once per leaf;
full powers q^(2k) do not appear repeatedly in leaves. Separating
2-adic denominator factors reduces some multiplication work but does
not eliminate odd denominator products, signed numerator products or
additional arctangent trees.

C3 characters with omega³=1 do not imply that alternating Taylor signs
(period 2) cancel. Genuine cubic Borwein requires a modular-equation
proof. Packing 40 trits into 64 bits gives entropy utilization
40log2(3)/64 about 99.06%, versus range utilization 3^40/2^64
about 65.91%; these are different notions. Packing does not
automatically speed up GMP's binary-limb products.

## Outstanding Agda welds
1. atanRationalSplitSound: arbitrary positive p/q exact finite prefix.
2. atanPowerTwoShiftSound: specialized tree equals original p=1 tree.
3. rationalTangentOneFifth: 1/8+3/41 tangent equality in source owner.
4. bishopAtanRationalAddition: same-source analytic addition plus branch.
5. shiftedMachinEnclosureSound: precision and interval transport to pi_M.
6. Pinned agda --safe acceptance and comparative kernel timings.

The first three algebraic facts have exact Python tests, not Agda
kernel acceptance. The original direct Machin split remains the fastest
measured candidate.
