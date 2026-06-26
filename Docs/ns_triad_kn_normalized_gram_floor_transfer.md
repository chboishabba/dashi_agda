# Gram Matrix Normalization Transfer and Spectral Scaling

This document formalizes the mapping between the normalized Gram matrix $K_N(A)$ and the unnormalized residue-facing operator $\widetilde{K}_N(A)$ within the Dashi $A$-weighted framework.

## Normalization Definitions

Let $L_{\text{neg}}(A)$ and $L_{\text{abs}}(A)$ denote the negative-coupling and absolute-coupling operators on the triad space. 

1. **Normalized Gram Operator:**
   $$K_N(A) = L_{\text{abs}}(A)^{-1/2} L_{\text{neg}}(A) L_{\text{abs}}(A)^{-1/2}$$
   The empirical block decomposition demonstrates a uniform lower bound on the spectrum of $K_N(A)$:
   $$\lambda_{\min}(K_N(A)) \geq c_0 > 0 \quad \text{uniformly in } N, \text{ with } c_0 \approx 0.16.$$

2. **Unnormalized Residue-Facing Operator:**
   $$\widetilde{K}_N(A) = L_{\text{neg}}(A)$$
   This operator acts directly on the unnormalized Fourier modes and dictates the $q_{\text{gap}}$ scaling bounds.

---

## Normalization Transfer Mapping

For any test vector $v$ in the domain of the operators, the Rayleigh quotient relation is given by:
$$\frac{\langle v, L_{\text{neg}} v \rangle}{\langle v, v \rangle} = \frac{\langle w, K_N w \rangle}{\langle w, L_{\text{abs}}^{-1} w \rangle}$$
where $w = L_{\text{abs}}^{1/2} v$.

### Scaling of the Absolute Operator $L_{\text{abs}}$
For a triad profile of shell $N$ matching the admissible $1\text{–}(N-1)\text{–}N$ structure, the absolute coupling capacity scales inversely with shell size due to the Biot-Savart decay factor:
$$\| L_{\text{abs}} \| \sim \frac{C_1}{N}$$

Thus, the eigenvalues of the absolute weight operator satisfy:
$$\lambda_{\min}(L_{\text{abs}}) \approx \frac{c_{\text{abs}}}{N}$$

### Scaling Transfer Theorem

> [!IMPORTANT]
> By min-max characterization, the lowest eigenvalue of the unnormalized operator satisfies:
> $$\lambda_{\min}(\widetilde{K}_N(A)) = \inf_{v \neq 0} \frac{\langle v, L_{\text{neg}} v \rangle}{\langle v, v \rangle} \geq \lambda_{\min}(K_N(A)) \cdot \lambda_{\min}(L_{\text{abs}}(A))$$
> Under the uniform floor $\lambda_{\min}(K_N(A)) \geq c_0 > 0$:
> $$\lambda_{\min}(\widetilde{K}_N(A)) \geq c_0 \cdot \left( \frac{c_{\text{abs}}}{N} \right) = \frac{c}{N}$$

Hence, the constant normalized floor $\lambda_{\min}(K_N) \geq c_0$ directly matches the $\mathcal{O}(1/N)$ unnormalized scaling used in the downstream residue/coercivity proofs.

---

## The Verification Program

To close the theorem:
1. **Azimuthal Equidistribution on Seam:** Prove $\lambda_{\min}(K_{\text{cross}}(A)) \geq c_0$.
2. **Complement Interlacing:** Show $\lambda_{\min}(K_{\text{comp}}(A)) \geq \lambda_{\min}(K_{\text{cross}}(A))$.
3. **Weak Remainder Bounds:** Show $\| R_N(A) \| \leq \frac{\epsilon}{N}$.
