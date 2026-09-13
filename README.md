# Sharp Norms from Finite Structure

[Read the paper (PDF)](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf)

The paper gives sharp graph-matrix norm laws from finite structure and uses them to obtain two application-level results: square-root-scale degree-four clique SoS feasibility and precise spectral behavior of Gaussian tensor networks. It also develops a norm theory for structured random factors.

## Main results

### Sharp norms for graph matrices

For every fixed simple graph shape in the dense Rademacher model, including shapes with overlapping or empty matrix boundaries, the paper proves

```math
\mathbb{E}\lVert M_\alpha\rVert
=\Theta_\alpha\left(n^{(v+h-s)/2}(\log n)^{a_*/2}\right).
```

Here $v$ is the number of shape vertices, $h$ counts isolated summation vertices, and $s$ is the minimum size of a separator between the matrix boundaries. Among minimum separators, $a_*$ is the largest number of components adjacent to the separator that meet neither surviving boundary. Both exponents therefore come from finite optimizations on the shape. Matching upper and lower bounds identify the logarithmic factor, which coarse graph parameters alone can miss.

### Square-root-scale degree-four clique SoS

For $G\sim G(n,1/2)$ and all sufficiently large $n$, we prove

```math
\begin{gathered}
\mathbb{P}\left[
  \forall k\in[9,cn^{1/2}],\quad
  \exists\mathcal{L}_k\ \text{feasible}
\right]\ge 1-n^{-10},\\
c>0\ \text{absolute},\qquad n\ge n_0.
\end{gathered}
```

The size range reaches **a fixed positive constant times the square root of n**. Each pseudoexpectation satisfies normalization, positivity on squares of degree-two polynomials, and all Boolean, nonedge, and size constraints through their allowed degrees.

**Contribution.** The result sharpens the Hopkins–Kothari–Potechin quartic-correction construction from a square-root scale with an asymptotic logarithmic loss to $c\sqrt{n}$. Critical log-free norm estimates and an exact positive-square identity make the full moment system feasible. Consequently, this degree-four relaxation cannot exclude clique sizes throughout the displayed range; the constant $c$ is not optimized.

### Sharp spectra for Gaussian tensor networks

Fix a finite, loopless network of independent standard circular complex-Gaussian tensors, with at least one tensor, every component meeting a terminal, and every edge having dimension $N$. Let $H_N$ be its contracted map, $b$ the number of input legs, and $R$ the total number of internal edges and open legs. Define the mean-normalized map and its Gram deviation by

```math
M_N=N^{-(R-b)/2}H_N,
\qquad
F_N=M_N^*M_N-I_{N^b}.
```

For a nonempty tensor set $T$, let $c(T)$ count internal edges crossing its boundary and let $a(T),b(T)$ count its incident output and input legs. The signed cut gap is

```math
\Delta=\min_{\varnothing\ne T}\bigl(c(T)+a(T)-b(T)\bigr).
```

**Sharp rates and exact convergence thresholds.** For every fixed $1\le t<\infty$,

```math
\begin{aligned}
\mathbb{E}\lVert F_N\rVert_{S_t}
  &\asymp N^{b/t-\Delta/2}
  &&(\Delta\ge0),\\
\mathbb{E}\lVert F_N\rVert_{\mathrm{op}}
  &\asymp N^{-\Delta/2}
  &&(\Delta>0).
\end{aligned}
```

Across all signs of $\Delta$, the necessary and sufficient conditions are

```math
\begin{aligned}
\lVert F_N\rVert_{\mathrm{op}}\xrightarrow{\mathbb{P}}0
  &\iff \Delta>0,\\
\lVert F_N\rVert_{S_t}\xrightarrow{\mathbb{P}}0
  &\iff \Delta>\frac{2b}{t}.
\end{aligned}
```

The Schatten norms here are **unnormalized**. These formulas determine both when the network approaches an isometry and its sharp deviation scale. They also quantify why operator, Frobenius, and trace norms can have different convergence thresholds.

**Exact spectral edge and min-entropy constant.** If the network is connected and both boundary sets are nonempty, let $s$ be the minimum input-output edge-cut size and set

```math
\rho_A=\frac{H_NH_N^*}{\lVert H_N\rVert_F^2},
\qquad
E_G=\sup\mathrm{supp}(\mu_G),
```

where $\mu_G$ is the network's limiting law specified by its minimum-energy permutation moments. We prove

```math
N^s\lambda_{\max}(\rho_A)\xrightarrow{\mathbb{P}}E_G,
\qquad
H_\infty(\rho_A)=s\log N-\log E_G+o_{\mathbb{P}}(1).
```

**Contribution.** This strengthens the high-probability scale estimate $\lambda_{\max}(\rho_A)=\Theta(N^{-s})$ to an exact limiting constant and identifies the constant correction to min-entropy. The spectral-edge theorem rules out right outliers at every fixed positive distance from $E_G$, which convergence of fixed moments alone does not establish.

### Structural norm theory for random factors

For a fixed typed model with independent factor arrays and role dimensions comparable to $n$, suppose each factor law is fixed, symmetric, has variance one, and satisfies

```math
\lVert\xi_e\rVert_{L^q}\asymp_e q^{\theta_e/2},
\qquad q\ge2,\qquad 0\le\theta_e\le2.
```

After removing unused summation roles and detached scalar components to obtain the core, let $s$ be its minimum separator size and let $a(S)$ count its active components. We prove the sharp formula

```math
\begin{aligned}
b_{\ast}&=\max_{\substack{S\text{ separates the core boundaries}\\|S|=s}}
       \left(a(S)+\sum_{e\subseteq S}\theta_e\right),\\
\mathbb{E}\lVert H\rVert
  &\asymp n^{(v+h-s)/2}(\log n)^{b_{\ast}/2},
\end{aligned}
```

where $v$ is the original role count and $h$ counts unused summation roles; factor occurrences in the sum belong to the core.

**Contribution.** The formula separates two sources of extreme growth: fluctuations in components attached to a cut and the tails of factors supported entirely on that cut. Their contributions add at one cut and compete across minimum cuts, giving a computable logarithmic exponent with a matching lower bound.

For example, take mutually independent $n\times n$ standard Gaussian matrices $G_0,\ldots,G_L$ and diagonal gates $D_j$ whose entries are products of $q_j$ independent standard Gaussians. For fixed $L\ge1$ and nonnegative integers $q_j$,

```math
\mathbb{E}\lVert G_0D_1G_1\cdots D_LG_L\rVert
\asymp n^{(L+1)/2}(\log n)^{\frac12\max_j q_j}.
```

The largest gate degree determines the logarithm, even though the matrix product contains every gate.

Separate theorems treat local weights and unequal role dimensions through weighted minimum cuts, and establish comparisons for bounded asymmetric noise, Gaussian inputs, and fixed-degree Hermite inputs under their stated hypotheses.

The assumptions and precise theorem statements are in the [paper](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf).
