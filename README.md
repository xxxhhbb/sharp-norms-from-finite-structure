# Sharp Norms from Finite Structure

[Read the paper (PDF)](./Sharp%20Norms%20from%20Finite%20Structure.pdf)
[Lean proof of the graph-matrix main theorem](./lean/README.md) · [Final theorem](./lean/R6/M1OriginalMain.lean)

The original two-sided graph-matrix norm theorem in Result 1 now has an end-to-end Lean 4.33.0 proof. The final theorem takes only the graph shape as input; its recorded axiom set contains only the standard Lean axioms. Source files, pinned dependencies, build instructions and local verification records are in [lean/](./lean/README.md). This formalization release covers the graph-matrix main theorem; the other results below are not included in its completion claim.

We establish four main results: a sharp norm classification for dense Rademacher graph matrices; degree-four clique SoS feasibility at a fixed multiple of the square-root scale; sharp convergence thresholds and exact spectral edges for Gaussian tensor networks; and a norm formula for independent random factors that accounts for both structure and scalar tails.

The central structural principle is that fluctuations add at a single cut and compete across minimum cuts. This determines sharp powers and logarithms. Additional algebraic structure yields a full SoS certificate, while a separate spectral comparison identifies exact tensor-network edge constants.

## 1. Sharp graph-matrix norms from two finite cut optimizations

For every fixed simple graph shape in the dense Rademacher model, including overlapping or empty matrix boundaries, we prove

```math
\mathbb{E}\lVert M_\alpha\rVert
=\Theta_\alpha\left(
n^{(v+h-s)/2}(\log n)^{a_{\ast}/2}
\right).
```

Here $v$ is the number of shape vertices and $h$ counts isolated summation vertices. A boundary separator is a set of vertices meeting every path between the row and column boundaries; boundary vertices themselves may belong to the separator. Let $\mathcal S$ be the set of these separators. Then

```math
s=\min_{S\in\mathcal S}|S|,
\qquad
a_{\ast}=\max_{\substack{S\in\mathcal S\\|S|=s}}a(S),
```

where $a(S)$ counts components remaining after deleting $S$ that are adjacent to $S$ and meet neither surviving boundary.

**What this achieves.** Two finite optimizations determine both growth exponents for a fixed shape of any size. Matching upper and lower bounds replace an unspecified polylogarithmic gap with the exact logarithmic exponent. The formula also distinguishes infinite families with identical coarse graph parameters but different sharp norm scales.

The upper bound controls every defect layer in a growing-order moment expansion. Conditional flattening and synchronized fluctuations provide the matching lower bound.

## 2. Degree-four clique SoS feasibility without logarithmic loss

For $G\sim G(n,1/2)$, there are absolute constants $c>0$ and $n_0$ such that, for $n\ge n_0$,

```math
\mathbb P\left[
\forall k\in[9,c n^{1/2}],\quad
\exists\mathcal L_k\ \text{degree-four clique feasible}
\right]\ge 1-n^{-10}.
```

The range reaches **a fixed positive constant times the square root of n**. The guarantee holds simultaneously for every real $k$ in this interval. Each functional satisfies the complete system

```math
\begin{aligned}
\mathcal L_k(1)&=1,\\
\mathcal L_k(p^2)&\ge0
&&(\deg p\le2),\\
\mathcal L_k((x_i^2-x_i)q)&=0
&&(\deg q\le2),\\
\mathcal L_k(x_ix_jq)&=0
&&(\{i,j\}\text{ a nonedge},\ \deg q\le2),\\
\mathcal L_k((\sum_i x_i-k)q)&=0
&&(\deg q\le3).
\end{aligned}
```

**What this achieves.** We sharpen the Hopkins–Kothari–Potechin quartic-correction construction from a square-root scale with an asymptotic logarithmic loss to $c n^{1/2}$. This degree-four relaxation therefore cannot exclude clique sizes throughout the stated range. The improvement removes the logarithmic loss while retaining all positivity and clique constraints; the absolute constant is not optimized.

Critical log-free graph-matrix estimates control the errors, and an exact positive-square identity handles the correlated quartic correction.

## 3. Gaussian tensor networks: sharp thresholds and exact spectral edges

Consider a fixed finite, loopless network with at least one tensor, independent standard circular complex-Gaussian coordinates, equal edge dimension $N$, and every component meeting a terminal. Let $H_N$ be the contracted map, $b$ the number of input legs, and $R$ the total number of internal edges and open legs. Define

```math
M_N=N^{-(R-b)/2}H_N,
\qquad
F_N=M_N^*M_N-I_{N^b}.
```

For a nonempty tensor set $T$, let $c(T)$ count internal edges crossing its boundary and let $a(T),b(T)$ count its incident output and input legs. Its signed cut gap is

```math
\Delta=\min_{\varnothing\ne T}\bigl(c(T)+a(T)-b(T)\bigr).
```

**Sharp deviation rates and necessary and sufficient thresholds.** For every fixed $1\le t<\infty$,

```math
\begin{aligned}
\mathbb E\lVert F_N\rVert_{S_t}
&\asymp N^{b/t-\Delta/2}
&&(\Delta\ge0),\\
\mathbb E\lVert F_N\rVert_{\mathrm{op}}
&\asymp N^{-\Delta/2}
&&(\Delta>0).
\end{aligned}
```

Across all signs of $\Delta$,

```math
\begin{aligned}
\lVert F_N\rVert_{\mathrm{op}}\xrightarrow{\mathbb P}0
&\iff \Delta>0,\\
\lVert F_N\rVert_{S_t}\xrightarrow{\mathbb P}0
&\iff \Delta>\frac{2b}{t}.
\end{aligned}
```

The Schatten norms are **unnormalized**. These formulas determine when the map approaches an isometry and the exact power of its deviation. The additional dimension cost $2b/t$ explains why operator, Frobenius, and trace norms can have different convergence thresholds.

**Exact right edge and min-entropy correction.** For a connected network with nonempty input and output boundaries, let $s$ be the minimum input-output edge-cut size. Set

```math
\rho_A=\frac{H_NH_N^*}{\lVert H_N\rVert_F^2},
\qquad
E_G=\sup\mathrm{supp}(\mu_G),
```

where $\mu_G$ is the known limiting law specified by the network's minimum-energy permutation moments. We prove

```math
\begin{aligned}
N^s\lambda_{\max}(\rho_A)&\xrightarrow{\mathbb P}E_G,\\
H_\infty(\rho_A)&=s\log N-\log E_G+o_{\mathbb P}(1).
\end{aligned}
```

**What this achieves.** The deviation results give exact cut criteria and matching scales. The spectral-edge result strengthens a high-probability estimate up to constant factors to a specific limiting largest-eigenvalue constant, identifying the constant correction to min-entropy. It excludes right outliers at every fixed positive distance from $E_G$, which convergence of fixed moments alone does not establish.

The edge theorem uses a flow-quotient comparison and auxiliary-dimension transfer together with the tensor-GUE strong-convergence theorem of Chen, Garza-Vargas, and van Handel.

## 4. Independent random factors: a sharp formula combining structure and tails

In a fixed typed model, each factor occurrence has its own independent array with independent, identically distributed coordinates, and every role dimension is comparable to $n$. Suppose the factor laws are fixed, symmetric, have variance one, and satisfy

```math
\lVert\xi_e\rVert_{L^q}\asymp_e q^{\theta_e/2},
\qquad q\ge2,\qquad 0\le\theta_e\le2.
```

Remove unused summation roles and detached scalar components to obtain the core. Its two-section graph joins roles that share a factor. Let $\mathcal S_{\min}$ be its minimum boundary separators, all of size $s$, and let $a(S)$ count active components as above. We prove

```math
\begin{aligned}
b_{\ast}
&=\max_{S\in\mathcal S_{\min}}
\left(a(S)+\sum_{e\subseteq S}\theta_e\right),\\
\mathbb E\lVert H\rVert
&\asymp n^{(v+h-s)/2}(\log n)^{b_{\ast}/2}.
\end{aligned}
```

Here $v$ is the original role count, $h$ counts unused summation roles, and the sum runs over core factor occurrences supported entirely on $S$.

**What this achieves.** The logarithmic exponent records both component fluctuations and factor tails. These contributions add at one cut, while different minimum cuts compete. The resulting structural formula has a matching lower bound under the stated fixed-law assumptions.

A concrete consequence concerns products of independent $n\times n$ Gaussian matrices $G_0,\ldots,G_L$ with diagonal gates $D_j$. If each gate entry is a product of $q_j$ independent standard Gaussians, all primitive Gaussian variables are independent, and $L\ge1,q_j\ge0$ are fixed integers, then

```math
\mathbb E\lVert G_0D_1G_1\cdots D_LG_L\rVert
\asymp n^{(L+1)/2}(\log n)^{\frac12\max_j q_j}.
```

The logarithmic growth depends on the **largest gate degree**, although every gate appears in the product. Separate theorems handle local weights and unequal dimensions through weighted minimum cuts, and comparisons cover bounded asymmetric noise, Gaussian inputs, and fixed-degree Hermite inputs under their respective hypotheses.

All asymptotic statements keep the shape or network fixed; implicit constants may depend on that structure and on the stated fixed model parameters. See the [full paper](./Sharp%20Norms%20from%20Finite%20Structure.pdf) for definitions, proofs, and the assumptions of each theorem.
