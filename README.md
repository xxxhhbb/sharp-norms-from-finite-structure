# Sharp Norms from Finite Structure

[Read the paper (PDF)](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf)

The paper gives sharp graph-matrix norm laws from finite structure and uses them to obtain two application-level results: square-root-scale degree-four clique SoS feasibility and precise spectral behavior of Gaussian tensor networks. It also develops a norm theory for structured random factors.

## Main results

### Sharp norms for graph matrices

For every fixed simple graph shape in the dense Rademacher model, including shapes with overlapping or empty matrix boundaries, the paper proves

$$
\mathbb{E}\lVert M_\alpha\rVert
=\Theta_\alpha\left(n^{(v+h-s)/2}(\log n)^{a_*/2}\right).
$$

Here $v$ is the number of shape vertices, $h$ counts isolated summation vertices, and $s$ is the minimum size of a separator between the matrix boundaries. Among minimum separators, $a_*$ is the largest number of components adjacent to the separator that meet neither surviving boundary. Both exponents therefore come from finite optimizations on the shape. Matching upper and lower bounds identify the logarithmic factor, which coarse graph parameters alone can miss.

### Square-root-scale degree-four clique SoS

For $G(n,1/2)$, with probability at least $1-n^{-10}$, the paper constructs feasible degree-four pseudoexpectations simultaneously for every real $9\le k\le c\sqrt{n}$, where $c>0$ is an absolute constant. The construction reaches the square-root scale without an asymptotic logarithmic loss for this relaxation.

### Sharp spectra for Gaussian tensor networks

For fixed networks with independent Gaussian tensors and equal edge dimensions, the paper gives sharp mean-Gram deviation scales and necessary and sufficient cut criteria for convergence in operator norm and unnormalized Schatten norms. For connected, loopless complex-Gaussian networks with nonempty input and output boundaries, it also proves convergence of the rescaled largest output-state eigenvalue to the exact right edge of the limiting law, determining the constant correction to min-entropy.

### Structural norm theory for random factors

The layerwise separator method also gives sharp norms for specified independent-factor models under explicit fixed-law moment assumptions. Further theorems cover local weights, unequal dimensions, bounded asymmetric noise, Gaussian inputs, and fixed-degree Hermite inputs.

The assumptions and precise theorem statements are in the [paper](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf).
