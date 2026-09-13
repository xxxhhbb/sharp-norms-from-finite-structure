# Sharp Norms from Finite Structure

[Read the paper (PDF)](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf)

Graph matrices built from shared random variables arise in spectral algorithms, sum-of-squares proofs, and high-dimensional statistics. This paper shows how finite structural data determine their sharp expected operator-norm growth.

## Main result

For every fixed simple graph shape in the dense Rademacher model, including shapes with overlapping or empty matrix boundaries, the paper proves

$$
\mathbb{E}\|M_\alpha\|
=\Theta_\alpha\!\left(n^{(v+h-s)/2}(\log n)^{a_*/2}\right).
$$

Here $v$ is the number of shape vertices, $h$ counts isolated summation vertices, and $s$ is the minimum size of a separator between the matrix boundaries. Among minimum separators, $a_*$ is the largest number of components adjacent to the separator that meet neither surviving boundary. Both exponents therefore come from finite optimizations on the shape. Matching upper and lower bounds identify the logarithmic factor, which coarse graph parameters alone can miss.

## Extensions and applications

- **Structured random factors.** The separator method also gives sharp norms for specified independent-factor models under explicit fixed-law moment assumptions, with further results for local weights, unequal dimensions, bounded asymmetric noise, Gaussian inputs, and fixed-degree Hermite inputs.
- **Degree-four clique SoS.** For $G(n,1/2)$, the paper constructs feasible degree-four pseudoexpectations, with high probability, simultaneously for $9\le k\le c\sqrt n$ for an absolute constant $c>0$. This reaches the square-root scale without an asymptotic logarithmic loss for the stated relaxation.
- **Gaussian tensor networks.** For fixed networks with independent Gaussian tensors and equal edge dimensions, the paper gives sharp mean-Gram deviation scales and necessary and sufficient convergence thresholds. For connected, loopless complex-Gaussian networks with nonempty input and output boundaries, it also identifies the limiting right spectral edge and the constant correction to min-entropy.

The assumptions and precise theorem statements are in the [paper](./Sharp%20Norms%20from%20Finite%20Structure%20-%20arXiv.pdf).
