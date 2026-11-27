# Completion and repair of Hadamard frames

A partial Hadamard matrix has entries $`+1`$ or $`-1`$ and mutually orthogonal rows, but fewer rows than columns. This project studies how to complete one, and how much of it must change when direct completion fails.

An augmenting exchange deletes $`r`$ existing rows and inserts $`r+1`$ new sign rows while preserving orthogonality with every retained row. Its cost is $`r`$. A tensor product replaces each entry of the first matrix by that entry times the second matrix.

## Main results

### 1. A three-row repair barrier survives every Hadamard tensor factor

An explicit $`16\times24`$ partial Hadamard matrix $`P`$ has minimum augmenting-exchange cost exactly three. For every full Hadamard matrix $`H`$, the product $`P\otimes H`$ also has minimum cost exactly three. Tensoring cannot bypass this barrier by inserting rows that are not themselves tensor products.

### 2. Real-valued fillings give no advantage for two-zero weighing matrices

Let $`n\ge4`$ be divisible by four, and let $`W`$ be an $`n\times n`$ matrix with entries $`0,\pm1`$ with $`WW^{\mathsf T}=(n-2)I_n`$. A matrix satisfying $`HH^{\mathsf T}=nI_n`$, obtained by changing only the zero entries of $`W`$ to arbitrary real values, exists if and only if those zeros can instead be filled with signs to obtain a Hadamard matrix.

### 3. Classification of the largest intersections with the sign cube

A $`q`$-dimensional real subspace $`V\subseteq\mathbb R^n`$ contains at most $`2^q`$ sign vectors. Equality holds exactly when, after permuting and negating coordinates, its vectors are constant on each of $`q`$ nonempty coordinate blocks. In this equality case, when $`V`$ is the orthogonal complement of a partial Hadamard frame, these blocks have equal size $`n/q`$, and completion reduces to a Hadamard matrix of order $`q`$.

Read the [paper](paper/main.pdf) for proofs and citations, or [further results](RESULTS.md) for the rest of the mathematical development. The [technical guide](TECHNICAL.md) covers building the Lean proofs, dependencies, formalization coverage, and submission checks.

Joshua Mark · [ORCID](https://orcid.org/0009-0003-5905-2382)
