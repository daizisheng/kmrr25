# kmrr25

Solutions, with Lean 4 formalizations, to problems from

> B. Kra, J. Moreira, F. K. Richter, D. Robertson,
> *Problems on infinite sumset configurations in the integers and beyond*,
> Bull. Amer. Math. Soc. 62 (2025), 537–574, [arXiv:2311.06197](https://arxiv.org/abs/2311.06197).

Question numbers follow arXiv:2311.06197v2. Questions posed in the survey without a number are
named by their subsection and a letter in order of appearance, e.g. §3.2(a).

## Layout

- `paper/kmrr-solutions/`: the paper *Solutions to several problems on infinite sumset
  configurations* by Shisheng Li and Yong Su (LaTeX sources and `main.pdf`). It answers twenty
  questions from the survey, including Question 5.14 (sums of k infinite sets in every countably
  infinite abelian group), and a question of Kousek and Radić on lower Banach density.
- `lean/`: Lean 4 formalizations of a number of results of the paper.

## Lean formalizations

The project uses Lean `v4.33.1` and Mathlib `v4.33.1`. To build it:

```sh
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build
```

None of the files contains `sorry` or adds an axiom. Every main theorem depends only on the
standard axioms `propext`, `Classical.choice` and `Quot.sound`. Where a result of the paper relies
on a published theorem that is not formalized, that theorem is stated as a `Prop` and passed in
as an explicit hypothesis. The table marks these cases.

| File | Paper result | Survey question | External input |
|---|---|---|---|
| `Q320.lean` | colourings with bad multipliers in every residue class | 3.20 | — |
| `Q323.lean` | a set of positive logarithmic density with no ℓB+mB+t | 3.23 | — |
| `Q324.lean` | log-equidistributed sets without B+B+t (both examples) | 3.24 | — |
| `S32a.lean` | both readings of the density condition | §3.2(a) | — |
| `S33a.lean` | ordered polynomial sums: negative direction | §3.3(a) | — |
| `S33a.lean` | ordered polynomial sums: positive direction | §3.3(a) | Kousek, Thm 1.2 |
| `S33e.lean` | generalisations of Question 3.18 (and Question 3.18 itself) | §3.3(e), 3.18 | — |
| `Q331.lean` | k-fold sums of blocks from a density Ramsey family | 3.31, §3.6(a) | KMRR, density finite sums (dynamical input) |
| `Q413.lean` | the integer-exponent case | 4.13 | — |
| `Q413a.lean` | the non-integer case, from the second-moment bound | 4.13 | the second-moment bound of the paper's proof |
| `S44a.lean` | random sets: monotone criterion, finite configurations, gap example | §4.4(a) | — |
| `C45.lean` | {b+c : b<c} ⊂ P with C ⊂ P−1 | Conjecture 4.5 | Tao–Ziegler, Thm 1.5 |
| `Q510.lean` | fibrewise density does not suffice in ℕ² | 5.10 | — |
| `Q516.lean` | admissible translates when [G:2G] < ∞ | 5.16, §5.3(a) | Charamaras–Mountakis, Cor. 1.13 |
| `Q523.lean` | the corner configuration in G^d | 5.23, §5.4(b) | — |
| `S51a.lean` | Bohr sets, Beatty sequences, {λ = 1} | §5.1(a) | — |
| `Q54.lean` | sums and shifted products at logarithmic scale | 5.4 | — |
| `Q56.lean`, `DoubleFolnerQ.lean` | sums and products in ℚ, double Følner sequences | 5.6 | — |
| `KR52.lean` | lower Banach density thresholds 1/2 and 3/4 | Kousek–Radić, Question 5.2 | — |

The main theorem of the paper (Question 5.14) is not formalized.

The module docstring of each file lists exactly which statements of the paper it covers and
which it does not.

## Authors

Shisheng Li and Yong Su. The work was carried out in collaboration with AI systems; see the
statement at the end of the paper.
