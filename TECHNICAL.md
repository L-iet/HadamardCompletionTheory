# Build, provenance, and formalization guide

This document contains the reproducibility and submission details for the mathematics introduced in the [README](README.md) and [further results](RESULTS.md).

## What the formalization covers

The public Lean development covers **62 of 64 principal manuscript results**. A principal result is one of the statements tracked in the paper-to-code correspondence, rather than a count of all supporting lemmas. The complete correspondence is in [paper/ALIGNMENT.json](paper/ALIGNMENT.json); [submission/SCOPE.json](submission/SCOPE.json) specifies which results are included in the prepared submission.

The labels in those files are bookkeeping identifiers. The prefixes refer to the projects: TS means tensor stability, PG phase geometry, CT completion theory, and E entropy designs. RH means the Riemann hypothesis; GRH means its generalized version. These hypotheses occur only in statements explicitly identified as conditional. They distinguish statements and their proof status; they are not additional mathematical hypotheses. The final table below explains each label by its theorem title. Proof development is currently paused.

### Results outside the public formalization

- **Conditional quantitative half-frame** (`CT-18-01`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.
- **Complete improving-neighbor census for this code** (`CT-26-02`): The complete principal statement has not been formalized. Supporting lemmas or computational certificates do not establish the whole claim.

## Build the proofs

Install Lean through elan, then run from this repository:

```sh
lake exe cache get
lake build
```

The toolchain is Lean **4.35.0**, with mathlib and its dependencies pinned in `lean-toolchain` and `lake-manifest.json`. Lake is Lean's build tool; mathlib is the community mathematics library. Downloading its cache avoids recompiling the library.

For a complete build and recorded axiom audit:

```sh
python scripts/record_verified_sources.py
python scripts/audit_mathlib_licenses.py
python -m pip install -r scripts/requirements-submission.txt
python scripts/validate_metadata.py
python scripts/check_submission.py
python scripts/check_submission_preparation.py
```

The recorder checks all configured proof and independent specification entry points. It records source hashes only after the ordinary builds and declaration audits succeed without input changes. An axiom audit checks every logical assumption on which a theorem depends. Only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` are allowed; they express propositional extensionality, classical choice, and soundness of quotients. No additional mathematical axioms or unfinished proofs are permitted in solution code.

The structure/scanner tests run before Lean setup in CI. Tests that use `.lake/` create their fixture parent themselves; they do not assume a downloaded cache or a previous build. No README, technical-guide, paper-disclosure wording, or abstract prefix is enforced by the theorem-coverage check. The guide above lists unfinished results for readers.

## Routine GitHub checks and official verification

The ordinary push/pull-request workflow runs structure/scanner tests, builds the Lean proofs, audits target axioms and pinned licenses, and validates metadata. It does not run Comparator, install its sandbox, or require a sandboxed comparison report. A standard GitHub runner may not provide the `nanoda_bin` executable that Comparator needs.

Full Challenge/Solution comparison remains available through the separate manually triggered **Official Palomar mechanical preflight** workflow and the comparison scripts below. Palomar registration still requires its official mechanical verification, including both Lean and NanoDa acceptance. A routine CI pass is not that verification.

### Independent statements and proof checking

Comparator is Lean's tool for comparing a submitted proof against an independently written statement. A `Challenge` module specifies statements using mathlib and core Lean; a `Solution` module supplies their proofs. Intentional placeholders occur only in the independent specification, which the solution must not import. They are not accepted proof dependencies.

The configurations below select groups of theorem statements and definitions. One configuration corresponds to one proposed Palomar entry, not automatically to every result in this paper. NanoDa is an independent proof checker; both it and Lean's own kernel must accept each group.

| Group | Configuration |
|---|---|
| Algorithms | [comparator-algorithms.json](comparator-algorithms.json) |
| Bloch | [comparator-bloch.json](comparator-bloch.json) |
| Character | [comparator-character.json](comparator-character.json) |
| Codes | [comparator-codes.json](comparator-codes.json) |
| Cyclic existence | [comparator-cyclic-existence.json](comparator-cyclic-existence.json) |
| Lattice | [comparator-lattice.json](comparator-lattice.json) |
| Quaternary | [comparator-quaternary.json](comparator-quaternary.json) |
| Repair | [comparator-repair.json](comparator-repair.json) |
| Main statements | [comparator.json](comparator.json) |

For local diagnostics of a selected group:

```sh
python scripts/run_local_comparator.py --config comparator.json
```

Local reports are in `submission/local-comparator*-result.json`. A documentation-only rebinding may update the source inventory after a disclosure-check script changes; it records the previous published report, checks that all Lean sources, build inputs, and exported proof bytes are unchanged, and does not claim another kernel run. They record actual kernel acceptance, or explicitly identified reuse of earlier acceptance for byte-identical exports. Such reports do not establish sandboxed registry verification. Earlier tensor-stability and phase-geometry receipts do not record original checker-binary digests; that limitation remains disclosed in their evidence.

For sandboxed checks on a compatible Linux host with bubblewrap and the configured Lean/NanoDa checker executables installed:

```sh
python scripts/run_comparator.py
python scripts/check_submission_preparation.py --require-sandbox
```

Bubblewrap isolates the source build. The preparation check also validates source bindings, complete target audits, paper/PDF bindings, licenses, and metadata. `python scripts/check_submission.py --ready` is the stricter whole-paper gate: it additionally requires complete principal-result coverage, so it fails while any principal manuscript result remains unformalized.

## Paper and publication

The [current paper](paper/main.pdf), [LaTeX source](paper/main.tex), and [standalone source bundle](paper/source.tar.gz) accompany the proofs. Rebuild them with:

```sh
python scripts/build_paper.py
python scripts/refresh_paper_bundle.py
```

On Windows, set `HADAMARD_NATIVE_TEX=1` to use the installed native TeX engine. Paper and proof-source hashes are recorded separately. Text files use LF line endings; `.gitattributes` keeps Git's text representation consistent. Historical artifacts retain their original bytes.

The repository is published on GitHub on `main`. Use the full immutable commit hash when requesting verification. The manual **Official Palomar mechanical preflight** GitHub workflow invokes a pinned official verifier for a chosen configuration; it does not register or submit the project. [submission/PALOMAR_ENTRIES.txt](submission/PALOMAR_ENTRIES.txt) lists the available entries. Local preparation, official mechanical verification, editorial review, and registry acceptance are distinct steps. The prepared CI does not globally disable AppArmor restrictions.

## Dependencies, licenses, and historical material

The nine pinned dependency revisions and their permissive license evidence are recorded in [submission/mathlib-licenses.json](submission/mathlib-licenses.json). See [DEPENDENCIES.txt](DEPENDENCIES.txt) and [LICENSE](LICENSE). Public papers are cited as mathematical sources; access to a paper is not treated as permission to redistribute its code.

Original project code is Apache-2.0, except for the explicitly attributed BSD-3-Clause translation of the Archive of Formal Proofs residue-matrix construction. Its author notices, license, and provenance are preserved in `CompletionCyclicExistence/`.

The `artifacts/` directory preserves earlier research proofs, experiments, data, and PDFs. It overlaps companion projects and is historical reference material, not an expansion of the current formalized claims. Its notice and snapshot describe that distinction. Generated `.lake/` files are disposable local build state and are excluded from Git.

## Completion-theory build notes

The small-defect results explicitly retain the classical real-extension input.
The exact candidate-test budget is formalized; the separate scalar-operation
complexity discussion remains outside the compared algorithm theorem.

Finite repair verification: RepairChallenge and comparator-repair.json specify the full one-row augmentation and odd-feasibility results independently. CompletionRepair contains original kernel-only finite certificates, exact integer elimination, and universal bounds. The repair comparison has no definition holes. Run all groups registered in submission/comparison-groups.json.

Order20 code-trap verification: CompletionCodeTrap contains the complete unconditional finite-example proof, including exact sign-class counts, the self-dual pivot neighbor, and the optimal two-row escape for arbitrary real Hadamard matrices. CodeChallenge/comparator-codes.json supplies an independent mathlib-only specification with zero definition holes. Mathematical data are in submission/code-trap-data.json; all proof code is original Apache-2.0 and uses the pinned mathlib dependency. The supplementary full compatibility histogram is a separate computational artifact.

UNCONDITIONAL CYCLIC EXISTENCE INTEGRATION
CompletionCyclicExistence/ contains the three-mod-eight three-square theorem,
fixed-sum four squares and actual uniform/skew cyclic coefficient constructions.
CyclicExistenceChallenge supplies eleven independent theorem targets and nine
concrete definitions. Its public group is comparator-cyclic-existence.json.
The current integration passed full local builds, bounded axiom audits and
all nine local comparison groups on one source snapshot. Full readiness also
requires the remaining principal proofs and registry checks.

The executable build configuration is lakefile.lean. submission/lake-catalogue.toml is the
machine-readable library catalogue; scripts/check_lake_catalogue.py checks their
agreement. The runtime plugin is restricted to the four libraries that need it.
On the first build, Python3 and the pinned Lean leanc compiler build licensed
mathlib elaborator support under .lake/cyclic-native. This can take substantial
time and disk space. Compilation uses at most two workers and is resumable.
The generated libraries initialize the elaborator; they supply no mathematical
axioms. New proof modules and the axiom-profile reader retain the 1GiB limit.
The existing name-only export preflight keeps its 4GiB diagnostic cap.
All proofs still require standard-axiom audits and independent kernel checks.

Windows runtime/build integration has been exercised locally. Linux handling
is implemented but has not yet been exercised on a clean Linux host. No Linux
registry or Palomar success is inferred. Preserve all license files if copying
sources; .lake generated objects and libraries are disposable and not submitted.

In submission/cyclic-existence-source-provenance.json, the sources array names
and hashes the packaged proof files. The foundationSources array preserves the
original pilot input receipt; its .lake residue-file path is historical. The
public build imports CompletionCyclicExistence/ResidueMatrix.lean and the
existing packaged CompletionTheory/CompletionCharacter foundations.

The bounded axiom audit reads Lean4.35's compiler-generated transitive axiom
cache from each defining olean, the same cache used by imported #print axioms.
It binds source and olean hashes, compares all20cyclic profiles with the stock
command at1GiB, and tests axiom-free, forbidden-builtin and missing-name cases.
The small diagnostic reader uses the pinned type-erased Lean extension format;
it declares no mathematical theorem. Comparator checks actual proof terms with
both independent kernels as a separate required stage.


## Theorem labels and public coverage

Each identifier below refers to a principal manuscript result. “Public proof” means its named Lean declarations are included in the configured public proof set; “Excluded” means the whole result is outside that set. Supporting lemmas do not change an excluded result’s status.

| Identifier | Mathematical statement | Coverage |
|---|---|---|
| `CT-01-01` | Uniform large-energy existence | Public proof |
| `CT-01-02` | cyclic-hermitian-norms corollary 2 | Public proof |
| `CT-01-03` | Odd multiplier closure | Public proof |
| `CT-01-04` | Skew-character large-energy region | Public proof |
| `CT-01-05` | A zero-aligned character ansatz is impossible | Public proof |
| `CT-02-01` | Sharp floor in the full character span | Public proof |
| `CT-02-02` | Only three prime lengths can reach the binary boundary | Public proof |
| `CT-03-01` | Exact residual criterion | Public proof |
| `CT-03-02` | Anchor enumeration | Public proof |
| `CT-03-03` | An elementary defect-two completion | Public proof |
| `CT-04-01` | Eight missing rows can already be fatal | Public proof |
| `CT-05-01` | Odd-block exchange budget | Public proof |
| `CT-05-02` | Cheap augmentation versus exact linear completion cost | Public proof |
| `CT-06-01` | Cube intersections through information coordinates | Public proof |
| `CT-06-02` | Maximum cube intersections are duplication spaces | Public proof |
| `CT-06-03` | A three-row deletion barrier | Public proof |
| `CT-07-01` | Tensoring cannot amplify the exchange cost upward | Public proof |
| `CT-07-02` | A general span-rigidity criterion | Public proof |
| `CT-07-03` | Preservation under half-overlap pair structure | Public proof |
| `CT-07-04` | tensor-exchange-barrier corollary 4 | Public proof |
| `CT-08-01` | Weighted odd-witness budget | Public proof |
| `CT-08-02` | The first possible parity deficit is eight | Public proof |
| `CT-08-03` | Saturated-lattice alternative | Public proof |
| `CT-09-01` | Exact one-row augmentation | Public proof |
| `CT-09-02` | Augmentation can destroy odd integer feasibility | Public proof |
| `CT-09-03` | Rounding defect | Public proof |
| `CT-10-01` | Exact modular count with a column-pair correction | Public proof |
| `CT-11-01` | The row correction at orders $4\bmod8$ | Public proof |
| `CT-11-02` | Exact boundary correction | Public proof |
| `CT-12-01` | Two-parity rigidity | Public proof |
| `CT-12-02` | Five rows remove compatibility tests | Public proof |
| `CT-12-03` | Exact code pivot | Public proof |
| `CT-13-01` | Finite certified example | Public proof |
| `CT-13-02` | Elementary tensor persistence | Public proof |
| `CT-14-01` | Exact restricted-neighbor incidence count | Public proof |
| `CT-14-02` | A modular pool splits into two codes | Public proof |
| `CT-15-01` | Weighted-grid classification | Public proof |
| `CT-15-02` | Exact compatibility and optimal retained-space repair | Public proof |
| `CT-16-01` | Exact first and second completion moments | Public proof |
| `CT-16-02` | Exact expected sign count along the walk | Public proof |
| `CT-17-01` | Exact third-moment certificate | Public proof |
| `CT-18-02` | Uniform power-of-two buffer | Public proof |
| `CT-19-01` | An exact residual parameterization | Public proof |
| `CT-19-02` | A rounding threshold for real completions | Public proof |
| `CT-20-01` | A signed complex-structure criterion | Public proof |
| `CT-20-02` | Exact criterion and quantitative separation | Public proof |
| `CT-21-01` | Forced block structure | Public proof |
| `CT-21-02` | All sign fillings in quadratic time | Public proof |
| `CT-22-01` | The only possible component sections | Public proof |
| `CT-22-02` | Conference conversion | Public proof |
| `CT-22-03` | Exact real feasibility and solution topology | Public proof |
| `CT-22-04` | A sharper cardinality bound | Public proof |
| `CT-23-01` | An exact rank test for a two-column flat completion | Public proof |
| `CT-23-02` | Quaternary input needs no extra phase freedom | Public proof |
| `CT-23-03` | Automatic quaternary completion using a classical real input | Public proof |
| `CT-24-01` | A one-column extension gate through realification | Public proof |
| `CT-24-02` | Automatic completion in complex codimension at most three | Public proof |
| `CT-24-03` | An explicit finite exact algorithm | Public proof |
| `CT-24-04` | A precise codimension-four gate | Public proof |
| `CT-25-01` | A four-row support-moving switch | Public proof |
| `CT-25-02` | Two fixed-support row blocks cannot change feasibility | Public proof |
| `CT-26-01` | Syndrome census identity | Public proof |
| `CT-18-01` | Conditional quantitative half-frame | Excluded; see explanation above |
| `CT-26-02` | Complete improving-neighbor census for this code | Excluded; see explanation above |
