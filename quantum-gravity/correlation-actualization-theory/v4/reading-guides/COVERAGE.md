# CAT v4: coverage of the three English reading guides

This record maps the specialist, STEM student, and general-reader guides to their original sources: **Yohtaro Soga, Correlation Actualization Theory, Version 4, 25 November 2026**. It does not revise the paper, calculations, or evidence files.

At the author's instruction on 25 November 2026, the three Japanese articles were removed from publication, together with their source fragments and generated HTML. The three English reading levels remain the publication format for these guides. That change did not revise the scientific content of the English articles.

## Roles of the three English guides

| Audience | English source fragment | Explanatory focus |
| --- | --- | --- |
| Specialists | [English source](../../../../site-src/content/expert-en.html) | Action and signs, instruments, kernels and domains, recovery conditions, clocks and metrics, and all protocols with their applicability assumptions |
| STEM students | [English source](../../../../site-src/content/student-en.html) | States and channels, linear algebra, spatial modes and internal codes, and a step-by-step account from preparation to observation |
| General readers | [English source](../../../../site-src/content/general-en.html) | Observer records, whether routes exist, topology and information, and clocks and geometry, using figures and concrete examples while keeping the limits of analogies explicit |

All three reading levels cover the same research assumptions, results, and open questions. They span every section of the main paper and the central themes of the supplement. They do not reproduce the paper verbatim, rewrite every proof, or individually reproduce all 91 research records. The mathematical and example-level detail varies with the audience; operator details omitted from the general guide are not replaced with claims of empirically established universal laws.

Original sources: [main-paper PDF](../paper/main.pdf), [technical-supplement PDF](../paper/supplement.pdf), [original README](../paper/README.md), and [result guide](../paper/evidence/result_guide.md). Each guide also links to the relevant PDF pages or original sources.

## Main-paper mapping

The table cells identify existing anchors in the currently published English articles. The main-paper sources are in `quantum-gravity/correlation-actualization-theory/v4/paper/`.

| Original section or main theme | Original source | Specialists | STEM students | General readers |
| --- | --- | --- | --- | --- |
| Abstract and §1: A/B infall, incomparable records, and three additional postulates | `main.tex` | `expert-tldr`, `expert-question` | `student-tldr`, `student-question` | `summary-heading`, `two-observers`, `correlations` |
| §2.1: Tides, mediators, direct interactions, and causal contact | `main.tex` | `expert-law`, `expert-closure` | `student-choices`, `student-current` | `actions`, `matrices` |
| §2.2: Support floor, finite attenuation, and exact zero | `main.tex` | `expert-closure` | `student-channel`, `student-domain` | `routes` |
| §2.3: Line bundles on a sphere, signed inward dimension, and the all-port condition | `main.tex` | `expert-closure`, `expert-deadlines` | `student-domain` | `routes` |
| §3.1: Ten matrices, real-time signs, the BFSS clock quotient, and the material index and compensation | `main.tex` | `expert-law`, `expert-geometry` | `student-parent`, `student-current` | `matrices` |
| §3.2: Receipt instruments, routing, conservation laws, and double histories | `main.tex` | `expert-law`, `expert-closure` | `student-channel`, `student-history` | `correlations`, `actions`, `matrices` |
| Record coarse-graining on a fixed network, observer outputs, and the meaning of rank | `parent-history.tex` | `expert-question`, `expert-law` | `student-history`, `student-finite` | `matrices`, `recovery` |
| §4.1: Deadlines, arrival versus absorption, natural-collapse preparations, and failure examples | `main.tex` | `expert-deadlines` | `student-deadline` | `deadline` |
| §4.2: Reference entanglement, all carriers, amplitude versus intensity, and endpoints | `main.tex` | `expert-recovery` | `student-recovery` | `recovery` |
| A common two-pulse source, joint probabilities, and conditional recovery | `joint-experiment.tex` | `expert-example` | `student-example` | `recovery` |
| §5: Material finite clocks and clock-sector assumptions | `geometry.tex` | `expert-geometry` | `student-finite`, `student-geometry` | `clock-geometry` |
| §5.1: Scalar signs, principal-part density, the metric, and a specified vacuum Einstein wave | `geometry.tex` | `expert-geometry` | `student-geometry` | `clock-geometry` |
| §5.2: High curvature, bounce, excitations and stability, and underived vacuum transitions | `geometry.tex` | `expert-continuation` | `student-spacetime` | `vacua` |
| §5.3: A shared metric, orientation, triple overlaps, and smooth structure | `geometry.tex` | `expert-continuation` | `student-spacetime` | `clock-geometry`, `vacua` |
| §6: IKKT/IIB, BFSS/M, loop approaches, causal sets, CDT, and finite circular apertures | `geometry.tex` | `expert-comparisons` | `student-theories` | `matrices` |
| §6.1: Restricted flux counts, a common radius, one-loop cancellation, matter, and forces | `geometry.tex` | `expert-vacua` | `student-vacua` | `vacua`, `sky` |
| §7: Inversion, memory and revisits, and readout calibration | `tests.tex` | `expert-readout` | `student-test` | `return` |
| §7: Stars, polarization, radio, neutrinos, CMB, expansion and distances, and dark components | `tests.tex` | `expert-tests` | `student-sky`, `student-cosmology` | `sky` |
| §8: The meaning of a candidate theory, prior work, and conditions required in the same collapse | `tests.tex` | `expert-comparisons`, `expert-evidence` | `student-theories`, `student-verification`, `student-glossary` | `next`, `evidence` |
| Appendix: Conditional Lean checks, analytic and experimental inputs, authorship, and AI use | `closing.tex` | `expert-evidence` | `student-verification` | `evidence`, `sources-heading` |

## Main themes of the technical supplement

| Supplement content | Original source | Specialists | STEM students | General readers |
| --- | --- | --- | --- | --- |
| Contact selection, reversible tides, continuous comparison, finite penalties, and agreement with the ordinary exterior | `supplement.tex` §1 | `expert-law`, `expert-closure` | `student-choices`, `student-domain`, `student-current` | `actions`, `routes` |
| Finite links, receipt effects, radiation capacity, and multiple visits | `supplement.tex` §2 | `expert-closure`, `expert-recovery`, `expert-readout` | `student-domain`, `student-recovery`, `student-test` | `routes`, `recovery`, `return` |
| Principal-part density, central commutators, and curved matrix sectors | `supplement.tex` §3 | `expert-geometry` | `student-parent`, `student-geometry` | `clock-geometry` |
| Preparation through readout: Signs, indices, recoil, and the four-bit distribution | `supp-revision.tex` | `expert-law`, `expert-example`, `expert-recovery` | `student-parent`, `student-current`, `student-example`, `student-recovery` | `matrices`, `recovery` |
| Physical output spaces, the absence of simultaneous copies, shared records, and outcome-labelled order | `supp-domains.tex` | `expert-question`, `expert-law` | `student-history`, `student-domain`, `student-example` | `actions`, `recovery` |
| Positive and negative controls, Pauli X, a uniform error bound over all states, and 900 trials | `supp-calibration.tex` | `expert-readout` | `student-test` | `return` |
| What was realized simultaneously in the same preparation | Comparison table in `supp-calibration.tex` | `expert-geometry`, `expert-vacua`, `expert-evidence` | `student-vacua`, `student-verification` | `vacua`, `evidence`, `next` |
| The 11 local and 12 astronomical protocols | `supp-tests.tex` | `expert-tests`: The [English list](../../../../site-src/content/expert-en.html#expert-tests) includes all 23, with equations and conditions | `student-test-reference`: The [English appendix](../../../../site-src/content/student-en.html#student-test-reference) includes all 23 and connects them to the principles explained in the article | `tests-reference`: The [English appendix](../../../../site-src/content/general-en.html#tests-reference) gives the comparisons and necessary conditions for all 23 |
| Choice of action, duality, existing observations, and arbitrary dark components | `supp-constraints.tex` | `expert-comparisons`, `expert-tests` | `student-theories`, `student-cosmology` | `matrices`, `sky` |
| Closest prior research and limits on originality | `supp-scope.tex` | `expert-comparisons` | `student-theories` | `matrices`, `next` |
| Evidence classification, 91 individual summaries, and negative results | `supp-scope.tex`, `supp-results.tex` | `expert-evidence` | `student-verification` | `evidence`, `sources-heading` |

At the earlier Japanese/English stage, the test lists were checked at each reading level in each language for 11 local rows and 12 astronomy/cosmology rows. All three current English guides retain these rows. The student and general-reader appendices supplement the explanations of principles; they do not reproduce the operators, derivations, and numerical records for every item.

Analogies in the general guide provide an entry into the corresponding mathematics. “Layers” are not observed parallel universes, “route count” is not a qubit count, and “inversion” does not mean that control of the entire actual environment has been achieved. Proofs, raw data, and detailed algorithms remain in the original PDFs and evidence index.

## Important values and their indispensable conditions

| Result or value | Required conditions or interpretation | Conclusion not established |
| --- | --- | --- |
| `N_in=max(1+m−n,0)`; zero at relative degree −1 | A specified holomorphic port on a sphere, with the physical species, internal bundle, and aperture specified | Unconditional closure of all black holes, including other species and ports |
| `p=0.64, r=3/4`; B closure 0.5376; joint occurrence 0.196608 | The same two-pulse preparation; A requires actual absorption at both endpoints; B has negative relative charge | A closure rate for astrophysical populations, two simultaneous copies, or closure on every trial |
| Recovery on closed B histories; all-history fidelity 0.6532 | The specified qubit, photon pair, graviton pair, and core, with the required accessibility | Resolution of the information problem for arbitrary collapse or every evaporation history |
| 5.44 ms, 20.66 μs, 1.003 μs | A specified orbit for 10 solar masses, two proper clocks, and different endpoints | A single time budget on the same clock, or guaranteed receipt |
| `Σp_z²`; `w²+(1−w)²` for two groups | A pure initial state and orthogonal charge groups; reverse each group's isometry and project the **whole register** onto its initial state | Applicability of the same expression to arbitrary mixed states, or identity with the logical-qubit quantity `1−p/2` or an astronomical echo amplitude |
| Readout upper bound 0.659582 / lower bound 0.970227; at most 900 trials | A separate design with target p=8/9, positive and negative calibration, all-state Δ≤0.01, dark counts d≤0.01, and independent stationary trials | An effect already achieved in an actual gravitational experiment, or an error probability based on the signal tail alone |
| `Tr K=0` for a specified wave | One vacuum Einstein wave read by a material probe | The Einstein equations for general matter, a common cone for every species, or full stability |
| 115 flux orbits, 49 with linearized fixing, and 41 with O3 saturation | A particular orientifold with fixed coupling/tadpole, the primitive condition, and a finite quotient | The number of all CAT vacua or of realistic, fully stable vacua |
| 59 groups and 1,195 floating-point values; 365 declarations | Reported v3 reruns of 9 selected drivers and 10 selected modules; v4 inherits identity and has limited checks | A new independent rerun of all 85 files, or empirical proof of the physical inputs |

## Scope and preservation of the three English guides

- The specialist, STEM student, and general-reader articles address the same assumptions, results, and open questions. The amount of explanation, vocabulary, and mathematical detail varies with the audience.
- For CAT v4, the specialist article has 12 display equations, the STEM article has 8, and the general-reader article has 0 standalone display equations. Their figure counts are 8, 9, and 9, respectively.
- When the Japanese articles were removed, the English source fragments and the article portions of the generated HTML were checked by hash against their pre-change versions. Shared navigation, including language switching, was changed.
- This record does not claim a new full review of the manuscript's mathematics, numerical research, or observations, or a new observational reanalysis. The explanations rely on the scope explicitly stated in Version 4.

## Original-source link checks

Checked directory: `physics/quantum-gravity/correlation-actualization-theory/v4/paper/`. Each `{{SOURCE_ROOT}}/…` reference in a source fragment was mapped to an actual file inside that directory.

| Source fragment | SOURCE_ROOT occurrences | Distinct destinations | Missing destinations |
| --- | ---: | ---: | ---: |
| expert-en.html | 3 | 3 | 0 |
| student-en.html | 27 | 13 | 0 |
| general-en.html | 9 | 7 | 0 |

No incorrect original-source path was found among the 39 occurrences. All `#page=` anchors into the main paper and supplement were within pages 1–18. These checks establish the source-fragment destinations and page ranges. HTTP retrieval after GitHub Pages publication, layout, figure display, and equation rendering are separate generation/publication checks.

The article fragments are in the shared [site-src/content](../../../../site-src/content/) directory. Their source links lead to the original paper and supplement. The English figures and captions are defined in the shared [figures.py](../../../../site-src/figures.py). [SCIENTIFIC_QA.md](SCIENTIFIC_QA.md) records the initial findings, their resolution, and the scope of the numerical and assumption checks. The shared [verification.json](../../../../site-src/verification.json) records checks of generated structure, links, equations, and PDF identity; it is a site-wide report and can also cover other papers as the site grows.
