# Correlation Actualization Theory

**A nonperturbative matrix proposal with observer-dependent layers**  
Yohtaro Soga · Fourth version for review · 25 November 2026 · Provisional correspondence gawakkyu0603@gmail.com

[Article](main.pdf) · [Technical supplement](supplement.pdf) · [Guide to the six physical questions](reading-guide.md) · [Response to the review of Version 3](response.md) · [Earlier responses](response-v3.md) · [Compact article source](arxiv-source.tar.gz)

The falling observer's proper clock and the distant observer's radiation records motivate the CAT proposal. Ordinary matrix dynamics creates correlations. Gravity may select a layer irreversibly and change the modes available at a later contact. Requiring an exactly absent inward route for B led to a constraint on the allowed states and then to the doubled matrix parent. Its form applies across matrix sizes. The calculations here evaluate complete scattering blocks on declared sectors; a rank limit or a general physical measure and widespread formation of the required ports in natural collapse remain open. [Scope of the matrix law](parent-history.tex)

## Where to start

| Question | Article and evidence |
|---|---|
| What makes A's and B's continuations physically different? | [The fixed-network history law, article p. 6](main.pdf#page=6) and [the observer-specific domain and common receipt](supp-domains.tex) |
| Why does the device give 0.5376 when the selected route closes exactly? | [Common source and the two missed preparations, article p. 8](main.pdf#page=8), [receiver and inclusive decoding](supp-revision.tex) |
| Does matter have the same real-time sign as the parent? | [Physical scalar and wave operator, article p. 9](main.pdf#page=9) and [signed calculation](evidence/workspace/code/cat_domain_calibration.py) |
| Can an ordinary detector mimic a return? | [The proposed observable, article p. 13](main.pdf#page=13), [900-shot protocol and assumptions](supp-calibration.tex) and [operating probabilities](evidence/workspace/verification/cat-domain-calibration-results.json) |
| Which other matrix theories or astronomical observations constrain CAT? | [Matrix comparison and geometry](geometry.tex), [conditional tests and their alternatives](tests.tex) and [the regimes realized together](supp-calibration.tex) |
| Where are the full calculations? | [English guide to 91 results](evidence/result_guide.md), [result-to-file and page mapping](evidence/experiments.json), [scopes of 56 primary identifiers](evidence/citation-audit.json) |

## Reproducing the calculations

Extract the entire ZIP to a writable directory and open a shell in that directory. All evidence, including the seven calculation-sheet PDFs referenced by the guide, is local. The individual research notes are in Japanese. Each result has an English summary. The manifest records a SHA-256 for every payload file. [Manifest](manifest.json)

**Windows x64.** The offline PowerShell entry point uses the bundled CPython 3.14.7, native scientific packages and Lean 3.51.1.

~~~powershell
.\review-offline.ps1 -Action check
.\review-offline.ps1 -Action numerical -Names 'cat_domain_calibration'
.\review-offline.ps1 -Action lean -Names 'CATObserverDomain'
.\review-offline.ps1 -Action study -Names 'RES-0183','cat_domain_calibration'
~~~

**Linux x86-64.** Use CPython 3.12 on a glibc system compatible with the bundled wheels (glibc 2.28 or later). The tested interpreter was CPython 3.12.3 on glibc 2.39. The wrapper verifies and installs the local wheels to a private cache. The formal check uses the bundled Linux binary and mathlib. [Pinned Linux distributions](evidence/python-linux/distributions.json)

~~~sh
bash review-linux.sh check
bash review-linux.sh numerical cat_domain_calibration
bash review-linux.sh lean CATObserverDomain
bash review-linux.sh study RES-0183 cat_domain_calibration
~~~

Omit the names on the numerical or Lean command to run the full default selection. The nine programs compare complete reference outputs, including 59 data groups and 1,195 floating-point values. The new program contributes five groups and 36 values. The ten selected Lean modules contain 365 theorem or lemma declarations; 13 belong to the [new module](evidence/workspace/verification/CATObserverDomain.lean). All 85 research Lean files are supplied. The nine previously checked modules and eight previously run drivers are byte-for-byte identical to their reviewed second-version sources. The third-version additions were run on Windows and Linux. The independent Version 3 review reports repeating all nine drivers and ten modules on Linux. For this editorial edition the archived computational inputs and formal sources were compared by SHA-256 with that reviewed version. The [verification record](evidence/verification.json) gives precise scopes and environments. The [comparison rules](numeric_policy.py) distinguish tiny nonzero quantities from numerical zeros.

## Rebuilding the paper

With pdfLaTeX and Poppler installed, run the following command in Bash. The script resolves references in three passes. The compact arXiv-style source also builds the article in isolation. The complete ZIP additionally contains the supplement, responses, inputs, programs and proof sources.

~~~sh
bash build.sh main supplement
~~~

[Article LaTeX](main.tex) · [Supplement LaTeX](supplement.tex) · [Source of the routing diagram](make_figure.py)

