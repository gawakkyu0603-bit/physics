# Publication scope / 公開範囲

This document describes the contents, canonical URLs and provenance of the `physics` research repository and its GitHub Pages site.

## Identity and hierarchy

| Item | Value |
| --- | --- |
| Owner / Repository | `gawakkyu0603-bit/physics` |
| Repository URL | <https://github.com/gawakkyu0603-bit/physics> |
| Branch | `main` |
| Research hierarchy | `quantum-gravity/correlation-actualization-theory/v4/` |
| Manuscript | Yohtaro Soga, *Correlation Actualization Theory: A nonperturbative matrix proposal with observer-dependent layers* |
| Manuscript version and date | Version 4 · 25 November 2026 |
| Namespaced release tag | `cat-v4.0.0` |
| Release URL | <https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0> |
| Pages source | `main` branch, `/docs` directory |
| Pages base | <https://gawakkyu0603-bit.github.io/physics/> |

The structure is **physics → field → paper → version**. Future research can add another field, paper, or version without treating CAT’s version number as the version of the whole repository. `tools/build_site.py` is the entry point for generating the reading site.

## English reading guides

The site entry point is `docs/en/index.html`. Current and future papers provide three complete English guides, one for each audience:

| Audience | English page path | Figures |
| --- | --- | --- |
| Specialists | `docs/en/quantum-gravity/cat/expert.html` | 8 |
| STEM students and graduates | `docs/en/quantum-gravity/cat/student.html` | 9 |
| General readers | `docs/en/quantum-gravity/cat/general.html` | 9 |

Public URLs use the Pages base followed by these paths with the leading `docs/` removed. Every guide begins with a TL;DR and covers the paper and supplement at its intended reader's level. The amount of explanation, vocabulary, equations and figures are adapted to the audience while preserving the assumptions, data meanings, conclusions and limitations.

Coverage extends from motivation and interaction choices through states, channels, physical domains, material currents, matrix dynamics, histories, deadlines, quantum recovery, the common-source fixture, clocks and finite sectors, geometry, shared spacetime, other theories, vacua and radius stability, laboratory and astronomical tests, cosmology, verification, and open questions. Reader-specific reference material links the testing proposals to the technical supplement.

Public repository, field, paper, and version READMEs are maintained in English; Japanese maintenance notes may remain. For every future paper, keep these three English audience guides, with a TL;DR first and complete, sufficiently detailed coverage of the paper and supplement. For this initial publication, after the repository, tag, Release assets, and Pages site have all been published and verified, make the one-time initial submission through Google and Bing and the corresponding Yahoo routes. A submission receipt does not establish actual search indexing. This request does not include periodic monitoring or repeated submission. See [the maintenance guide](../ADDING_PAPERS.ja.md).

These are companion explanations of the fourth version. They do not alter the original paper, create new physical evidence, or transform a conditional construction into an observed result.

## Original material and complete download

The version’s [verification statement](../quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) is the detailed provenance record.

| Distribution | Scope |
| --- | --- |
| Version directory’s `paper/` | 709 original files, 23,463,032 bytes, retained without changes |
| Release-only runtime payload | 33 original files, 287,543,228 bytes, from `evidence/lean-toolchain`, `evidence/python-linux`, and `evidence/python-win64` |
| Full publication ZIP | All 742 original files, 311,006,260 bytes of original expanded payload, under `CAT-review/`, plus notices outside that directory |
| GitHub automatic source archives | A snapshot of the Git tree; they do not include the Release-only runtime files |

The 33 omitted files are bundled runtime/dependency archives and metadata, **not newly generated execution outputs**. The full publication ZIP is a new wrapper preserving the individual original file bytes. Its checksum is therefore different from that of the original received ZIP.

Original received archive SHA-256:

```text
fad61f93e3915de81701d9ebe8f3326c8a66fbb23c1a16572ee8aac7609fa14f
```

Release assets are `CAT_v4_full_publication_bundle.zip`, the unchanged article and supplement PDFs, the compact article-source archive, and `SHA256SUMS`. Asset checksums describe the actual asset files; the original archive hash above is retained separately as provenance. Use the full bundle for the supplied offline reproduction wrappers and original full-package manifest check.

## Scientific interpretation and verification

CAT is presented as an unrefereed research preprint. Its finite constructions use specified ranks, clocks, preparations, physical ports, and accessible carriers. Exact closure at a constrained port does not establish closure at every inward port. The common-source example is a prepared flat fixture, not a generic collapsing star. The readout protocol is a proposed experiment, not an observed gravitational signal.

The unresolved tasks include a consistent quantum theory across rank and clock sectors, realistic matter and gravity in a stable vacuum, widespread natural preparation of the required ports, and recovery at the evaporation endpoint. The companion guides retain these distinctions.

The recorded Version 3 technical review reran nine selected numerical drivers and ten selected Lean modules on Linux. The numerical comparison covers 59 groups and 1,195 floating-point values; the selected formal modules contain 365 theorem or lemma declarations. Version 4 inherits this execution evidence through source-identity comparisons and includes a successful limited package check with 143 finite-link systems. **No full numerical/Lean-suite rerun during the Version 4 review is asserted.** See [VERIFICATION.md](../quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) for exact scopes and [the original verification record](../quantum-gravity/correlation-actualization-theory/v4/paper/evidence/verification.json).

Kernel-checked consequences retain their mathematical and physical inputs. They do not certify that the required ports, clocks, or instruments occur in nature. The archive includes negative results and unsuccessful preparations alongside successful conditional examples.

## Human contribution, AI, and rights

The manuscript identifies Yohtaro Soga’s concepts, exact-closure criterion, and research direction. Codex assisted with mathematical construction, literature searches, numerical and Lean code, checks, and drafting; separate AI-generated technical reviews prompted changes. These reviews are development evidence, not journal peer review or independent human-expert acceptance. The [original contribution statement](../quantum-gravity/correlation-actualization-theory/v4/paper/closing.tex) remains the source.

No new repository-wide license is assigned to the original CAT work. Existing third-party licenses and attribution requirements remain attached to their components. Read [RIGHTS.md](../quantum-gravity/correlation-actualization-theory/v4/RIGHTS.md) and [THIRD_PARTY_NOTICES.md](../quantum-gravity/correlation-actualization-theory/v4/THIRD_PARTY_NOTICES.md). The repository does not claim a DOI, journal acceptance, or an institution’s endorsement.

## 日本語の確認事項

リポジトリは `gawakkyu0603-bit/physics`、版タグは `cat-v4.0.0` です。階層は物理学全体から分野・論文・版へ進みます。Pagesは英語の共通入口と、専門家・学生・一般向けの英語3ページを備えます。各ページはTL;DRから始まり、前提知識に合わせて主論文と補足の全体を説明します。今後の論文紹介も英語3種類で提供します。

原版709ファイルはGit内で変更せず保持し、33個の実行環境・依存関係ファイルは完全ZIPへ残します。完全ZIPは原版全742ファイルを保持した新しい配布物で、元ZIPとはハッシュが異なります。原研究への一括した新規ライセンス許諾は行いません。

第3版での全選択スイート実行、第4版への同一性継承、第4版の限定検査を区別します。物理的仮定、条件付きの数学・数値結果、未実施の実験設計、未完成の一般理論を同列に扱いません。今後の追加も版を保持し、サイト生成は `tools/build_site.py` から管理します。
