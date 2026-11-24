# CAT v4: scientific consistency QA and resolution record

## Scope and current assessment

This record covers the three English guides for specialists, STEM students, and general readers included in this repository, and their 26 figure types. The sources are the [main paper](../paper/main.pdf), [technical supplement](../paper/supplement.pdf), TeX sources, response, and verification records for **Yohtaro Soga, Correlation Actualization Theory, Version 4, 25 November 2026**.

**The current publication consists of three English articles.** At the author's instruction on 25 November 2026, the three Japanese articles and Japanese public navigation were removed for readability. The English source fragments and generated article contents were preserved, with generation, link, and sitemap checks associated with the publication change. The language change itself is not a new scientific review.

The two improvements identified in the initial four-page QA were resolved during the subsequent six-page Japanese/English editing stage. The scientific checks below retain that history and identify the conditions and explanations that remain in the current English articles. They do not certify the readability of the removed Japanese pages.

This is editorial scientific QA intended to keep the explanations faithful to the paper's assumptions, results, and open questions. It does not constitute a new full review, independent reruns of all 91 research results, observational reanalysis, external journal peer review, or acceptance for publication. The original initial-QA record is preserved in the historical appendix, separately from the current resolution status.

| Audience | Source fragment | English-article figures | English-article display equations | Local / astronomy-cosmology test rows |
| --- | --- | ---: | ---: | ---: |
| Specialists | [English](../../../../site-src/content/expert-en.html) | 8 | 12 | 11 / 12 |
| STEM students | [English](../../../../site-src/content/student-en.html) | 9 | 8 | 11 / 12 |
| General readers | [English](../../../../site-src/content/general-en.html) | 9 | 0 | 11 / 12 |

[COVERAGE.md](COVERAGE.md) maps the main-paper sections and central supplement themes to the guides. The reading levels need not have identical equation counts or word counts. The same assumptions, results, and limits are retained across the current three articles.

## The two initial findings and their resolution

| Initial finding | Implemented response | Current verification location |
| --- | --- | --- |
| The specialist article did not explicitly state the pure-initial-state condition for the return rate `Σp_z²` | Both Japanese and English versions were supplemented with the pure initial state, orthogonal charge groups, reversal of each group's isometry, and projection of the whole register onto its initial state. This was distinguished from the logical-qubit return rate `1−p/2` in a separate setup | `expert-readout`: [English](../../../../site-src/content/expert-en.html#expert-readout). Original definition: opening of [tests.tex](../paper/tests.tex) |
| The student article grouped the supplement's 11 local and 12 astronomy/cosmology tests, leaving some without individual descriptions | The explanations of principles were preserved, and reference appendices containing all 23 were added in Japanese and English. Appendices with the same counts were also added to the general-reader guides | Student `student-test-reference`: [English](../../../../site-src/content/student-en.html#student-test-reference). General-reader `tests-reference`: [English](../../../../site-src/content/general-en.html#tests-reference). Original list: [supp-tests.tex](../paper/supp-tests.tex) |

Reading `expert-tests`, `student-test-reference`, and `tests-reference` from the HTML confirmed **11 local rows and 12 astronomy/cosmology rows in each of the current three English pages**. The student article also uses row identifiers `L01`–`L11` and `A01`–`A12`. These tables describe proposed tests for specified preparations and branches; they do not claim that one apparatus or vacuum satisfies every condition simultaneously.

## Scope of checks on values and assumptions

The following items were compared with the original paper. Simple arithmetic was recalculated, but this was not a new execution of all published numerical studies.

| Item | Checked values and scientific distinctions | Principal original sources |
| --- | --- | --- |
| Exact closure | `N_in = max(1+m−n,0)` for the specified spherical port. The checks distinguish zero at a negative unit difference, the number of spatial modes from the internal code dimension, and the condition for closing every port | [main.tex](../paper/main.tex), [supp-domains.tex](../paper/supp-domains.tex) |
| Joint probabilities from one preparation | `r = 3/4`, `p = 0.64`, B closure 0.5376, and joint A/B occurrence 0.196608. A is actual absorption at both endpoints and excludes agreement between two empty records | [joint-experiment.tex](../paper/joint-experiment.tex) |
| Recovery and carriers | Conditional recovery on closed histories is distinguished from all-history fidelity 0.6532. Photon-pair, graviton-pair, and core weights 1/2, 1/3, and 1/6 describe alternative carriers, not three copies. Accessibility is a condition | [joint-experiment.tex](../paper/joint-experiment.tex), [supp-revision.tex](../paper/supp-revision.tex) |
| Causal deadlines | 5.44 ms, 20.66 μs, and 1.003 μs refer to the specified 10-solar-mass example. They use different clocks and endpoints; an arrival margin alone does not guarantee successful receipt | [main.tex](../paper/main.tex) |
| Return and calibration | Distinguish the whole-register `Σp_z²` from the logical-qubit `1−p/2`, and the joint preparation's `p = 0.64` from a separate design's target `p = 8/9`. Checked: 900 trials, upper bound 0.659582 / lower bound 0.970227, uniform `Δ ≤ 0.01` over every allowed state and flag, dark counts `d ≤ 0.01`, and withholding a decision at counts 86–87 | [tests.tex](../paper/tests.tex), [supp-calibration.tex](../paper/supp-calibration.tex) |
| Clocks, metrics, and gravity | Distinguish the ten matrix components from matrix size N, finite clocks from rank limits, and a metric read from a nondegenerate four-dimensional H from the general Einstein equations. The specified wave's `Tr K = 0` is not generalized to all matter or full stability | [parent-history.tex](../paper/parent-history.tex), [geometry.tex](../paper/geometry.tex) |
| Vacua and radius | 48,055,489 → 20,597 → 115 → 49 → 41 are different filtering stages for the specified square-torus orientifold with fixed coupling and a tadpole bound. They do not give the number of all CAT vacua, full stability, or a determination of the common radius | [geometry.tex](../paper/geometry.tex) |
| Astronomy and cosmology tests | Checked the names, comparisons, and necessary conditions of all 23 tests. Pantheon+, DESI, and similar results are treated as observational values used by the original paper, retaining limitations concerning preparation on the same branch, uniformity, low redshift, and selection effects | [supp-tests.tex](../paper/supp-tests.tex), [supp-constraints.tex](../paper/supp-constraints.tex), [tests.tex](../paper/tests.tex) |
| Computational evidence, authorship, and AI | Records cover 9 drivers, 59 groups, and 1,195 floating-point values, plus 10 selected Lean modules and 365 declarations. The v3 reruns are distinguished from v4's inherited identity and limited checks. AI technical review is not treated as external peer review | [verification.json](../paper/evidence/verification.json), [response.md](../paper/response.md), [closing.tex](../paper/closing.tex) |

The arithmetic checks found the four joint-table cells to be `[3072,1728,5328,5497]/15625`, or `[19.6608,11.0592,34.0992,35.1808]%`, summing to 1. The checks also confirmed `0.75×0.64 + 0.25×0.64×0.36 = 0.5376`, `0.75×0.64³ = 0.196608`, and `0.5376 + 0.4624/4 = 0.6532`. The bounds obtained from the calibration's binomial inversion and formulas agreed with the displayed rounded values 0.659582 / 0.970227.

## Figure revision history

The 26 types in the shared [figures.py](../../../../site-src/figures.py) were compared with the original paper and figure specifications. Numerical corrections were unnecessary, but the following changes corrected the direction of allowed-range shading and made the conditions explicit.

| Figure or explanation | Resolved point |
| --- | --- |
| Bands in `expert-readout-design` | Shade CAT from 0 to its upper bound and the ordinary model from its lower bound to 1; explicitly show `≤` / `≥`. Corrected the previous depiction that shaded the ordinary model from 0 to its lower bound |
| `expert-joint-probabilities` | Label A as actual absorption at both endpoints and B as relative charge −1. Add a dedicated caption stating that two empty records are excluded from event A |
| `student-geometry`, `expert-geometry-ladder` | Add `det H ≠ 0; d = 4` and the assumptions needed to construct the metric |
| Caption for `expert-readout-design` | State target `p = 8/9`, uniform `Δ ≤ 0.01` over every allowed state and flag, and the independent dark-count bound `d ≤ 0.01` |
| `expert-vacuum-constraints` | Identify the counted object as the specified square-torus orientifold with fixed coupling and a tadpole bound |
| `general-evidence` | Add “decoding” to the English version to match the Japanese version at that editing stage |
| `expert-closure-count`, `student-domain`, `general-route` | Add captions explaining that the multiple lines are allowed spatial modes, not copies of an unknown state C |
| `expert-history-instrument`, `student-channel`, `general-records` | Connect the figure's outcome z to its use in the later port operation W through the caption |
| General-reader page, `correlations` | Replace the “stacked sheets” explanation with a sentence in both languages matching the actual frame-and-branch diagram |

At the earlier Japanese/English stage, 26 figures × 2 languages, or 52 SVGs, were checked. The current publication includes the 26 English figures. Checks covered numerical values, alternative branches versus copies, physical inputs versus conditional consequences, and proposed designs versus observed values. `general-source` explains recovery from a carrier on a closed history; it is not presented as a diagram of the complete common-source apparatus.

## Recorded mechanical checks and their limits

The counts below describe CAT v4 and the recorded site configuration at the transition to English-only publication. Site-wide page counts may change when other papers are added.

| Check | Recorded scope or method |
| --- | --- |
| Published pages | 7 HTML pages in total: the shared entry, English index, field entry, paper entry, and three English articles |
| Body preservation | Compare before/after SHA-256 hashes of the three English source fragments and the article portions of generated HTML |
| Display equations and figures | Preserve 12 equations / 8 figures for specialists, 8 / 9 for students, and 0 / 9 for general readers |
| Test lists | 11 local rows and 12 astronomy/cosmology rows per article; include the student and general-reader appendix anchors |
| SOURCE_ROOT references | Map 3 specialist, 27 student, and 9 general-reader occurrences, 39 in total, to the original sources |
| Generation, links, and equations | Check all pages for the configured languages, IDs, TL;DR, figure descriptions, KaTeX, and local and original-source links |
| Search correspondence | Check canonical URLs, English self-references, the entry's x-default, and the sitemap containing 7 HTML pages + 2 PDFs |
| Original-PDF identity | Check that the SHA-256 hashes of the main paper and supplement match the v4 originals |

See the shared [verification.json](../../../../site-src/verification.json) for execution results. This is a site-wide generated report, whose scope can include other papers as the site grows. The English-only transition does not establish a new full review, a complete rerun of the numerical studies, or HTTP retrieval and visual inspection of the published site. Structural and hash agreement is evidence of content preservation; it is not itself proof that the natural-language scientific explanations are correct.

## Historical appendix: original initial-QA record

The following is the initial report on the four specialist/student pages, preserved verbatim in Japanese. Statements about room for improvement or the pages being unedited describe that earlier stage. Current resolutions are documented above in “The two initial findings and their resolution.” This quoted record is historical evidence, not an active Japanese edition of the maintenance documentation.

Original record SHA-256: `ed4d9faffd2b75352c3a2bda196695a4f543cb511407782fc605df65f60c89be`.

<details>
<summary>Open the initial four-page QA record (verbatim Japanese archive)</summary>

# 第4版・専門家／学生向け解説の科学的整合性 QA

対象：`expert-ja.html`、`expert-en.html`、`student-ja.html`、`student-en.html`。原資料は `CAT-review-v4/CAT-review` の主論文・補遺 TeX、README、応答書。全節を読み、科学的意味、数値の前提、日英対応を照合した。対象 HTML は編集していない。これは解説と原資料の整合性検査であり、原論文の全結果の独立再計算・外部査読・掲載承認ではない。

## 判定

**重大な科学的齟齬、重大な日英差、実測と提案の取り違えは検出しなかった。** 公開を妨げる科学的誤りは確認していない。以下の条件明示と網羅性について補強の余地がある。

| 箇所 | 指摘と根拠 | 推奨対応 |
|---|---|---|
| 専門家版 JA/EN `#expert-readout` 冒頭 | 帰還率 `Σ p_z²` は原 `tests.tex` 冒頭で、**純粋な初期状態**が直交電荷群へ分かれ、各群の isometry を戻し、元状態へ射影する設定の式。専門家解説では純粋性が明示されず、任意の混合状態について同式が成り立つようにも読める。学生版 `#student-test` は条件を明記済み。 | 「純粋な初期状態について／For a pure initial state」と、可能なら元状態への射影を補う。式や数値の修正は不要。 |
| 学生版の検証案の網羅性 | 主要主題は揃うが、補遺 `supp-tests.tex` の **11 局所試験＋12 天文・宇宙論試験**は全件の個別説明ではない。特に、共鳴時間、中間スピン軸、集合／個別符号、四受信器、補償、二ボソン、四準位参照、空区間などの局所試験が集約され、天文では反復潮汐と inspiral の位相予算が個別項目になっていない。専門家版は全23件を含む。 | 「内容漏れなく」の要件を厳密に満たすなら、本文を維持して短い参照表を追加するか、全件の表へ明示リンクする。科学的誤りではなく詳細範囲の差。 |

## 重点照合で問題がなかった点

| 項目 | 確認内容・原資料 |
|---|---|
| 厳密閉鎖 | 内向きモード数、負の単位差で零、空間一モードと内部量子状態の区別、非正則成分・別種・別ポートによる再開を明示。`parent-history.tex`、`supp-domains.tex`、`supp-revision.tex`。 |
| 因果期限 | 5.44 ms、20.66 μs、1.003 μs を別の時計・区間として扱い、古典的 null 地平面から新たに受信して通常の外向き信号を出す問題を区別。`parent-history.tex`。専門家版の表は右端欄まで含めると期限の意味が明瞭。 |
| 共通準備と回復 | 吸収 0.64、源の重み 0.75、閉鎖 0.5376、同時成立 0.196608、全履歴忠実度 0.6532、別条件の 13/16 と 23/32 が正しく区別される。回復は複製ではなく、利用可能な放射・core・flag を含む条件付きチャネル。`joint-experiment.tex`、`supp-revision.tex`。 |
| 戻り実験 | 理想的な全レジスター帰還と論理 qubit の読み出し、設計吸収 8/9 と先の 0.64、900 試行、誤差・暗計数の各 0.01 上限、86–87 回の保留を混同していない。専門家版は較正誤差予算、自動再試行なし、較正通過率も記載。`tests.tex`、`supp-calibration.tex`。 |
| 行列・時計・幾何 | 行列成分数と行列サイズ、有限時計、実時間符号、伝播円錐と Einstein 方程式、特定波動解と一般解を区別。非摂動的という語を全ランクの量子論完成に拡張していない。`parent-history.tex`、`geometry.tex`、`supp-domains.tex`。 |
| 真空・宇宙論 | 49 は限定フラックス列挙での線形化固定であり全真空数ではない。半径の復元力、軽いスカラーの制約、Pantheon+ の仮定、DESI の事後選択した二点診断、イベント喪失と強度減衰を区別。`geometry.tex`、`tests.tex`、`supp-calibration.tex`、`supp-constraints.tex`。 |
| 天文・既存実験 | 専門家版の全23試験は補遺の条件に対応。ナトリウム粒子干渉、192/128 モード、Cassini、38.6 μm、SPARC 68/56/42 等も補遺の表現・数値に対応する。これらは原論文が用いる観測値として記述される。`supp-tests.tex`、`supp-constraints.tex`。 |
| 証拠と AI の位置づけ | 9 ドライバー・59 群・1,195 浮動小数点値、選択10 Lean モジュール・365宣言を、自然界の証明とせず、編集改訂の第4版で全スイートを新規実行したとも述べていない。AI 技術レビューを外部の学術誌査読と扱っていない。`README.md`、`response.md`、`closing.tex`。 |

数値の簡単な独立算術照合：`0.75×0.64 + 0.25×0.64×0.36 = 0.5376`、`0.75×0.64³ = 0.196608`、`0.5376 + 0.4624/4 = 0.6532`。日英の数値列と節構成も比較し、語順や数字の綴りによる差を除いて重要な対応不一致は認めなかった。


</details>
