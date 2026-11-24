# CAT 第四版：解説ページの科学的整合性 QA と対応記録

## 対象と現在の判定

対象は、このリポジトリに同梱する専門家・理工系学生・一般読者向けの日本語／英語、計6ページと、その26種類の図です。原資料は **Yohtaro Soga, Correlation Actualization Theory, Version 4, 25 November 2026** の[主論文](../quantum-gravity/correlation-actualization-theory/v4/paper/main.pdf)、[技術補足](../quantum-gravity/correlation-actualization-theory/v4/paper/supplement.pdf)、TeXソース、応答書、検証記録です。

**初回の4ページQAで挙がった2件の補強事項は解決済みです。** その後、一般向けを含めた6ページの試験一覧、数値と限定条件、日英の構造・出典・図の対応を確認し、下記の図説明も修正しました。確認した範囲で、未対応の重大な科学的齟齬や重要な日英差は見つかっていません。

これは、解説が原論文の仮定・結果・未解決事項を正しく伝えるための編集上の科学的QAです。新たな全面査読、91件の研究結果の独立再実行、観測データの再解析、外部の学術誌査読・掲載承認を意味しません。初回QAの原記録は末尾に保存し、当時の指摘と現在の解決状態を分けて示します。

| 読者 | 本文素材 | 各言語の図 | 各言語の表示式 | 局所／天文・宇宙論の試験行 |
| --- | --- | ---: | ---: | ---: |
| 専門家 | [日本語](content/expert-ja.html) / [English](content/expert-en.html) | 8 | 12 | 11 / 12 |
| 理工系学生 | [日本語](content/student-ja.html) / [English](content/student-en.html) | 9 | 8 | 11 / 12 |
| 一般読者 | [日本語](content/general-ja.html) / [English](content/general-en.html) | 9 | 0 | 11 / 12 |

主論文の各節と補足の主要テーマへの対応は [COVERAGE.md](COVERAGE.md) に記録しています。読者水準間で同じ数の式や同じ語数を要求するものではありません。同じ読者水準の日英では、仮定・結果・限界を保持します。

## 初回の2指摘と解決確認

| 初回の指摘 | 実装した対応 | 現在の確認先 |
| --- | --- | --- |
| 専門家版の帰還率 `Σp_z²` に、純粋な初期状態という条件が明示されていなかった | 純粋な初期状態、直交電荷群、各群の等長写像を戻す操作、全レジスターの元状態への射影を日英に追加。別設定の論理qubit帰還率 `1−p/2` と区別 | `expert-readout`：[日本語](content/expert-ja.html#expert-readout)／[English](content/expert-en.html#expert-readout)。原定義：[tests.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/tests.tex) 冒頭 |
| 学生版は補足の11局所試験＋12天文・宇宙論試験を集約し、一部の個別説明がなかった | 原理説明を維持して、全23件の参照付録を日英に追加。一般向けにも同数の付録を追加 | 学生 `student-test-reference`：[日本語](content/student-ja.html#student-test-reference)／[English](content/student-en.html#student-test-reference)。一般 `tests-reference`：[日本語](content/general-ja.html#tests-reference)／[English](content/general-en.html#tests-reference)。原一覧：[supp-tests.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-tests.tex) |

専門家の `expert-tests`、学生の `student-test-reference`、一般の `tests-reference` をHTMLから読み取り、**6ページすべてで局所11行・天文／宇宙論12行**を確認しました。学生版では `L01`–`L11`、`A01`–`A12` の行識別子も使っています。各表は指定した準備・枝ごとの検証案を示し、一つの装置や真空が全条件を同時に満たすという主張にはしていません。

## 数値と仮定について確認した範囲

以下は原論文との照合項目です。単純な算術は再計算しましたが、掲載された全数値研究を新たに実行したわけではありません。

| 項目 | 確認した値・科学的な区別 | 主な原資料 |
| --- | --- | --- |
| 厳密な閉鎖 | 指定球面ポートで `N_in = max(1+m−n,0)`。負の単位差で零となること、空間モード数と内部コード次元、全ポートを閉じる条件を区別 | [main.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/main.tex)、[supp-domains.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-domains.tex) |
| 一つの準備からの共同確率 | `r = 3/4`、`p = 0.64`、B閉鎖0.5376、A/B同時成立0.196608。Aの事象は両端の実吸収であり、空記録同士の一致を含めない | [joint-experiment.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/joint-experiment.tex) |
| 回復と担体 | 閉鎖履歴の条件付き回復と全履歴忠実度0.6532を区別。光子対・重力子対・コアの重み1/2・1/3・1/6は代替的担体であり、三つの複製ではない。アクセス可能性が条件 | [joint-experiment.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/joint-experiment.tex)、[supp-revision.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-revision.tex) |
| 因果期限 | 5.44 ms、20.66 μs、1.003 μsは指定した10太陽質量の例。異なる時計と終点の値で、到来の余裕だけでは受信成功を保証しない | [main.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/main.tex) |
| 帰還・較正 | 全レジスターの `Σp_z²` と論理qubitの `1−p/2`、共同準備の `p = 0.64` と別設計の目標 `p = 8/9` を区別。900試行、上限0.659582／下限0.970227、全許容状態・旗に一様な `Δ ≤ 0.01`、暗計数 `d ≤ 0.01`、86–87回の保留を確認 | [tests.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/tests.tex)、[supp-calibration.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-calibration.tex) |
| 時計・計量・重力 | 十個の行列成分と行列サイズN、有限時計とランク極限、非退化な4次元Hから読む計量と一般のEinstein方程式を区別。指定波の `Tr K = 0` から全物質・全安定性へ一般化しない | [parent-history.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/parent-history.tex)、[geometry.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/geometry.tex) |
| 真空・半径 | 48,055,489 → 20,597 → 115 → 49 → 41は、固定結合・tadpole上限を持つ指定正方トーラスorientifoldの異なる絞り込み段階。全CAT真空数、完全安定性、共通半径の決定を意味しない | [geometry.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/geometry.tex) |
| 天文・宇宙論の試験 | 23件の名称・比較対象・必要条件を照合。Pantheon+、DESIなどは原論文が用いた観測値として扱い、同じ枝の準備・均一性・低赤方偏移・選択効果などの限定を保持 | [supp-tests.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-tests.tex)、[supp-constraints.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/supp-constraints.tex)、[tests.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/tests.tex) |
| 計算証拠・著者・AI | 9 driver・59群・1,195浮動小数点値と、選択10 Lean module・365宣言の記録。v3の再実行とv4の同一性継承・限定checkを区別し、AI技術レビューを外部査読として扱わない | [verification.json](../quantum-gravity/correlation-actualization-theory/v4/paper/evidence/verification.json)、[response.md](../quantum-gravity/correlation-actualization-theory/v4/paper/response.md)、[closing.tex](../quantum-gravity/correlation-actualization-theory/v4/paper/closing.tex) |

算術照合では、共同表の4セルが `[3072,1728,5328,5497]/15625`、すなわち `[19.6608,11.0592,34.0992,35.1808]%` となり、総和1であることを確認しました。`0.75×0.64 + 0.25×0.64×0.36 = 0.5376`、`0.75×0.64³ = 0.196608`、`0.5376 + 0.4624/4 = 0.6532` も一致します。較正の二項反転と式から得る境界は、表示の丸め値0.659582／0.970227と一致しました。

## 図の修正と日英対応

[figures.py](figures.py) の26種類を原論文と図仕様に照合しました。数値の修正は不要でしたが、許容域の表示方向と、条件を明確にする以下の修正を実施しました。

| 図・説明 | 解決した点 |
| --- | --- |
| `expert-readout-design` の帯 | CATは0から上限、通常模型は下限から1を塗り、`≤`／`≥` を明示。通常模型の下限を0から塗っていた表現を修正 |
| `expert-joint-probabilities` | Aは両端の実吸収、Bは相対電荷−1と表示。空の二記録をAの事象に含めないことを専用captionへ追加 |
| `student-geometry`, `expert-geometry-ladder` | `det H ≠ 0; d = 4` と、計量構成の前提を追加 |
| `expert-readout-design` のcaption | 目標 `p = 8/9`、全許容状態・旗に一様な `Δ ≤ 0.01`、独立な暗計数上限 `d ≤ 0.01` を明記 |
| `expert-vacuum-constraints` | 固定結合とtadpole上限を持つ指定正方トーラスorientifoldという計数対象を明記 |
| `general-evidence` | 英語にも日本語と同じ「復号」を追加 |
| `expert-closure-count`, `student-domain`, `general-route` | 複数の線が許される空間モードを表し、未知状態Cの複製ではないことをcaptionへ追加 |
| `expert-history-instrument`, `student-channel`, `general-records` | 図の結果zが後続ポート操作Wへ使われることをcaptionで接続 |
| 一般ページ `correlations` | 「重ねたシート」の説明を、実際の枠と枝による図に対応する日英の一文へ変更 |

同じ図IDから日英を生成し、26図×2言語の**52 SVGでXML構造エラー0**を確認しました。図中の数値、代替的な枝と複製の区別、物理的入力と条件付き帰結の区別、未実施の設計と観測値の区別を対象としました。`general-source` は閉鎖履歴における担体からの回復を説明する図であり、共通源の全装置配置を描く図としては扱っていません。

## 機械的照合と、その限界

| 確認対象 | 確認結果 |
| --- | --- |
| 6本文素材の日英対応 | 各読者水準で、ID列・図ID列・原資料へのリンク列が一致。重複IDなし |
| 表示式 | 専門家12個、学生8個の日英TeX列が一致。一般向けには独立した表示式なし |
| 試験一覧 | 各ページに局所11行・天文／宇宙論12行。学生・一般の付録アンカーも実在 |
| `SOURCE_ROOT` 参照 | 専門家各3、学生各27、一般各9、合計78出現。存在しない原資料パス0 |
| PDFページ指定 | 主論文・補足の18ページ以内。ページ番号の範囲検査と、実際の内容との照合を区別 |
| 生成物の既存検査記録 | [verification.json](verification.json) に13 HTML、522ローカルリンク、84原資料リンク、日英3組、エラー0を記録。これは本文素材の78リンクと集計対象が異なる |
| 原PDFの同一性 | 生成工程の記録で主論文・補足のSHA-256がv4原本と一致。値は [verification.json](verification.json) に保存 |

ID・式・リンク列の一致だけで、自然言語の意味の同等性が自動的に証明されるわけではありません。数値、仮定、失敗例、未解決事項については上の科学的照合と組み合わせて確認しました。全6ページへの同じ表・式・数値の重複掲載は要求していません。

この文書の仕上げでは、現行の本文素材と参照先を読み取って照合し、本文・研究原稿・生成処理を変更していません。生成物側の検査結果は既存の記録を参照しており、本書更新に伴う再ビルドや、公開先のHTTP取得・画面レイアウト検査を実施したという記録ではありません。

## 初回QAの原記録

以下は専門家・学生の4ページを対象とした初回報告を、文面を変更せず保存したものです。「補強の余地」や「未編集」という記載は、その時点の状態を表します。現在の対応状況は上の「初回の2指摘と解決確認」を参照してください。

原記録のSHA-256：`ed4d9faffd2b75352c3a2bda196695a4f543cb511407782fc605df65f60c89be`。

<details>
<summary>初回の4ページQA記録を開く</summary>

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
