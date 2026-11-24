# CAT 第四版：英語3記事の内容対応表

この文書は、専門家・理工系学生・一般読者向けの英語3記事を、原論文と照合するための内容索引です。対象は **Yohtaro Soga, Correlation Actualization Theory, Version 4, 25 November 2026**。原論文・計算・証拠ファイルを改訂する文書ではありません。

2026年11月25日の著者の指示により、日本語3記事は公開対象から除外し、本文素材と生成HTMLを削除しました。今後も英語の3読者水準を追加します。この変更で英語本文の科学的内容は改訂していません。

## 英語3記事の役割

| 読者 | 英語の本文素材 | 説明の重点 |
| --- | --- | --- |
| 専門家 | [English source](content/expert-en.html) | 作用と符号、instrument、核・定義域、回復条件、時計・計量、全プロトコルと適用仮定 |
| 理工系学生 | [English source](content/student-en.html) | 状態とチャネル、線形代数、空間モードと内部コード、準備から観測までの段階的な説明 |
| 一般読者 | [English source](content/general-en.html) | 観測者の記録、道の有無、位相と情報、時計と幾何を図と具体例で説明し、比喩の適用範囲を保つ |

三つの読者水準は同じ研究の仮定・結果・未解決事項を扱います。原論文の全節と補足の中心テーマを横断して説明していますが、逐語的な全文転載、全証明の書き直し、91件の研究記録すべての個別再掲ではありません。数式や事例の詳細度は読者に合わせて変え、一般向けで省いた演算子の詳細を、実証済みの普遍法則に置き換えることはしていません。

原本への入口：[主論文PDF](../quantum-gravity/correlation-actualization-theory/v4/paper/main.pdf)、[技術補足PDF](../quantum-gravity/correlation-actualization-theory/v4/paper/supplement.pdf)、[原版README](../quantum-gravity/correlation-actualization-theory/v4/paper/README.md)、[結果ガイド](../quantum-gravity/correlation-actualization-theory/v4/paper/evidence/result_guide.md)。各解説本文からも該当PDFページまたは原ソースを参照できます。

## 主論文から各解説への対応

表のセルは各ページ内の実在するアンカーです。現在公開する英語記事のIDを示します。主論文のソースは `quantum-gravity/correlation-actualization-theory/v4/paper/` にあります。

| 原論文の節・主要テーマ | 原ソース | 専門家 | 理工系学生 | 一般向け |
| --- | --- | --- | --- | --- |
| Abstract・§1：A/Bの落下、比較不能な記録、三つの追加仮定 | `main.tex` | `expert-tldr`, `expert-question` | `student-tldr`, `student-question` | `summary-heading`, `two-observers`, `correlations` |
| §2.1：潮汐、媒介場、直接相互作用、因果的接触 | `main.tex` | `expert-law`, `expert-closure` | `student-choices`, `student-current` | `actions`, `matrices` |
| §2.2：support floor、有限減衰と厳密な零 | `main.tex` | `expert-closure` | `student-channel`, `student-domain` | `routes` |
| §2.3：球面の線束、符号付きの内向き次元、全ポート条件 | `main.tex` | `expert-closure`, `expert-deadlines` | `student-domain` | `routes` |
| §3.1：十行列、実時間符号、BFSS時計商、材料指数と補償 | `main.tex` | `expert-law`, `expert-geometry` | `student-parent`, `student-current` | `matrices` |
| §3.2：受信instrument、routing、保存則、二重履歴 | `main.tex` | `expert-law`, `expert-closure` | `student-channel`, `student-history` | `correlations`, `actions`, `matrices` |
| 固定ネットワークの記録粗視化、観測者の出力、ランクの意味 | `parent-history.tex` | `expert-question`, `expert-law` | `student-history`, `student-finite` | `matrices`, `recovery` |
| §4.1：締切、到来と吸収、自然崩壊の準備、失敗例 | `main.tex` | `expert-deadlines` | `student-deadline` | `deadline` |
| §4.2：参照エンタングルメント、全キャリア、振幅と強度、終端 | `main.tex` | `expert-recovery` | `student-recovery` | `recovery` |
| 共通の二パルス源、共同確率、条件付き回復 | `joint-experiment.tex` | `expert-example` | `student-example` | `recovery` |
| §5：物質的な有限時計、時計セクターの前提 | `geometry.tex` | `expert-geometry` | `student-finite`, `student-geometry` | `clock-geometry` |
| §5.1：スカラーの符号、主部密度、計量、指定真空Einstein波 | `geometry.tex` | `expert-geometry` | `student-geometry` | `clock-geometry` |
| §5.2：高曲率、bounce、励起と安定性、未導出の真空遷移 | `geometry.tex` | `expert-continuation` | `student-spacetime` | `vacua` |
| §5.3：共有計量、向き、三重の重なり、滑らか構造 | `geometry.tex` | `expert-continuation` | `student-spacetime` | `clock-geometry`, `vacua` |
| §6：IKKT/IIB、BFSS/M、loop、causal sets、CDT、有限円開口 | `geometry.tex` | `expert-comparisons` | `student-theories` | `matrices` |
| §6.1：限定flux counts、共通半径、一ループ相殺、物質と力 | `geometry.tex` | `expert-vacua` | `student-vacua` | `vacua`, `sky` |
| §7：反転、記憶と再訪問、読み出し較正 | `tests.tex` | `expert-readout` | `student-test` | `return` |
| §7：恒星・偏極・電波・neutrino・CMB、膨張と距離、暗黒成分 | `tests.tex` | `expert-tests` | `student-sky`, `student-cosmology` | `sky` |
| §8：候補理論の意味、先行研究、同じ崩壊で成立すべき条件 | `tests.tex` | `expert-comparisons`, `expert-evidence` | `student-theories`, `student-verification`, `student-glossary` | `next`, `evidence` |
| Appendix：条件付きLean検証、解析・実験入力、著者とAI利用 | `closing.tex` | `expert-evidence` | `student-verification` | `evidence`, `sources-heading` |

## 技術補足の主要事項

| 補足の内容 | 原ソース | 専門家 | 理工系学生 | 一般向け |
| --- | --- | --- | --- | --- |
| 接触の選択、可逆潮汐、連続比較、有限罰則、通常外部との一致 | `supplement.tex` §1 | `expert-law`, `expert-closure` | `student-choices`, `student-domain`, `student-current` | `actions`, `routes` |
| 有限リンク、受信効果、放射容量、複数訪問 | `supplement.tex` §2 | `expert-closure`, `expert-recovery`, `expert-readout` | `student-domain`, `student-recovery`, `student-test` | `routes`, `recovery`, `return` |
| 主部密度、中央交換子、曲がった行列セクター | `supplement.tex` §3 | `expert-geometry` | `student-parent`, `student-geometry` | `clock-geometry` |
| 準備からreadoutまで、符号・指数・反跳・四ビット分布 | `supp-revision.tex` | `expert-law`, `expert-example`, `expert-recovery` | `student-parent`, `student-current`, `student-example`, `student-recovery` | `matrices`, `recovery` |
| 物理的出力空間、同時複製でないこと、共有記録、結果付き順序 | `supp-domains.tex` | `expert-question`, `expert-law` | `student-history`, `student-domain`, `student-example` | `actions`, `recovery` |
| 正負参照、Pauli X、全状態誤差上限、900試行 | `supp-calibration.tex` | `expert-readout` | `student-test` | `return` |
| 何が同じ準備で同時に実現したか | `supp-calibration.tex` の比較表 | `expert-geometry`, `expert-vacua`, `expert-evidence` | `student-vacua`, `student-verification` | `vacua`, `evidence`, `next` |
| 局所11種類と天体12種類のプロトコル | `supp-tests.tex` | `expert-tests`：[English](content/expert-en.html#expert-tests)に全23件と数式・条件を列挙 | `student-test-reference`：[English appendix](content/student-en.html#student-test-reference)に全23件を掲載し、本文の原理説明へ接続 | `tests-reference`：[English appendix](content/general-en.html#tests-reference)に全23件の比較対象と必要条件を掲載 |
| 作用の選択、双対性、既存観測、任意の暗黒成分 | `supp-constraints.tex` | `expert-comparisons`, `expert-tests` | `student-theories`, `student-cosmology` | `matrices`, `sky` |
| 近い先行研究と独自性の限界 | `supp-scope.tex` | `expert-comparisons` | `student-theories` | `matrices`, `next` |
| 証拠の分類・91件の個別要約・否定的結果 | `supp-scope.tex`, `supp-results.tex` | `expert-evidence` | `student-verification` | `evidence`, `sources-heading` |

各読者水準・各言語の試験一覧を確認すると、局所11行と天文・宇宙論12行が揃っています。学生・一般向けの付録は原理説明を補う参照表であり、全項目の演算子・導出・数値記録を再掲するものではありません。

一般向けの比喩は、対応する数学の入口として使います。「層」は観測された並行宇宙ではなく、「経路数」はqubit数ではなく、「反転」は実際の全環境制御を達成したという意味ではありません。証明・生データ・詳細なアルゴリズムは元のPDFと証拠索引を読む構成です。

## 重要な値と、その値に不可欠な条件

| 結果・値 | 必須条件／解釈 | 拡張していない結論 |
| --- | --- | --- |
| `N_in=max(1+m−n,0)`、相対次数−1で零 | 指定した球面の正則ポート。物理的種・内部束・開口を指定 | 別の種・ポートを含む全ブラックホールの無条件の閉鎖 |
| `p=0.64, r=3/4`、B閉鎖0.5376、共同成立0.196608 | 同じ二パルス準備、Aは両端の実吸収、Bは負の相対電荷 | 天体集団の閉鎖率、二つの同時コピー、全試行での閉鎖 |
| 閉鎖B履歴で回復、全履歴忠実度0.6532 | 指定したqubit・光子対・重力子対・コアとアクセス可能性 | 任意の崩壊・全蒸発履歴に対する情報問題の解決 |
| 5.44 ms、20.66 μs、1.003 μs | 10太陽質量の指定軌道と二つの固有時計・異なる終点 | 同じ時計上の一つの時間予算、受信が必ず起きること |
| `Σp_z²`、二群では`w²+(1−w)²` | 純粋な初期状態と直交電荷群を用い、各群の等長写像を戻して**全register**を元状態へ射影 | 任意の混合状態への同式の適用、論理qubitの`1−p/2`や天体echoの振幅と同一の量 |
| 読み出し上限0.659582／下限0.970227、最大900試行 | 別設定の目標p=8/9、正負較正、全状態Δ≤0.01、暗計数d≤0.01、独立定常試行 | 現実の重力実験で既に達成された効果、信号tailだけの誤差確率 |
| 指定波形の`Tr K=0` | 物質プローブが読む一つの真空Einstein波 | 一般物質のEinstein方程式、全種の共通円錐、全安定性 |
| 115 flux軌道、49の線形固定、41のO3飽和 | 固定coupling/tadpoleの特定orientifold、primitive条件と有限商 | CAT全体の真空数や、現実的な完全安定真空の数 |
| 59グループ・1,195浮動小数点値、365宣言 | v3で選択9driver／10moduleの再実行報告。v4は同一性継承と限定check | 85ファイル全体の新規独立再実行、物理的前提の実証 |

## 英語3記事の範囲と保持方針

- 専門家・理工系学生・一般読者の各記事で、同じ研究の仮定・結果・未解決事項を扱います。説明量・語彙・式の詳細度は読者に合わせます。
- 専門家版の表示式は12個、理工系版は8個、一般向けの独立した表示式は0個です。図は専門家8点・理工系9点・一般9点です。
- 日本語記事を除外する変更では、英語の本文素材と生成HTML内のarticle部分が変更前と同一であることをハッシュで照合します。言語切替などの共通ナビゲーションは変更対象です。
- 原稿の数学・数値・観測について新たな全面再査読や観測再解析を行ったとは表示しません。各説明の根拠は第四版の明示した範囲です。

## 原ソースへのリンク検査

検査先：`physics/quantum-gravity/correlation-actualization-theory/v4/paper/`。本文の `{{SOURCE_ROOT}}/…` を同ディレクトリ内の実ファイルに対応させた。

| 本文 | SOURCE_ROOTリンク出現数 | 異なる参照先 | 存在しない参照先 |
| --- | ---: | ---: | ---: |
| expert-en.html | 3 | 3 | 0 |
| student-en.html | 27 | 13 | 0 |
| general-en.html | 9 | 7 | 0 |

全39出現について誤った原ソースパスは見つからなかった。主論文・補足への `#page=` アンカーも全て1–18ページの範囲内である。これは本文素材内の参照先とページ範囲の確認であり、GitHub Pages公開後のHTTP取得、レイアウト、図の表示、数式描画の確認は生成・公開工程で別途行う。

本文素材は、このリポジトリに同梱する [site-src/content](content/) にある。各本文の出典リンクから原論文と補足へ進める。英語で公開する図・captionは [figures.py](figures.py) に、初回の指摘、修正確認、数値と仮定の照合範囲は [SCIENTIFIC_QA.md](SCIENTIFIC_QA.md) に記録した。生成物の構造・リンク・数式・PDF同一性の検査記録は [verification.json](verification.json) を参照する。
