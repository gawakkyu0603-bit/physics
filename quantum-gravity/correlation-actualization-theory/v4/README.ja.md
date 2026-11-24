# Correlation Actualization Theory

## 観測者に依存するレイヤーをもつ非摂動的行列理論の提案

**Yohtaro Soga · 第四版 · 2026年11月25日**  
[English](README.md) · 日本語

[主論文](paper/main.pdf) · [技術補足](paper/supplement.pdf) · [読解ガイド](paper/reading-guide.md) · [検証記録](VERIFICATION.md)

この版ディレクトリには **Correlation Actualization Theory（CAT）第四版**を収録しています。
CAT は、ブラックホールに落下する観測者と遠方の観測者が取得できる記録の違いを出発点とします。
通常の行列ダイナミクスによる相関形成に加え、重力がレイヤーを不可逆に選択し、
その後の物質的接触で利用できる伝播モードを変える規則を提案します。

**論文の状態：外部査読を経ていない研究プレプリント。**
同梱資料で扱う技術レビューは AI を用いて作成されたもので、研究の検討・確認記録の一部です。
学術誌の査読や掲載受理を意味しません。

リポジトリは
[`gawakkyu0603-bit/physics`](https://github.com/gawakkyu0603-bit/physics)、この版のパスは
`quantum-gravity/correlation-actualization-theory/v4`、Release タグは `cat-v4.0.0` です。

## 論文と証拠資料への入口

| 読みたい内容 | 資料 |
| --- | --- |
| 物理的提案と主要な論証 | [主論文・18ページ](paper/main.pdf) |
| 定義・仮定・計算・較正の詳細 | [技術補足・18ページ](paper/supplement.pdf) |
| 六つの物理的問いと対応箇所 | [読解ガイド](paper/reading-guide.md) |
| 各研究結果と根拠資料 | [91件の番号付き結果の英語ガイド](paper/evidence/result_guide.md) |
| 結果・ファイル・ページの対応 | [証拠索引](paper/evidence/experiments.json) |
| 実行済みの確認と適用範囲 | [公開版の検証要約](VERIFICATION.md)、[原版の検証記録](paper/evidence/verification.json) |
| 第三版へのレビューに対応した変更 | [第四版の応答書](paper/response.md) |
| 元の配布一式に付属する説明 | [変更していない原版 README](paper/README.md) |

研究記録には日本語の作業ノートと英語の要約が含まれます。
91件の番号付き記録には、条件付きの計算結果や否定的結果も含まれます。
この件数は、新しい物理法則の数を表すものではありません。

## 提案が示している範囲

論文は行列サイズを横断して記述される処方を提案しています。
非摂動的な計算は、**ランク・時計・準備状態・物理的ポートを指定した範囲**で、
散乱ブロック全体を扱います。仮定の詳細は[行列則の議論](paper/parent-history.tex)と
[観測者ごとの定義域を扱う補足](paper/supp-domains.tex)に記載しています。

- 内向き経路の厳密な閉鎖は、指定した制約付きチャネルについて成立します。
  観測者の記述全体を外部だけで完結させるには、アクセス可能な内向きポートがすべて閉じる必要があります。
  一つの角度領域の閉鎖だけから、その全体的結論は導けません。
- 共通の準備から出発する例は、指定した条件下の継続経路と情報回復チャネルを示します。
  自然な恒星崩壊についての一般解を与えるものではありません。
- ランクと時計のセクターを結びつける量子理論、自然な崩壊で必要なポートが広く形成される機構、
  蒸発終端での情報回復は未解決です。提案する読み出しプロトコルは実験設計であり、測定結果ではありません。

[形式検証の付録](paper/closing.tex)は、数学的主張と Lean 宣言を対応づけ、
前提となる物理的・解析的入力を明記しています。条件付きの数学的命題のカーネル検証は、
その条件が自然界で実現することの証明ではありません。

## Git 版と完全配布 ZIP

版を固定した配布物は、
[`cat-v4.0.0` Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0) を参照してください。
[release-assets.json](release-assets.json) に配布ファイル、サイズ、チェックサム、ダウンロード URL を記録しています。

| 配布形態 | 内容と用途 |
| --- | --- |
| Git checkout | `quantum-gravity/correlation-actualization-theory/v4/` に公開用の説明文書、その `paper/` に第四版原本の709ファイル。PDF・LaTeX・証拠資料・プログラム・Lean ソースを含みます。 |
| Release asset の `CAT_v4_full_publication_bundle.zip` | `CAT-review/` に第四版原本の全742ファイル。Git 版で省略した33個の実行環境・依存関係ファイルも含みます。配布用の告知・ライセンス資料は `CAT-review/` の外側に置いています。付属のオフライン再実行ラッパーにはこちらを使用してください。 |
| GitHub が自動生成する “Source code” ZIP / tarball | Git ツリーのスナップショットです。Release asset にのみ収録する実行環境は含みません。 |

`paper/` に保持する原本ファイルは、提供された第四版とバイト単位で同一です。
この README の `paper/` などの相対パスは、この版ディレクトリを起点とします。
[公開版 manifest](PUBLICATION_MANIFEST.json) は、このディレクトリの全ファイルから自分自身を除いた一覧で、
そこに記載するパスも同じディレクトリを起点とします。
[原版 manifest](paper/manifest.json) は、Git 版に含まれない実行環境も含めた完全な原本一式を対象にします。
完全性の検査は、Git ツリーではなく、**完全配布 ZIP を展開した `CAT-review/`** に対して実行してください。

## 検証の実行状況

[公開版の検証要約](VERIFICATION.md)では、過去版での実行、ソースの同一性確認、
第四版の技術レビューで再実行した限定的な検査を区別しています。

| 確認項目 | 記録された範囲 |
| --- | --- |
| 数値計算 | 第三版レビューは、選択された9本の driver を Linux で再実行したと報告しています。参照出力との比較対象は59グループ・1,195個の浮動小数点値に加え、ラベル・整数・配列構造です。 |
| Lean | 第三版レビューは、選択された10モジュールを Linux で再実行したと報告しています。その中には365個の theorem / lemma 宣言があります。全85研究用 Lean ファイルを同梱していますが、この再実行範囲は85ファイル全体ではありません。 |
| 第四版への継承 | 計算ソースと参照出力を第三版と SHA-256 で照合しています。詳細な比較結果は公開版の検証要約を参照してください。 |
| 第四版の技術レビュー | パッケージ検査を再実行し、143個の有限な内向き接続系を含む確認が成功しています。第四版で全数値 driver・全選択 Lean モジュールを再実行したとは主張していません。 |

[原版の検証記録](paper/evidence/verification.json)と[第四版の応答書](paper/response.md)に、
それ以前の検証履歴を保持しています。[numeric_policy.py](paper/numeric_policy.py)は、
微小だが非零の値、物理的な分解能、解析的に零となる量の数値残差を区別します。

## 完全配布 ZIP から再実行する

Release から `CAT_v4_full_publication_bundle.zip` をダウンロードし、書き込み可能な場所に展開してください。
展開後の `CAT-review/` でシェルを開いて、以下を実行します。
この手順は完全版用です。Git checkout には省略した実行環境アーカイブが含まれません。

### Linux x86-64

CPython 3.12 と互換性のある glibc 環境（glibc 2.28 以降）が必要です。
記録された確認環境は CPython 3.12.3 / glibc 2.39 です。
ラッパーは同梱の科学計算用 wheel を専用キャッシュに展開し、同梱の Lean と mathlib を使用します。

```sh
bash review-linux.sh check
bash review-linux.sh numerical cat_domain_calibration
bash review-linux.sh lean CATObserverDomain
bash review-linux.sh study RES-0183 cat_domain_calibration
```

### Windows x64

PowerShell ラッパーは、同梱の CPython 3.14.7、科学計算パッケージ、Lean 3.51.1 を使用します。

```powershell
.\review-offline.ps1 -Action check
.\review-offline.ps1 -Action numerical -Names 'cat_domain_calibration'
.\review-offline.ps1 -Action lean -Names 'CATObserverDomain'
.\review-offline.ps1 -Action study -Names 'RES-0183','cat_domain_calibration'
```

数値計算または Lean のコマンドで名前を省略すると、既定の選択対象をすべて実行します。
固定した環境とコマンドの詳細は[原版 README](paper/README.md)を参照してください。

## 論文 PDF を再生成する

Git checkout では、pdfLaTeX と Poppler を用意し、`physics` リポジトリのルートから以下を実行します。

```sh
cd quantum-gravity/correlation-actualization-theory/v4/paper
bash build.sh main supplement
```

[主論文ソース](paper/main.tex)、[補足ソース](paper/supplement.tex)、
[主論文の小型ソースアーカイブ](paper/arxiv-source.tar.gz)を同梱しています。
小型アーカイブは論文をビルドするための資料であり、ファイル名は arXiv への投稿を意味しません。

## 人間の著者と AI の貢献

Yohtaro Soga は、観測者ごとのレイヤー、その不可逆な重力的選択、落下者の異なる帰結を提案し、
遠方の観測者の記述における内向き経路の厳密な閉鎖を有効作用の選択基準として設定して、研究を指揮しました。
OpenAI Codex は数学的構成、文献調査、数値計算と Lean のコード、検証、文章作成を支援しました。
別途実施した AI による技術レビューが、修正と説明の明確化につながりました。
これらの役割は、論文の[「Author contributions and use of AI」節](paper/closing.tex)に記載しています。
人間の著者名は Yohtaro Soga です。

## 引用・改訂履歴・権利

引用する際の識別情報：**Yohtaro Soga (2026), _Correlation Actualization Theory:
A nonperturbative matrix proposal with observer-dependent layers_, Version 4,
25 November 2026.** この配布版を特定する `cat-v4.0.0` release または正確なコミットも記載してください。

以前の改訂応答は [response-v3.md](paper/response-v3.md) と [response-v2.md](paper/response-v2.md) に保持しています。
このリポジトリの説明は、DOI の取得、学術誌の受理、所属機関を主張するものではありません。

再利用条件は配布用の告知資料、および第三者コンポーネントに付属する既存ライセンスを確認してください。
この README は、原著作物に新たなライセンス許諾を追加するものではありません。
