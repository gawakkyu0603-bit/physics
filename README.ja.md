# Physics

物理学の論文、再現用の証拠資料、日英の読解ガイドを版ごとにまとめるリポジトリです。

[English](README.md) · 日本語

## 研究の索引

構成は **分野 → 論文 → 版** です。原研究の資料と、解説用のウェブサイトを分けて保持します。

| 分野 | 論文 | 版と証拠資料 |
| --- | --- | --- |
| [量子重力](quantum-gravity/README.md) | [Correlation Actualization Theory（CAT）](quantum-gravity/correlation-actualization-theory/README.md) | [第4版](quantum-gravity/correlation-actualization-theory/v4/README.ja.md) · [検証記録](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md) |

## 読者に合った入口から読む

Pagesの共通入口は[日本語](https://gawakkyu0603-bit.github.io/physics/ja/index.html)と[English](https://gawakkyu0603-bit.github.io/physics/en/index.html)です。

| 読者 | 日本語 | English |
| --- | --- | --- |
| 研究分野の専門家 | [専門家向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/expert.html) | [Expert guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/expert.html) |
| 理工系の学部生・大学院生 | [理工系学生向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/student.html) | [Student guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/student.html) |
| 一般の読者 | [一般読者向け](https://gawakkyu0603-bit.github.io/physics/ja/quantum-gravity/cat/general.html) | [General guide](https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/general.html) |

各言語の対は同じ研究テーマと結論を扱います。各ページはTL;DRから始まり、論文全体をそれぞれの水準で説明し、原資料へリンクします。図は専門家向け8点、学生向け9点、一般向け9点を収録し、日英が対応しています。

## 論文と配布物

CAT第4版は、Yohtaro Sogaによる2026年11月25日付の**外部査読を経ていない研究プレプリント**です。不可逆な重力的受信と物理的な出力領域の変化を提案します。具体的な結果は、ランク・時計・準備・ポートを指定した範囲で成立します。セクターを結ぶ理論、一般の自然な崩壊、蒸発終端での回復は未解決です。

版ディレクトリの`paper/`には**原版と同一の709ファイル**を保持します。`cat-v4.0.0`の[Release](https://github.com/gawakkyu0603-bit/physics/releases/tag/cat-v4.0.0)用の完全配布ZIPは、Gitから省いた33個の実行環境・依存関係ファイルを含む、**原版の全742ファイル**を保持します。配布用の注意書きは原版の`CAT-review/`の外側に置きます。GitHubが自動生成するソースアーカイブはGitツリーのみです。

[主論文](quantum-gravity/correlation-actualization-theory/v4/paper/main.pdf) · [技術補足](quantum-gravity/correlation-actualization-theory/v4/paper/supplement.pdf) · [再現手順](quantum-gravity/correlation-actualization-theory/v4/README.ja.md) · [公開範囲](docs/PUBLICATION_SCOPE.md)

[検証記録](quantum-gravity/correlation-actualization-theory/v4/VERIFICATION.md)は、第3版での全選択スイート実行と、第4版での同一性照合・限定的な再実行を区別します。人間の著者の構想と研究の方向づけ、Codexの補助、AIによる技術レビューは原論文で開示しています。その技術レビューは学術誌の査読ではありません。

## 今後の論文追加とサイト生成

新しい論文は分野ごとに追加し、版ディレクトリを明示します。原稿は変更せず、解説とその生成元をサイトの作業手順で管理します。サイト生成の入口は[tools/build_site.py](tools/build_site.py)です。日本語と英語で説明の範囲をそろえてください。

原研究に新しい一括ライセンスは付与していません。[権利表示](quantum-gravity/correlation-actualization-theory/v4/RIGHTS.md)と[第三者資料の注意書き](quantum-gravity/correlation-actualization-theory/v4/THIRD_PARTY_NOTICES.md)を参照してください。DOI取得や学術誌での受理は主張していません。

リポジトリ：[gawakkyu0603-bit/physics](https://github.com/gawakkyu0603-bit/physics)。
