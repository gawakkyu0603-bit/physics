# サイトの生成元と、新しい論文の追加

このディレクトリは、日英それぞれの専門家・理工系学生・一般読者向け解説を生成するための資料です。研究資料は **分野 → 論文 → 版** に分け、ウェブサイトはカタログで選んだ版を案内します。

現在の対象はCAT第4版です。ビルドやファイルの追加だけでは、GitHubへの公開やPagesの設定は実行されません。

## 1. 生成元と出力の関係

| 場所 | 役割 |
| --- | --- |
| `catalog.json` | 公開先、分野の日英名・説明、論文と版、記事・PDFへの対応 |
| `content/` | 日英3水準、計6個のHTML本文素材 |
| `figures.py` | 日英対応のSVG図を作る関数と登録表 |
| `render-math.cjs` | KaTeXで数式をHTMLとMathMLへ変換 |
| `COVERAGE.md` | 原論文の節・検証案と、解説ページの対応 |
| `../tools/build_site.py` | 共通ナビゲーション、目次、図、数式、索引を合成 |
| `../tools/verify_site.py` | リンク、日英構造、数式、図、原本PDFの確認 |
| `../docs/` | 生成するHTMLと、配信する既存の共通資産・PDF |
| `build-stats.json` / `verification.json` | ビルド／検証コマンドの実行時に更新する記録 |

`build_site.py`はHTMLを生成します。PDFやCSS・JavaScript・フォントを自動的に配置する処理は含まないため、必要な配信ファイルは別途、正しい場所へ置きます。

## 2. 原論文を版付きで配置する

例えば新しい分野に新しい論文を追加する場合、次のような対応を作ります。以下の名前は追加手順を示す例で、実在する収録論文ではありません。

| 対象 | 例 |
| --- | --- |
| 分野のディレクトリ | `stellar-physics/` |
| 論文の原資料ディレクトリ | `stellar-physics/compact-star-modes/` |
| 版 | `stellar-physics/compact-star-modes/v1/` |
| 原稿・コード・証拠 | `stellar-physics/compact-star-modes/v1/paper/` |
| 公開タグ | `star-modes-v1.0.0` |
| Pagesの論文URL部分 | `ja/stellar-physics/star-modes/`、`en/stellar-physics/star-modes/` |

原稿・データ・計算コードは受領した版のまま保持し、解説のための変更を加えません。版のREADME、検証履歴、権利表示、配布条件をその版のディレクトリに用意します。大きい実行環境をGitから外す場合は、原本の完全配布物への対応を記録します。

同じ論文を改訂するときは旧版を残して`v2/`などを追加します。現在のPagesルートには版番号が含まれないため、同じ`field`と`slug`のカタログ項目を複数置くと同じHTMLパスへ書き込みます。通常はカタログで案内する一版を選び、過去版は原資料・タグ・Releaseからたどれるようにします。

## 3. 分野を登録する

`catalog.json`の`fields`へ、重複しない`slug`と日英の`name`・`summary`を追加します。

```json
{
  "slug": "stellar-physics",
  "name": {"ja": "恒星物理", "en": "Stellar physics"},
  "summary": {
    "ja": "恒星の構造と振動を、論文・解説・再現資料から読む。",
    "en": "Explore stellar structure and oscillations through papers, explanations, and reproduction materials."
  }
}
```

分野ページの題名・説明、記事のパンくず、論文カードの分野名は、この登録から読みます。`papers`の`field`は必ずここにある`slug`を参照してください。両言語の値を省略しないでください。

## 4. 論文と解説のファイルを登録する

`papers`へ追加する項目の例です。

```json
{
  "slug": "star-modes",
  "field": "stellar-physics",
  "archive_slug": "compact-star-modes",
  "title": "Example paper title",
  "short_title": "Star modes",
  "subtitle": "Example descriptive subtitle",
  "author": "Author name",
  "version": "1",
  "date": "YYYY-MM-DD",
  "release": "star-modes-v1.0.0",
  "source_path": "stellar-physics/compact-star-modes/v1/paper",
  "content_prefix": "star-modes-",
  "main_pdf": "downloads/star-modes-v1-main.pdf",
  "supplement_pdf": "downloads/star-modes-v1-supplement.pdf",
  "audiences": ["general", "student", "expert"],
  "languages": ["ja", "en"],
  "summary": {
    "ja": "この論文の問いと、得られた結果の範囲。",
    "en": "The paper’s question and the scope of its results."
  },
  "page_counts": {"main": 12, "supplement": 6},
  "audience_descriptions": {
    "general": {"ja": "身近な例から、論文の問いを理解する。", "en": "Understand the question through accessible examples."},
    "student": {"ja": "基礎式から模型と計算へ進む。", "en": "Connect foundational equations to the model and calculations."},
    "expert": {"ja": "定義、仮定、検証を詳しく読む。", "en": "Examine definitions, assumptions, and tests in detail."}
  },
  "reading_times": {"general": "15–25", "student": "25–40", "expert": "35–50"},
  "scope": {
    "ja": ["全ての読者水準で説明する研究範囲。", "図や計算の適用条件。"],
    "en": ["Research themes covered at every reading level.", "Conditions applying to the diagrams and calculations."]
  },
  "hero_figure": "star-modes-student-overview",
  "interactive_return": false
}
```

`slug`はサイトの短い名前、`archive_slug`は原資料側の論文ディレクトリ名です。`source_path`はリポジトリルートからの原資料へのパス、PDFパスは`docs/`からの相対パスです。リリース名は論文ごとに区別してください。

例のページ数・時間は説明用です。実際のPDFと記事で確認して入力します。論文固有の表示と、未指定時の動作は次のとおりです。

| メタデータ | 使う場所／未指定時 |
| --- | --- |
| `title`、`short_title` | 論文入口の題名、パンくず、単一論文の紹介。略称を省くと`title`を使う |
| `version` | 記事ヘッダー、PDF案内、記事末尾の版説明。原資料と一致する値が必須 |
| `page_counts.main` / `.supplement` | PDFボタンのページ数。省略した側は数を表示しない |
| `audience_descriptions` | 3水準のカードと記事末尾の案内。言語や水準の値がなければ中立的な説明を使う |
| `reading_times` | 読了時間の目安。未指定なら時間を表示せず、TL;DRの案内だけにする |
| `scope.ja` / `.en` | 論文入口に並べる説明範囲の段落。文字列の配列で指定し、未指定なら原論文への中立的な案内を表示 |
| `hero_figure` | 論文一覧・分野一覧の紹介図。未指定なら図なし、未登録のIDなら明示的にエラー |
| `interactive_return` | 二群の理想帰還の対話的説明を入れる明示的な指定。既定は無効で、現在はCATだけが有効 |

複数論文を登録すると共通入口のTL;DRは収録件数を案内し、単一論文ならその論文の題名・版を使います。新しい論文にCATの題名・版・ページ数・図・読了時間を自動適用しません。

`content_prefix`が`star-modes-`なら、本文素材は以下の6ファイルです。

- `content/star-modes-general-ja.html`、`content/star-modes-general-en.html`
- `content/star-modes-student-ja.html`、`content/star-modes-student-en.html`
- `content/star-modes-expert-ja.html`、`content/star-modes-expert-en.html`

CATの接頭辞は空文字です。新しい論文で空文字を再利用すると、既存CATの本文を読み込むため、論文ごとに別の接頭辞を使います。日英は同じテーマ・結論・出典を持つ完全な対とし、片方だけ短縮しません。

## 5. 本文素材の書式

本文はページ全体ではなく、`article`を一つ含む断片にします。見出し、TL;DR、最初の説明の例は次のとおりです。

```html
<article lang="ja">
  <header class="article-header">
    <h1>解説の題名</h1>
    <p class="lead">この読者に向けた導入。</p>
  </header>
  <aside class="tldr" id="star-modes-student-tldr">
    <h2>TL;DR</h2>
    <p>問い、結果、条件、残る課題を短く示す。</p>
  </aside>
  <section id="star-modes-student-model">
    <h2 id="star-modes-student-model-heading">模型を理解する</h2>
    <p>短い段落で説明する。</p>
    <div data-figure="star-modes-student-overview"></div>
    <p><a href="{{PAPER_PDF}}#page=2">論文本体の該当ページ</a></p>
    <p><a href="{{SOURCE_ROOT}}/main.tex">原ソース</a></p>
  </section>
</article>
```

ビルダーはTL;DRを記事の先頭へ移し、`h1`を共通ヘッダーへ載せ、`h2`から目次を作ります。各ページ内のIDを重複させず、日英の同じ節には同じIDを使います。TL;DR内の見出しも`h2`が必要です。

置換されるトークンは`{{PAPER_PDF}}`、`{{SUPP_PDF}}`、`{{SOURCE_ROOT}}`です。前二つはPDFへのローカルリンク、最後はその論文の指定Releaseタグを使ったGitHubの原資料リンクになります。ページ番号や原ソースのファイル名は、実際の版で確認します。

インライン数式は`\(...\)`、表示数式は`<div class="equation">\[...\]</div>`を使います。同じ読者水準の日英で表示式を一致させ、記号と成立条件を説明します。HTML内の`<`や`>`は必要に応じてエンティティへ変換してください。KaTeXのエラーはビルドを停止します。

専門家・学生・一般向けで説明の粒度を変えても、物理的仮定、条件付き結果、計画段階の実験、未解決事項の区別を保ちます。新しい論文についても`COVERAGE.md`に原論文・補足と本文の対応を追加します。

## 6. 図を日英で追加する

`figures.py`に、`lang`を受け取り`(SVGの内部文字列, 高さ)`を返す、名前付きの図関数を用意します。既存の`text`、`rect`、`arrow`等を再利用できます。標準の幅は880です。

次に、`MAP`へHTMLで使う図IDと関数を登録し、`CAPTIONS`へ**関数名**をキーとして、日英の題名・説明を登録します。

```python
MAP['star-modes-student-overview'] = star_modes_overview
CAPTIONS['star_modes_overview'] = (
    '日本語の図題', 'English figure title',
    '日本語で条件と図の意味を説明。',
    'Explain the conditions and meaning in English.'
)
```

`figure()`が`figure-`で始まるID、SVGの`title`、キャプションを付けます。同じ図IDを同じページに二度置かないでください。図IDを本文の節IDに使う場合も、生成される`figure-…`と衝突しないようにします。

色だけに意味を持たせず、日英で同じ値・構造を保ちます。模式図、計算例、観測データを明示して区別し、小画面で文字が欠けないことを確認します。

## 7. PDFと配布情報を確認する

新しいPDFを、カタログに書いた`docs/downloads/…`へ原版と同じバイト列で配置します。主論文・補足それぞれのSHA-256を記録し、`verify_site.py`のPDF検査対象へ追加します。現在の検査対象はCAT第4版の2PDFなので、別論文の登録だけではそのPDFの同一性検査は増えません。既存のCAT検査を消さずに拡張します。

共通のダウンロード案内は、カタログの版番号・PDFページ数を読みます。案内先の原資料、検証記録、Releaseタグを同じ版にそろえてください。`source_path`や`archive_slug`を新しくしても、原資料側のREADMEや検証履歴が自動作成されるわけではありません。

図や解説の内容は著者・編集者が用意し、カタログはそれらの対応を指定します。既存CATの文言・図はCAT自身のメタデータに残り、新しい論文へ流用されません。二群の理想帰還の計算は特定の数学的説明なので、新論文と直接の関係がない限り`interactive_return`を有効にしません。

## 8. ビルド、検証、表示確認

リポジトリルートで、Node.jsとPython 3を用意します。Pythonの依存は必要に応じて専用の仮想環境へ入れてください。

```sh
npm ci
python3 -m pip install -r site-src/requirements.txt
python3 tools/build_site.py
python3 tools/verify_site.py
```

ビルドは`docs/`のHTMLと`site-src/build-stats.json`を更新し、検証は`site-src/verification.json`を更新します。検証は、ローカルリンク、原資料リンク、日英の節・図・表示式、重複ID、TL;DR、数式エラー、登録済みPDFのハッシュを確認します。終了コードと`error_count`を確認してください。

表示確認は例えば次のローカルサーバーから行えます。

```sh
python3 -m http.server 8000 --directory docs
```

日英の共通入口、分野、論文入口、3水準の全6記事を開きます。PCと狭い画面で、目次、長い数式・表・図の横スクロール、言語切替、他水準への移動、PDFと出典を確認します。構造検査だけでは、翻訳の同等性や科学的内容の正しさは検査されません。

カタログからの削除・改名では、古い生成HTMLは自動削除されません。残す版へのリンクを整理したうえで、不要な旧生成ページを個別に確認します。ビルド後の差分では、意図した解説・カタログ・生成物の変更と、変更してはいけない原論文を区別してください。

公開操作はこの工程と別です。実際にpush・Pages設定・Release作成を済ませ、公開URLで結果を確認するまでは、準備済みの状態を公開済みと記載しません。
