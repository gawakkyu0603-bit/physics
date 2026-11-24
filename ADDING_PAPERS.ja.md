# 新しい論文の追加・改訂・公開の運用メモ

[リポジトリの案内（英語）](README.md) · [サイト生成元の詳細仕様](site-src/README.md)

このメモは、今後の論文を同じ `physics` リポジトリへ追加し、原資料、再現資料、英語3水準の紹介ページを一貫した状態で公開するための作業手順です。今回・今後とも公開する論文紹介は英語の一般・理工系学生・専門家向け3記事とし、公開用のルート・分野・論文・版のREADMEは英語に統一し、READMEの日本語別版は作成しません。日本語の運用メモは管理資料として残します。命名例として用いる「恒星振動の論文」は架空の作業例であり、実際に収録した研究や検証結果を示しません。コマンドは、特記しない限りリポジトリのルートで実行します。

## TL;DR

1. 受領した原稿を確定し、**分野 → 論文 → 版 → `paper/`** に保持します。過去版を上書きせず、原本と配布物のハッシュを記録します。
2. 分野・論文のREADMEと版ごとの検証・引用・権利・配布情報を作り、`site-src/catalog.json` に今回案内する版を登録します。
3. **一般・理工系学生・専門家向けの英語3記事**を作成します。各記事の冒頭はTL;DRとし、論文・補足の全論点、成立条件、検証案、未解決事項を、その読者が理解できる深さで扱います。
4. 本文・図・数式・出典の対応を確認し、PDFを `docs/downloads/` に配置します。新論文のPDFハッシュ検査も追加して、ビルド、構造検証、原論文との内容照合、画面確認を行います。
5. 原資料と生成済み `docs/` を同じコミットに含め、`main` に反映します。確定コミットへ論文固有のタグを付け、そのタグのReleaseに配布物を添付します。Pagesの配信元は **`main` ブランチの `/docs`** です。
6. 公開URL、英語3記事の相互リンク、PDF、タグ固定の出典、Releaseの添付資料を実際に確認します。今回の初回公開では、リポジトリ・タグ・Release添付・Pagesのすべての公開作業と公開確認が完了した後に、Google・Bing・Yahoo向けの初回申請を行います。申請の受付と検索への収録を区別し、定期監視や繰り返しの再申請は行いません。

## 1. 公開先と管理単位

既存の公開先を使います。論文ごとに新しいリポジトリを作る必要はありません。

| 対象 | このリポジトリでの指定 |
| --- | --- |
| GitHub | [gawakkyu0603-bit/physics](https://github.com/gawakkyu0603-bit/physics) |
| Pagesの基底URL | `https://gawakkyu0603-bit.github.io/physics/` |
| 配信するブランチ・ディレクトリ | `main` / `docs` |
| 掲載内容の登録 | [site-src/catalog.json](site-src/catalog.json) |
| サイトの生成 | [tools/build_site.py](tools/build_site.py) |
| サイトの構造・リンク等の検証 | [tools/verify_site.py](tools/verify_site.py) |

原資料の版と、現在の紹介ページを分けて管理します。原資料の例は `stellar-physics/compact-star-modes/v1/paper/`、紹介ページの例は `en/stellar-physics/star-modes/expert.html` です。**現在の紹介ページURLには版番号が含まれません。** 同じ `field` と `slug` を持つ項目を複数登録すると、同じ出力先へ書き込まれます。

通常はカタログに、その論文について現在案内する一版だけを置きます。改訂時は原資料の `v1/` を残して `v2/` を追加し、カタログの版・タグ・原資料パス・PDF・解説をそろえて切り替えます。過去版へは論文README、版ディレクトリ、タグ、Releaseからアクセスできるようにします。過去版の紹介サイトも同時に配信したい場合は、別のURL設計と生成・検証処理の変更が必要です。現在のコードが版別サイトを自動的に保存するわけではありません。

### 名前を先に確定する

| 用途 | 架空の新規論文の例 | 留意点 |
| --- | --- | --- |
| 分野 `field` | `stellar-physics` | 同じ分野の既存登録があれば再利用する |
| 原資料側の論文名 `archive_slug` | `compact-star-modes` | 分野配下のディレクトリ名と一致させる |
| Pages側の論文名 `slug` | `star-modes` | 分野内で一意にする。公開後の変更はURL変更になる |
| 版 `version` | `"1"` | 原資料の `v1/` と対応する文字列 |
| Releaseタグ `release` | `star-modes-v1.0.0` | 論文名を含め、他論文のタグと区別する |
| 本文の接頭辞 `content_prefix` | `star-modes-` | 他論文と共用しない。CATの空文字を再利用しない |

## 2. 開始前にそろえる資料と作業場所

先に、確定版の主論文・補足・ソース・データ・実行手順、著者名、題名、版、日付、引用情報、配布条件を確認します。既に実行した検証については、対象版、コマンド、環境、入力、結果、失敗例、未実行範囲が分かる記録を用意します。これらが不足するときは、足りない項目を明示し、実行済み・取得済みとして記載しません。

未反映の作業がないか確認した後、専用の作業ブランチを使います。既存の変更がある場合は、その変更を担当者と整理してから切り替えてください。

```sh
git status --short
git switch main
git pull --ff-only origin main
git switch -c add-star-modes-v1
```

大きい原本アーカイブ、Release添付用の作業ファイル、仮想環境は、例えばリポジトリの隣のディレクトリで管理します。配布物をGitへ誤って二重追加しないためです。公開用に準備するファイルには、認証情報や個人用の作業メモを含めません。

## 3. 原資料と版ごとの説明を置く

新しい分野を作る場合は `stellar-physics/README.md`、論文には `stellar-physics/compact-star-modes/README.md` を用意し、分野の索引、論文の概要、公開版へのリンクを記載します。ルートの英語 [README.md](README.md) の研究索引も更新します。これらの原資料側READMEは、サイトのビルドでは自動生成されません。

| 版ディレクトリの内容 | 記録すること |
| --- | --- |
| `paper/` | 受領した原稿・ソース・データ・コード。解説の都合で書き換えない |
| `README.md`（英語） | 版の内容、読む順序、再現手順、主要ファイル、配布物へのリンク |
| `VERIFICATION.md` | この版で確認した事実、以前の版から引き継ぐ証拠、今回実行していない範囲 |
| `RELEASE_NOTES.md` | 初版の範囲、または前版との差分と公開上の変更 |
| `CITATION.cff` / `CITATION.bib` | 実際の著者、題名、版、公開日、URL。DOIは取得した場合だけ記載 |
| `RIGHTS.md` / `THIRD_PARTY_NOTICES.md` | 原研究と第三者資料の権利・配布条件。確認した条件を記載 |
| `PUBLICATION_MANIFEST.json` | 原本との対応、保持・除外の範囲、版内各ファイルのサイズとSHA-256 |
| `release-assets.json` | 実際に添付するファイル名、サイズ、SHA-256、Releaseタグ、ダウンロード先 |

CATの [第4版ディレクトリ](quantum-gravity/correlation-actualization-theory/v4/README.md) は書式の参考にできます。ただし、原本のファイル数、実行済み検証、著者、ライセンス、AI利用、査読状況、ハッシュ値は論文ごとに確認します。CATの値や表現を新しい研究へコピーしただけで検証記録にはなりません。

原資料をGitから一部除外する場合は、対象のパスと理由、完全配布物に含むかどうかを明記します。原本と配布物がどの範囲で同一なのかを、ファイル数とハッシュで追跡できるようにします。原稿に修正が必要なら、修正内容を記録した新しい版として扱います。

## 4. カタログへ分野と論文を登録する

`site-src/catalog.json` の既存項目を保ったまま追加します。トップレベルの `languages` は `["en"]` を維持し、各論文の `languages` も `["en"]` とします。新しい分野なら `fields` 配列へ、次の形式の項目を加えます。

```json
{
  "slug": "stellar-physics",
  "name": {"en": "Stellar physics"},
  "summary": {
    "en": "Papers and explanations on stellar structure and oscillations."
  }
}
```

`papers` 配列へ追加する最小構成の例です。題名・著者・日付・説明は、実際の新しい論文で置き換えます。

```json
{
  "slug": "star-modes",
  "field": "stellar-physics",
  "archive_slug": "compact-star-modes",
  "title": "Example paper title",
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
  "languages": ["en"],
  "summary": {
    "en": "The actual research question and the scope of the results."
  }
}
```

`source_path` はリポジトリルートから、PDFパスは `docs/` からの相対パスです。記事末尾の検証記録へのリンクは `field/archive_slug/vVERSION/VERIFICATION.md` から組み立てるため、この組合せも実際の配置と一致させます。`public_base_url` は末尾の `/physics/` を含む既存値を維持します。

読みやすい案内のため、確認できた値を `short_title`、`page_counts`、`audience_descriptions`、`reading_times`、`scope` に追加します。完全な書式と未指定時の動作は [サイト生成元の詳細仕様](site-src/README.md) を参照してください。ページ数や読了時間は、原稿・本文で確認した値を使います。`hero_figure` を指定する場合は、先にその図を登録します。

現在の共通画面は主論文と補足の2種類のPDFを前提にしています。補足のない論文を扱う場合は、空のPDFや無関係なPDFを指定せず、画面・ビルダー・検証の対応を先に変更します。また、`interactive_return` はCAT固有の二群の理想帰還を説明する機能です。別論文では原則として省略または `false` とし、その数学的内容が本当に必要な場合だけ個別に検討します。

## 5. 英語・3水準の本文をそろえる

上の接頭辞に対応する本文素材は、次の3ファイルです。今後の論文にもこの3本を用意します。

| 読者 | 英語の本文素材 |
| --- | --- |
| 一般読者 | `site-src/content/star-modes-general-en.html` |
| 理工系学生・卒業者 | `site-src/content/star-modes-student-en.html` |
| 専門家 | `site-src/content/star-modes-expert-en.html` |

**論文全体を理解できる英語3本の解説を作ります。** 本文と補足の各節、主要な定義・仮定・結果、比較対象、全ての検証案、反例や不成立条件、限界を先に洗い出してください。それぞれの水準で、導入から結論まで読み通せる順序へ組み替えます。

| 読者 | 前提と説明の深さ | 数式・図の使い方 |
| --- | --- | --- |
| 一般読者 | 科学雑誌Newton程度を目安に、研究上の問い、具体例、機構、結果の意味を順に説明する。必要な用語は本文で定義する | 数式が必要な箇所は記号と意味を言葉で補う。模式図・具体的な数値例を中心にし、比喩と物理的主張を区別する |
| 理工系学生・卒業者 | 学部程度の数学・物理から、論文独自の定義や道具へ橋を架ける。途中式や具体的な計算例を示す | 基本式、単位、仮定、極限を説明し、図の値と計算を対応させる |
| 専門家 | 定義、定理や主張の条件、導出の要点、既存理論との差、検証の再現方法を精密に扱う | 論文の記号との対応、式番号、数値条件、出典・コード・証拠への参照を付ける |

3水準とも研究テーマ、条件、結論、限界、出典を漏れなく扱い、数値や図の意味を原論文とそろえます。説明の深さを変えても、条件付きの結果を断定に変えません。英語として自然で読みやすい文章を用い、文量に一律の上限は設けず、前提知識から論理の橋を渡すために必要な説明を確保します。長くなる場合は段落・節・目次で整理します。

### カバレッジと出典の対応を残す

[site-src/COVERAGE.md](site-src/COVERAGE.md) に論文別の項目を追加し、少なくとも次の列を持つ対応表を用意します。論点を一つずつ照合し、未対応を残さないことが目的です。

| 原資料の位置 | 論点・条件 | 一般EN | 学生EN | 専門家EN | 裏付け |
| --- | --- | --- | --- | --- | --- |
| 主論文の節・式番号、補足の節 | 何を説明し、何を仮定しているか | 対応節ID | 対応節ID | 対応節ID | PDFページ、ソース、データ、実行記録 |

「全部扱った」という宣言だけで済ませず、補足の結果、検証計画、否定的結果、未解決事項まで表で点検します。[site-src/SCIENTIFIC_QA.md](site-src/SCIENTIFIC_QA.md) にも、新しい論文の内容照合、修正点、未確認範囲を追記します。図の中の数値・注記も本文と同じ精度で照合してください。

## 6. 本文・数式・出典リンクの書式

本文素材はHTMLページ全体ではなく、一つの `article` を含む断片です。次は書式だけを示す例です。

```html
<article lang="en">
  <header class="article-header">
    <h1>A guide for this audience</h1>
    <p class="lead">Introduce the background and the research question.</p>
  </header>
  <aside class="tldr" id="star-modes-student-tldr">
    <h2>TL;DR</h2>
    <p>State the question, results, conditions, and open problems.</p>
  </aside>
  <section id="star-modes-student-model">
    <h2 id="star-modes-student-model-heading">Model and conditions</h2>
    <p>Define the notation, then explain the equations and examples.</p>
    <div data-figure="star-modes-student-overview"></div>
    <p><a href="{{PAPER_PDF}}#page=2">Relevant page in the paper</a></p>
    <p><a href="{{SUPP_PDF}}#page=3">Relevant page in the supplement</a></p>
    <p><a href="{{SOURCE_ROOT}}/main.tex">Original source file</a></p>
  </section>
</article>
```

ビルダーはTL;DRを記事本文の先頭へ移し、題名を共通ヘッダーへ載せ、`h2` から目次を作ります。ページ内のIDを一意にします。共通ナビゲーションには、同じ論文の他水準と論文入口へのリンクが生成されます。手作業の本文リンクでも、実際の移動先を確認してください。

`{{PAPER_PDF}}` と `{{SUPP_PDF}}` は配信PDFへのリンク、`{{SOURCE_ROOT}}` はカタログのReleaseタグに固定したGitHub原資料リンクに置換されます。例のページ番号・ファイル名は必ず原稿で置き換えます。存在しない `main.tex` や、版の異なるページ番号をそのまま残しません。

インライン数式は `\(...\)`、表示数式は `<div class="equation">\[...\]</div>` を使います。記号を導入し、単位や成立条件を近くに書き、複雑な式は意味が追える単位に分けます。長い式は狭い画面でも読めるか確認します。HTML中の不等号などは必要に応じて `&lt;` / `&gt;` にします。表示式を原論文と照合し、KaTeXの変換エラーがあればビルドを修正してから進めます。

## 7. カラフルで正確な図表を作る

[site-src/figures.py](site-src/figures.py) に `lang` を受け取り、SVG内部文字列と高さを返す名前付き関数を追加します。現在の共通幅は880です。既存の描画補助関数を利用でき、本文には図IDで埋め込みます。

```python
# star_modes_overview(lang) を先に定義してから登録する。
MAP['star-modes-student-overview'] = star_modes_overview
CAPTIONS['star_modes_overview'] = (
    '', 'English figure title',
    '',
    'English explanation with conditions, units, sources, and scope.'
)
```

`MAP` のキーは本文の `data-figure` に対応し、`CAPTIONS` のキーは**関数名**です。現行の図APIは4要素の組を読み、英語では第2要素の題名と第4要素の説明を使います。上の例の空文字は未使用要素の位置を保つもので、追加の言語版を作る必要はありません。図関数には `lang="en"` が渡されます。図には共通処理でSVGのタイトルとキャプションが付きます。生成される図のIDは `figure-図ID` です。同じ図IDを同一ページに二度使うとIDが重複するため、繰り返して載せる場合は別の図IDを登録します。

機構の模式図、量の比較、工程図、条件と結果の対応表などを、読者がつまずく箇所へ配置します。装飾を増やすことよりも、本文の理解を進める役割を持たせます。色には英語のラベルや線種を併用し、図と本文で数値・配置・色の意味を一致させてください。

計算図は元データと処理を追跡できるようにし、軸、単位、パラメータ、誤差、適用範囲を明示します。模式図・仮定した模型・計算結果・観測データを区別します。未実施の実験や未検証の予測を、観測済みの結果として描かないことが科学的な説明の基本です。

## 8. PDFを配置し、同一性の検査対象を増やす

ビルダーはPDFをコピーしません。確定した原版のバイト列を `docs/downloads/star-modes-v1-main.pdf` と `docs/downloads/star-modes-v1-supplement.pdf` へ配置します。原資料、Pages、Releaseの3か所で同じPDFを配る場合は、SHA-256が一致することを確認します。

次は原資料側が `paper/main.pdf` と `paper/supplement.pdf` の場合の確認例です。異なる名前なら実際のパスへ変更します。

```python
from pathlib import Path
import hashlib

pairs = [
    ('stellar-physics/compact-star-modes/v1/paper/main.pdf',
     'docs/downloads/star-modes-v1-main.pdf'),
    ('stellar-physics/compact-star-modes/v1/paper/supplement.pdf',
     'docs/downloads/star-modes-v1-supplement.pdf'),
]
for original, served in pairs:
    expected = hashlib.sha256(Path(original).read_bytes()).hexdigest()
    actual = hashlib.sha256(Path(served).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f'PDF differs: {served}')
    print(served, Path(served).stat().st_size, actual)
```

現行の `tools/verify_site.py` の `expected` 辞書にはCAT第4版の2PDFが登録されています。**カタログへ論文を加えても、新論文のPDFハッシュ検査は自動では増えません。** 上で得た新PDFのハッシュを検査対象へ追加し、既存のCAT検査を残します。将来この仕組みを一般化する場合も、期待値は確認済みの原本から独立に記録し、検査のたびに検査対象自身から期待値を生成しないようにします。

## 9. ビルドと、機械・内容・表示の3段階の確認

### 9.1 生成と構造検証

Node.js、npm、Python 3を用意します。仮想環境を作る場合は、現在の `.gitignore` が任意の仮想環境名を除外する前提にせず、リポジトリの外へ作ります。

```sh
python3 -m venv ../physics-site-venv
. ../physics-site-venv/bin/activate
python3 -m pip install -r site-src/requirements.txt
npm ci
python3 tools/build_site.py
python3 tools/verify_site.py
git diff --check
git diff --stat
```

`npm ci` はロックファイルに従って依存を入れます。`npm run build` / `npm run verify` は上のPythonコマンドに対応します。ビルドはHTML、`docs/sitemap.xml`、`docs/<確認キー>.txt`、`site-src/build-stats.json` を更新し、検証は `site-src/verification.json` を更新します。確認キーファイルには `site-src/indexnow.json` の同じ公開用キーを使い、通常の論文追加時に作り直しません。CSS・JavaScript・フォント等の配信資産は、必要に応じて別途配置・更新します。

検証の終了コードが0、`error_count` が0であることを確認します。検査項目には、ローカルファイル・アンカー、原資料パス、ID、TL;DR、KaTeX、設定した公開言語・記事、登録済みPDFのハッシュ、canonical URL、英語の自己参照等のhreflang、サイトマップのURL範囲が含まれます。今回の1論文では7 HTMLと2 PDF、計9 URLがサイトマップの対象です。新しい論文を加えたときは、実際の掲載内容に対応する件数を確認します。

ここで原資料へのGitHubリンク検査が確認するのは、対応する**ローカルファイルの存在**です。リモートのタグが作成済みか、公開先でダウンロードできるかは別に確認します。また、検査対象のページ数は掲載論文数により増えるため、CATだけの件数を固定の成功条件にしません。

### 9.2 原論文と内容の照合

原論文・補足とカバレッジ表を照合し、英語3記事を読みます。仮定、式、数値、単位、図、出典、条件付きの結論が一致することを確認します。解説で加えた計算例は、解説用の例であることを明示して再計算します。科学的な正しさ、網羅性、読者に応じた説明の十分さは、構造検証が成功しても保証されません。

### 9.3 PCと狭い画面で読む

```sh
python3 -m http.server 8000 --directory docs
```

`http://localhost:8000/` から英語のトップ、分野、論文入口、3水準の全3記事を開きます。本文の行長、段落、見出し、目次、数式、表、図の文字、横スクロール、他水準への移動、PDFと原資料へのリンクを確認します。一般向けは初見の読者の立場で読み、専門家向けは出典から主張を追えるか確認します。

カタログの削除・改名では、古い生成HTMLは自動削除されません。URLを変更した場合は、旧ページを残すか案内ページにするかを決め、古い内容が意図せず配信され続けないよう個別に確認します。差分に原論文の意図しない変更が含まれていないことも確認します。

## 10. Release添付資料とマニフェストを確定する

GitHubの自動ソースアーカイブと、論文用に用意する配布物は内容が異なります。GitHubの自動 `Source code (zip)` / `Source code (tar.gz)` は、そのタグ時点のリポジトリ全体です。複数論文のリポジトリでは、他論文も含むGitツリーになります。Gitに含めなかった実行環境などを加える機能ではありません。[GitHubのRelease説明](https://docs.github.com/en/repositories/releasing-projects-on-github/about-releases)も参照してください。

CATと同様の構成で配布する場合は、次の5点を用意します。論文に必要な資料の範囲に合わせ、内容と名称を版のREADMEに明記します。

| 添付物 | 役割 |
| --- | --- |
| 主論文PDF | 読むための確定版。Pages掲載PDFと一致させる |
| 補足PDF | 主論文を支える導出・検証・追加資料 |
| 論文ソース `tar.gz` | 論文の再ビルドに必要な実際のソース集合 |
| 完全配布ZIP | 原本の資料全体と必要な再現資源。Gitから省いた資料の有無を明記 |
| `SHA256SUMS` | 上の配布ファイルのハッシュ一覧。自身を対象に含めない |

`PUBLICATION_MANIFEST.json` は、CATの [既存書式](quantum-gravity/correlation-actualization-theory/v4/PUBLICATION_MANIFEST.json) を参考に、新しい版の実際の内容から作ります。パスの基準は版ディレクトリで、マニフェスト自身は対象外です。版内のREADME等を直した場合もハッシュの更新が必要です。`release-assets.json` には別途、完成した添付物のサイズ・ハッシュ・URLを記録します。両者は対象の異なる記録です。

現行のサイト生成コマンドは、原資料の取り込み、配布ZIP、ソースアーカイブ、マニフェスト、Releaseを自動作成しません。これらを完成させてから公開コミットを確定します。アーカイブ内のパス、展開後のファイル一覧、原本とのハッシュ対応を調べ、単に圧縮できたことだけで完全性を判断しません。

例えば添付物を `../star-modes-release-assets/` に用意した場合、次のようにチェックサムを作れます。実際のファイル名に合わせてください。

```sh
(
  cd ../star-modes-release-assets || exit 1
  sha256sum star-modes-v1-main.pdf star-modes-v1-supplement.pdf \
    star-modes-v1-source.tar.gz star-modes-v1-full-bundle.zip > SHA256SUMS
  sha256sum --check SHA256SUMS
)
```

## 11. Git、タグ、Release、Pagesへ順に反映する

### 11.1 変更をレビューしてmainへ反映する

追加した原資料、説明、カタログ、本文素材、図、検証処理、生成物を同じ作業ブランチで確認します。次は追加するファイルを明示する一例です。実際に変更した範囲に合わせます。

```sh
git add stellar-physics README.md site-src tools/verify_site.py docs
git diff --cached --stat
git diff --cached --check
git commit -m "Add star modes v1 paper and three English reading guides"
git push -u origin add-star-modes-v1
```

ビルダー等も変更した場合は、その変更も明示的に追加します。GitHubでこのブランチから `main` へのPull Requestを作り、原本・解説・配布情報・生成物が対応していることを確認してマージします。公開対象が確定してから、ローカルの `main` を最新にします。

```sh
git switch main
git pull --ff-only origin main
git status --short
git rev-parse HEAD
```

ここで表示したコミットを、検証記録・公開作業記録に残します。未反映の差分があるままタグを付けないでください。

### 11.2 確定コミットに論文固有のタグを付ける

次は新規タグの作成例です。既存タグの移動・上書きには使いません。

```sh
paper_tag=star-modes-v1.0.0
paper_publication_commit=$(git rev-parse HEAD)
git tag -a "$paper_tag" "$paper_publication_commit" -m "Star modes version 1"
git push origin "refs/tags/$paper_tag"
```

カタログが参照するタグと一致させます。タグ公開後の修正は履歴に残し、新しい版・配布改訂のタグを用意します。同じ原稿版の解説だけを改良する場合は、原稿をそのままにして変更理由と対象を記録し、`main` の紹介ページを更新できます。

### 11.3 Releaseに添付する

GitHub画面から作成しても、認証済みのGitHub CLIから作成しても構いません。CLIを用いる場合の例です。ファイル内容とタグを先に確認します。

```sh
gh release create star-modes-v1.0.0 \
  --repo gawakkyu0603-bit/physics \
  --verify-tag \
  --latest=false \
  --title "Star modes — version 1" \
  --notes-file stellar-physics/compact-star-modes/v1/RELEASE_NOTES.md \
  ../star-modes-release-assets/star-modes-v1-main.pdf \
  ../star-modes-release-assets/star-modes-v1-supplement.pdf \
  ../star-modes-release-assets/star-modes-v1-source.tar.gz \
  ../star-modes-release-assets/star-modes-v1-full-bundle.zip \
  ../star-modes-release-assets/SHA256SUMS
```

`--verify-tag` は、リモートにそのタグがなければ作成を中止する指定です。`--latest=false` はこのReleaseをリポジトリ全体の「Latest」にしない指定です。複数論文の最新版は、全体のLatest表示だけに依存せず、各論文のカタログ・索引・タグで案内します。指定の意味は [GitHub CLIの公式マニュアル](https://cli.github.com/manual/gh_release_create) で確認できます。

### 11.4 Pagesの配信元を確認する

リポジトリの **Settings → Pages → Build and deployment** で、Sourceを **Deploy from a branch**、Branchを **main**、Folderを **/docs** にします。既にこの設定なら論文ごとの再設定は不要です。生成した `docs/` を `main` に反映した後、Pagesのデプロイ結果を確認します。ローカルでビルドが成功しただけでは公開完了ではありません。[GitHub Pagesの公式設定手順](https://docs.github.com/en/pages/getting-started-with-github-pages/configuring-a-publishing-source-for-your-github-pages-site)を参照してください。

公開途中では、Pagesが先に更新されタグやReleaseがまだ存在しない時間帯があり得ます。全ての公開先の確認が終わるまで、完了として案内しません。

## 12. 公開後の確認と今回の初回申請

公開サイトのトップから新しい分野・論文へ進み、英語3記事を実際に開きます。ブラウザーのキャッシュやローカルプレビューでなく、公開URLを確認してください。

- 全記事でTL;DRが冒頭にあり、読者水準切替・PDF・原資料へ移動できる。
- Releaseのタグが記録したコミットを指し、全添付物を取得できる。取得した配布物を `SHA256SUMS` と照合できる。
- PagesのPDFが原本と一致し、タグ固定の原資料・検証記録へのリンクが公開先でも開く。
- `https://gawakkyu0603-bit.github.io/physics/sitemap.xml` に新しいHTMLと登録したPDFが含まれ、canonicalと英語のhreflangが実URLに対応する。
- READMEの研究索引、論文の版一覧、Release、Pagesが同じ版を案内している。

今回の公開では、リポジトリ・タグ・Release添付・Pagesのすべての公開作業と確認が完了した後に、Google Search ConsoleとBing Webmaster Toolsで初回の登録・サイトマップ送信を行い、BingへIndexNowで通知します。Yahoo! JAPANはGoogle、海外Yahoo SearchはBing Webmaster Toolsの関連経路を使います。申請先の所有権確認には実際に発行された値を用い、申請・受付と検索への収録を区別します。この依頼に定期監視や繰り返しの再申請は含めません。

## 13. 完了記録と次回への引き継ぎ

次の内容を論文の公開作業記録へ残すと、改訂時に取り違えを防げます。再現用コマンドや検証ログは、後から担当者が確認できるパスへ保存します。

| 記録項目 | 書く内容 |
| --- | --- |
| 論文の識別 | 題名、著者、分野、`archive_slug`、`slug`、原稿版、日付 |
| 原本と保持範囲 | 原本アーカイブのSHA-256、保持・除外したファイルの数とパス、完全配布物との対応 |
| 公開位置 | `main` の確定コミット、論文固有タグ、Release URL、英語の論文入口と3記事のURL |
| 生成・機械検証 | 実行コマンド、環境、終了コード、検証記録のパス、PDFハッシュ |
| 内容・表示確認 | カバレッジ表、原論文との照合、図表・数式・出典の点検、PCと狭い画面での確認 |
| 検証の範囲 | 今回実行したもの、過去の版の記録を参照したもの、今回未確認のもの |
| 配布物 | 実際の添付ファイル一覧、サイズ、SHA-256、ダウンロード確認結果 |
| 今回の初回申請 | 申請先、送信日時、実際の応答。受付だけで収録済みと扱わない |
| 次の作業 | 残る研究課題と、残る公開作業をそれぞれ具体的に記録 |

次の論文を追加するときは、まずこの記録と [サイト生成元の詳細仕様](site-src/README.md) を読み、実際のコードが更新されていれば手順との差を確認します。過去の論文の原資料と公開タグを保持しながら、新しい資料・解説・配布物を追加していきます。
