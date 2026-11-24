# 検索エンジンへの登録リクエストと更新時の運用

この文書は、リポジトリ・タグ・Release添付・GitHub Pagesのすべての公開作業が完了し、実際の公開URLを確認した後に、Google・Bing・Yahoo向けのインデックス登録リクエストを行うための運用方針と手順です。今回以降の論文も、英語の専門家・理工系学生・一般読者向けの3記事を公開し、各冒頭のTL;DR、論文・補足の網羅、十分な説明を維持します。公開用READMEは英語に統一し、日本語のREADME別版は作りません。手順や設定ファイルが存在するだけでは、リクエストの送信やインデックス登録は完了していません。送信日時、対象URL、実際の応答を作業記録に残してください。

## 1. 公開元と、送信前の確認

対象サイトは `https://gawakkyu0603-bit.github.io/physics/` です。GitHub Pagesは`main`の`docs/`を配信します。新しい論文の追加手順は[ADDING_PAPERS.ja.md](ADDING_PAPERS.ja.md)にあります。

1. 原稿・英語3水準の説明・リンクを完成させ、`python3 tools/build_site.py`と`python3 tools/verify_site.py`を実行します。
2. `docs/`、生成元、検証結果を同じコミットで公開します。リポジトリ、論文固有タグ、Releaseと全添付資料、Pagesのすべてが公開済みで、原資料リンクと配布物のサイズ・ハッシュが一致することを確認します。
3. 対象URLと[サイトマップ](https://gawakkyu0603-bit.github.io/physics/sitemap.xml)が公開状態で取得できることを確認してから、以下の送信を実行します。

ビルドはcanonical・英語の自己参照等のhreflangと`sitemap.xml`を生成します。サイトマップには生成したHTMLとカタログ登録済みの主論文・補足PDFが入ります。今回の英語3記事の構成は、共通入口・英語トップ・分野・論文入口と3記事の7 HTML＋2 PDF、計9 URLです。今後の論文も英語3水準で追加します。確認用キーのファイルはサイトマップに掲載しません。

## 2. Google Search Console

プロパティは **URLプレフィックス** `https://gawakkyu0603-bit.github.io/physics/` とします。DomainプロパティにはDNSの確認が必要です。HTMLタグまたはHTMLファイル方式では、Search Console画面で実際に発行された値を指定位置へ公開し、画面の「確認」を実行します。確認タグ・ファイルは検証後も保持します。[Googleの所有権確認手順](https://support.google.com/webmasters/answer/9008080?hl=ja)

HTMLファイル方式では、確認ファイルをリポジトリ直下だけに置いてもPagesから配信されません。必ず `docs/google....html` に配置し、`https://gawakkyu0603-bit.github.io/physics/google....html` で元の内容が取得できることを確認します。現在のビルドはこれらの既存確認ファイルを保持し、サイト検証はファイル名と確認本文の対応を別枠で検査します。確認ファイルは英語3記事やサイトマップのURL数に含めません。配置だけではSearch Consoleの所有権確認や登録申請は完了しないため、画面上の確認結果を別に記録してください。

所有権確認後、「サイトマップ」から公開済みの`sitemap.xml`を送信し、個別URLは「URL検査」から「インデックス登録をリクエスト」を実行します。受付日時と対象を記録します。日次上限に達した場合は反復送信せず、未送信の対象を記録してください。受付後のクロールや収録はGoogle側で判断されます。[URL検査](https://support.google.com/webmasters/answer/9012289?hl=ja)・[サイトマップ](https://support.google.com/webmasters/answer/7451001?hl=ja)

GoogleのIndexing APIは求人情報または所定のライブ配信動画向けであり、この論文サイトには使用しません。[APIの対象範囲](https://developers.google.com/search/apis/indexing-api/v3/quickstart)

## 3. Bing Webmaster Toolsへの登録とIndexNow通知

### Bing Webmaster Toolsでサイトを追加する

[Yahoo Searchの公式登録案内](https://ca.help.yahoo.com/kb/SLN2217.html)は、Bing Webmaster Toolsからサイトを登録するよう案内しています。全公開作業が完了した後、[Bing Webmaster Tools](https://www.bing.com/webmasters/)で対象のサイトURL `https://gawakkyu0603-bit.github.io/physics/` を追加します。画面で提示された方法と値を使って所有権を確認し、公開済みの `https://gawakkyu0603-bit.github.io/physics/sitemap.xml` を送信します。Google Search Consoleからインポートする場合も、対象のサイトと権限を確認します。サイト追加・所有権確認・サイトマップ送信はそれぞれの実際の画面結果と日時を記録します。

以下のIndexNow通知は、URLの追加・更新を伝える別の経路です。IndexNowが受付済みであっても、Bing Webmaster Toolsでのサイト登録や、Bing・Yahooでの収録が完了したとは扱いません。

### 設定と確認キー

| ファイル | 役割 |
| --- | --- |
| `site-src/indexnow.json` | サイトURL、継続して使う32桁の確認キー、公開するキーのURL |
| `docs/<確認キー>.txt` | キーだけを記したUTF-8の公開確認ファイル |
| `tools/submit_indexnow.py` | ローカル検証、公開状態の確認、1回のIndexNow送信 |
| `.github/workflows/submit-indexnow.yml` | 手動実行専用のGitHub Actionsワークフロー |

確認キーは、このサイトの該当場所へファイルを置けることを示す公開用の値です。GitHubやGoogleのログイン情報は使いません。キーは最初に作成したものを設定ファイルへ保存し、以後のビルドは同じ値で確認ファイルを生成します。通常の論文追加で作り直さないでください。公開先を移す場合は`catalog.json`の`public_base_url`と`indexnow.json`のサイト・キーURLをそろえ、移転先で公開確認してから送信します。

このプロジェクトはホスト直下ではなく`/physics/`にあるため、送信JSONに`keyLocation`を必ず含めます。このキーは`/physics/`配下のURLにだけ使います。[IndexNowの確認方法と適用範囲](https://www.indexnow.org/documentation)

### ローカルから実行する

追加パッケージは不要で、Python標準ライブラリを使用します。リポジトリのルートで、まずネットワーク通信を行わない検証を実行します。

```bash
python3 tools/submit_indexnow.py --dry-run --output indexnow-dry-run.json
```

公開と確認が完了してから実際に送信します。

```bash
python3 tools/submit_indexnow.py --output indexnow-result.json
```

スクリプトは、URLが設定したHTTPSのホストと`/physics/`配下に収まること、対応するローカルファイル、キー、サイトマップを確認します。実送信ではさらに公開済みキーと公開済みサイトマップを確認し、ローカルのURL集合と一致してから `https://www.bing.com/indexnow` へ1回だけJSONをPOSTします。自動再試行はありません。

初回はサイトマップの全URLを対象にします。その後、一部だけ追加・更新した場合は、サイトマップにある変更対象を`--url`で選べます。複数の場合はこの引数を繰り返します。

```bash
python3 tools/submit_indexnow.py --dry-run \
  --url https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/general.html \
  --url https://gawakkyu0603-bit.github.io/physics/en/quantum-gravity/cat/expert.html
```

URLは実際に変更したページへ置き換え、検証後に`--dry-run`を外します。本スクリプトは現在のサイトマップに存在するページの追加・更新用です。削除済みページの通知は扱いません。IndexNowの上限は1回10,000 URLです。[Bingの導入手順](https://www.bing.com/indexnow/getstarted)

### GitHub Actionsから手動実行する

リポジトリの **Actions → Submit published URLs to IndexNow → Run workflow** を開き、配信済みのコミットを含むブランチを選びます。`dry_run`は既定で有効です。まず検証を実行し、実送信時だけ無効にします。

このワークフローにはpush・定期実行・Pages完了時の自動トリガーを設けていません。権限は`contents: read`だけで、指定コミットを公開Git経由で取得します。外部Actionや個人アクセストークンは使いません。完了後は実行ログとSummaryのJSONを保存・参照します。公開前のコミットを選ぶと、実送信時のサイトマップ照合で停止します。

### 応答の読み方

| 応答・結果 | 記録する意味 |
| --- | --- |
| `dry_run_validated` | ローカル検証のみ。送信0回 |
| HTTP `200` / `received` | URL通知の受信を確認。クロール・インデックス登録は未確認 |
| HTTP `202` / `received_key_verification_pending` | 通知を受信し、キーの検証待ち |
| HTTP `400` | 要求形式を確認 |
| HTTP `403` | 公開キーの場所・内容・取得可否を確認 |
| HTTP `422` | URLのホスト・範囲・キー形式を確認 |
| HTTP `429` | 過剰送信。連続再試行を行わない |
| 通信エラー | `submission_attempted`でPOSTを試みたかを確認。応答がなければ受付済みとは扱わない |

`200`または`202`の応答は、検索結果への掲載を保証しません。IndexNow参加検索エンジン間で通知が共有される仕組みがありますが、各エンジンの実際の収録状況は別に確認します。[IndexNowの応答仕様](https://www.indexnow.org/documentation)

## 4. Yahooの扱い

**Yahoo! JAPAN**について、LINEヤフーはGoogleの検索エンジンを使用していると説明しています。そのため、このサイトではGoogle Search Console経由の通知を関連する経路として整えます。ただしGoogleへの受付をYahoo! JAPANでの掲載確認やYahoo固有の申請受付とは記録しません。[LINEヤフーの説明](https://privacy.lycorp.co.jp/ja/utilization/)

**海外のYahoo Search**は、公式ヘルプでBing Webmaster Tools経由の登録を案内しています。BingへのIndexNow通知の受付結果と、Yahooの検索結果への反映は別々に記録します。本リポジトリのIndexNowスクリプトは、Yahooアカウントへの直接申請やBing Webmaster Tools内の操作を行うものではありません。[Yahooの登録案内](https://ca.help.yahoo.com/kb/SLN2217.html)

検索結果への反映を確認できた場合だけ、対象サービス・URL・確認日時を記録します。「設定済み」「送信済み」「受付確認」「収録確認」を区別することで、今後の論文追加時にも実際の進捗を追えます。
