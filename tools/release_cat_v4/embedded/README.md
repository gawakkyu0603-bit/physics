# CAT Version 4 — complete publication bundle

Yohtaro Soga · Manuscript dated 25 November 2026

This archive contains every one of the 742 files in the supplied Version 4
research package, unchanged under `CAT-review/`. Distribution notices and
license copies are outside that directory. The new ZIP has its own checksum;
it is not byte-identical to the received ZIP.

## Read

- [Main paper, 18 pages](CAT-review/main.pdf)
- [Technical supplement, 18 pages](CAT-review/supplement.pdf)
- [Reading guide](CAT-review/reading-guide.md)
- [Original package README](CAT-review/README.md)
- [91-result evidence guide](CAT-review/evidence/result_guide.md)
- [Original file manifest](CAT-review/manifest.json)
- [Verification scope](VERIFICATION.md)
- [Third-party terms and attribution](THIRD_PARTY_NOTICES.md)
- [Rights and reuse](RIGHTS.md)

Status: unrefereed research preprint. The technical reviews were AI-assisted;
they are not journal peer review. Author and AI roles are disclosed in the paper.
The finite calculations and Lean assertions retain the assumptions stated there.

## Reproduce

Open a shell in the extracted `CAT-review/` directory and follow its README.
For the Linux integrity check with CPython 3.12:

```sh
cd CAT-review
bash review-linux.sh check
```

For Windows x64 PowerShell:

```powershell
cd CAT-review
.\review-offline.ps1 -Action check
```

The bundled environments include all 33 runtime/dependency files omitted from
the browsing-oriented Git tree. They are preserved with their existing licenses.
`PUBLICATION_MANIFEST.json` records checksums for this archive's contents except
that manifest itself. The external release `SHA256SUMS` identifies this ZIP.

## 日本語

本ZIPは、第四版原本の全742ファイルを `CAT-review/` に変更せず収録した完全配布版です。
配布条件・出典・ライセンスの説明を、その外側に追加しています。
原本内の `manifest.json` と原本ファイルの対応は維持しています。
GitHubの自動生成するソースZIPとは異なり、同梱のオフライン再実行に必要な依存物を含みます。
原稿のAI利用開示と条件付きの検証範囲を維持し、学術誌の査読済みという表示は行っていません。
RITデータ等の再利用条件は `THIRD_PARTY_NOTICES.md` を確認してください。
