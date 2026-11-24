# 生データ・大型資料の外部保存マニフェスト

`.gitignore`で`data/raw/`の内容は初期状態ではGitから除外されます。原本の保存先を明示し、必要に応じてGit LFS等の管理方式に変更してください。

| データID | 資料の出所 | 保存先（必要なら非公開） | SHA-256 | 取得日/版 | 再現・復元方法 |
|---|---|---|---|---|---|
| DAT-0001 | Maas・Plätzer・Pressler の公開四次元CDT計算、Zenodo 20589545 | [抽出ヘッダー](cdt-20589545-profiles.json)・[原本とライセンス](CDT-DATA.md) | 選択した各ファイルは JSON 内。抽出集合は[再現マニフェスト](../verification/verification-record.json) | 2026-11-18、原本 v1 | [取得・オフライン解析コード](../code/cdt_public_profiles.py) |
| DAT-0002 | RIT BSSN非回転ブラックホール合体5試行の公開HDF5と個別メタデータ | [取得・版・分解能](RIT-MERGERS.md)・[積分後の値](processed/rit-merger-flux.json) | [10原本](rit-merger-files.json) | 2026-11-21、n100 / n140 | [波形の再取得・再積分](../code/rit_merger_flux.py) |
