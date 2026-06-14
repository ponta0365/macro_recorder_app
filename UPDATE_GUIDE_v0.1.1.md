# v0.1.1 更新手順

次回の配布版を `v0.1.1` として出すときの手順。

1. `macro_recorder_app.py` と関連ドキュメントを修正する。
2. `python -m py_compile macro_recorder_app.py` を通す。
3. `macro_recorder_release.zip` を再生成する。
4. `README.md` と `install.txt` の表記を必要に応じて更新する。
5. Git で変更を commit して push する。
6. GitHub PR を確認して必要ならマージする。
7. `release_notes_v0.1.1.md` を整えてから、`gh release create v0.1.1 macro_recorder_release.zip --title "v0.1.1" --notes-file release_notes_v0.1.1.md` のように新しい Release を作る。

注意:
- 配布用 zip はリポジトリに含めるが、更新内容を変えたあとに必ず作り直す。
- Release ノートには、何が変わったか、確認したコマンド、ユーザーへの影響を書く。
