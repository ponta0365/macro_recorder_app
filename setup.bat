@echo off
setlocal

cd /d "%~dp0"

python -m pip install --upgrade pip
if errorlevel 1 (
  echo pip の更新に失敗しました。
  pause
  exit /b 1
)

python -m pip install -r "%~dp0requirements.txt"
if errorlevel 1 (
  echo 依存関係のインストールに失敗しました。
  pause
  exit /b 1
)

echo.
echo セットアップが完了しました。
echo 起動するには start_macro_recorder.bat を実行してください。
pause

endlocal
