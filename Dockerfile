# ベースイメージ
FROM python:3.10-slim

# 必要なパッケージをインストール
RUN apt-get update && \
    apt-get install -y build-essential libatlas-base-dev libffi-dev libssl-dev && \
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

# 作業ディレクトリを作成
WORKDIR /app

# 依存関係ファイルをコピー
COPY requirements.txt .

# Pythonパッケージをインストール
RUN pip install --upgrade pip && pip install --no-cache-dir -r requirements.txt

# アプリコードをコピー
COPY . .

# 起動コマンド（後から上書き可能）
CMD ["python", "trading_bot.py", "--mode", "backtest"]
