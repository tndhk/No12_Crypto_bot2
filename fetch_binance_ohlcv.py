
import os
import time
import pandas as pd
from datetime import datetime, timedelta
from binance.client import Client
from dotenv import load_dotenv

load_dotenv()

# APIキー
api_key = os.getenv("BINANCE_API_KEY")
api_secret = os.getenv("BINANCE_API_SECRET")

# パラメータ
symbol = os.getenv("SYMBOL", "BTCUSDT")
interval = os.getenv("INTERVAL", "1h")
months = 12
limit = 1000

client = Client(api_key, api_secret)

def fetch_historical_klines(symbol, interval, months=12):
    end_time = datetime.utcnow()
    start_time = end_time - timedelta(days=30 * months)
    all_data = []

    print(f"Fetching data for {symbol}, {interval}, from {start_time.date()} to {end_time.date()}")

    while start_time < end_time:
        start_ts = int(start_time.timestamp() * 1000)
        try:
            klines = client.get_klines(symbol=symbol, interval=interval, limit=limit, startTime=start_ts)
            if not klines:
                break

            df = pd.DataFrame(klines, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume',
                'close_time', 'quote_asset_volume', 'number_of_trades',
                'taker_buy_base_asset_volume', 'taker_buy_quote_asset_volume', 'ignore'
            ])
            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            df = df.astype({'open': float, 'high': float, 'low': float, 'close': float, 'volume': float})
            all_data.append(df)

            # 次の開始時間へ
            last_ts = klines[-1][0]
            start_time = datetime.utcfromtimestamp(last_ts / 1000) + timedelta(milliseconds=1)
            time.sleep(0.2)  # API制限対策
        except Exception as e:
            print(f"Error: {e}")
            break

    return pd.concat(all_data, ignore_index=True) if all_data else pd.DataFrame()

if __name__ == "__main__":
    df = fetch_historical_klines(symbol, interval, months)
    if not df.empty:
        filename = f"data/{symbol}_{interval}_{months}months.csv"
        os.makedirs("data", exist_ok=True)
        df.to_csv(filename, index=False)
        print(f"Saved to {filename}")
    else:
        print("No data fetched.")
