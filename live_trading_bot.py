
# -*- coding: utf-8 -*-
"""
Binance API対応・リアルトレード可能なトレーディングボット
"""

import os
from dotenv import load_dotenv
from binance.client import Client
from binance.exceptions import BinanceAPIException
import pandas as pd
import numpy as np
import talib as ta
from datetime import datetime
import logging

load_dotenv()
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

class LiveTradingBot:
    def __init__(self):
        # API接続
        self.api_key = os.getenv("BINANCE_API_KEY")
        self.api_secret = os.getenv("BINANCE_API_SECRET")
        self.client = Client(self.api_key, self.api_secret)

        # 設定読み込み
        self.symbol = os.getenv("SYMBOL", "BTCUSDT")
        self.interval = os.getenv("INTERVAL", "15m")
        self.stop_loss_percent = float(os.getenv("STOP_LOSS_PERCENT", 2.0))
        self.tp_multiplier = float(os.getenv("TAKE_PROFIT_MULTIPLIER", 3.0))
        self.trade_quantity = float(os.getenv("TRADE_QUANTITY", 0.01))
        self.buy_threshold = float(os.getenv("BUY_THRESHOLD", 0.6))
        self.sell_threshold = float(os.getenv("SELL_THRESHOLD", -0.6))

        self.weight_ma = 0.3
        self.weight_rsi = 0.2
        self.weight_macd = 0.2
        self.weight_bb = 0.2
        self.weight_breakout = 0.1

        self.in_position = False
        self.entry_price = 0.0
        self.stop_loss = 0.0
        self.take_profit = 0.0

    def fetch_ohlcv(self, limit=100):
        """BinanceからOHLCV取得"""
        try:
            klines = self.client.get_klines(symbol=self.symbol, interval=self.interval, limit=limit)
            df = pd.DataFrame(klines, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume',
                'close_time', 'quote_asset_volume', 'number_of_trades',
                'taker_buy_base_asset_volume', 'taker_buy_quote_asset_volume', 'ignore'
            ])
            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            for col in ['open', 'high', 'low', 'close', 'volume']:
                df[col] = df[col].astype(float)
            return df
        except BinanceAPIException as e:
            logger.error(f"Binance API エラー: {e}")
            return pd.DataFrame()

    def calculate_indicators(self, df):
        df['EMA_short'] = df['close'].ewm(span=10).mean()
        df['EMA_long'] = df['close'].ewm(span=25).mean()
        df['ma_signal'] = np.where(df['EMA_short'] > df['EMA_long'], 1, -1)
        df['RSI'] = ta.RSI(df['close'], timeperiod=14)
        df['rsi_signal'] = np.where(df['RSI'] < 30, 1, np.where(df['RSI'] > 70, -1, 0))
        df['BB_upper'], df['BB_middle'], df['BB_lower'] = ta.BBANDS(df['close'], timeperiod=20)
        df['bb_signal'] = np.where(df['close'] < df['BB_lower'], 1, np.where(df['close'] > df['BB_upper'], -1, 0))
        macd, macdsignal, _ = ta.MACD(df['close'], fastperiod=12, slowperiod=26, signalperiod=9)
        df['macd_signal'] = np.where(macd > macdsignal, 1, -1)
        df['breakout_signal'] = np.where(df['close'] > df['high'].rolling(14).max().shift(1), 1,
                                         np.where(df['close'] < df['low'].rolling(14).min().shift(1), -1, 0))
        df['ATR'] = ta.ATR(df['high'], df['low'], df['close'], timeperiod=14)
        return df

    def generate_signal(self, row):
        score = (
            self.weight_ma * row['ma_signal'] +
            self.weight_macd * row['macd_signal'] +
            self.weight_rsi * (1 if row['RSI'] > 50 else -1) +
            self.weight_breakout * row['breakout_signal']
        )
        if score >= self.buy_threshold:
            return 1
        elif score <= self.sell_threshold:
            return -1
        else:
            return 0

    def place_order(self, side):
        try:
            order = self.client.create_order(
                symbol=self.symbol,
                side=side,
                type=Client.ORDER_TYPE_MARKET,
                quantity=self.trade_quantity
            )
            logger.info(f"{side} 注文成功: {order}")
            return order
        except BinanceAPIException as e:
            logger.error(f"注文エラー: {e}")
            return None

    def run(self):
        df = self.fetch_ohlcv()
        if df.empty or len(df) < 30:
            logger.warning("十分なデータが取得できませんでした")
            return
        df = self.calculate_indicators(df)
        latest = df.iloc[-1]
        atr = latest['ATR']
        signal = self.generate_signal(latest)

        if not self.in_position and signal == 1:
            self.entry_price = latest['close']
            self.stop_loss = self.entry_price * (1 - self.stop_loss_percent / 100)
            self.take_profit = self.entry_price + atr * self.tp_multiplier
            order = self.place_order(Client.SIDE_BUY)
            if order:
                self.in_position = True
        elif self.in_position and (latest['close'] <= self.stop_loss or latest['close'] >= self.take_profit or signal == -1):
            order = self.place_order(Client.SIDE_SELL)
            if order:
                self.in_position = False

# 起動処理
if __name__ == "__main__":
    bot = LiveTradingBot()
    bot.run()
