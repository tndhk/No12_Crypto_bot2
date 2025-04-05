# -*- coding: utf-8 -*-
"""
高度に改良されたトレーディングボット - Docker環境対応

改良機能:
- 複合シグナルロジック（複数指標の重み付け統合）
- バックテスト用データの最適化された取り扱い
- 高精度なインターバル内価格変動シミュレーション
- 実行価格とスリッページの現実的なモデル化
- 堅牢なエラーハンドリングとAPI制限管理

実行方法:
    バックテスト: python trading_bot.py --mode backtest
    ライブトレード: python trading_bot.py --mode live
    最適化: python trading_bot.py --mode optimize
"""

import os
import time
import argparse
import pandas as pd
import numpy as np
from binance.client import Client
from binance.exceptions import BinanceAPIException
import matplotlib.pyplot as plt
from datetime import datetime, timedelta
from dotenv import load_dotenv
from loguru import logger
import json
import sys
import schedule
import random
import traceback
from typing import Dict, List, Tuple, Optional, Union, Any
import warnings
import pickle
import glob
from concurrent.futures import ThreadPoolExecutor, ProcessPoolExecutor
from scipy import stats
from tqdm import tqdm
import matplotlib.dates as mdates
from matplotlib.ticker import PercentFormatter
import seaborn as sns
import re

from concurrent.futures import ProcessPoolExecutor, as_completed
import itertools
from datetime import datetime

# 環境変数の読み込み
load_dotenv()

# ロギング設定
logger.remove()
logger.add(sys.stderr, level=os.getenv("LOG_LEVEL", "INFO"))
logger.add("logs/trading_bot_{time}.log", rotation="1 day", retention="30 days")

# 警告を抑制
warnings.filterwarnings('ignore')

class EnhancedTradingBot:
    def __init__(self):
        """
        トレーディングボットの初期化
        環境変数から設定を読み込む
        """
        # API設定
        self.api_key = os.getenv("BINANCE_API_KEY")
        self.api_secret = os.getenv("BINANCE_API_SECRET")
        self.client = None  # バックテスト時は初期化せず、ライブトレード時のみ初期化
        
        # 取引設定
        self.symbol = os.getenv("SYMBOL", "BTCUSDT")
        self.interval = os.getenv("INTERVAL", "1h")
        self.trade_quantity = float(os.getenv("QUANTITY", "0.001"))
        
        # 基本的な戦略パラメータ
        self.short_window = int(os.getenv("SHORT_WINDOW", "9"))
        self.long_window = int(os.getenv("LONG_WINDOW", "21"))
        self.stop_loss_percent = float(os.getenv("STOP_LOSS_PERCENT", "2.0"))
        self.take_profit_percent = float(os.getenv("TAKE_PROFIT_PERCENT", "5.0"))
        
        # RSI設定
        self.rsi_period = int(os.getenv("RSI_PERIOD", "14"))
        self.rsi_oversold = float(os.getenv("RSI_OVERSOLD", "30"))
        self.rsi_overbought = float(os.getenv("RSI_OVERBOUGHT", "70"))
        
        # MACD設定
        self.macd_fast = int(os.getenv("MACD_FAST", "12"))
        self.macd_slow = int(os.getenv("MACD_SLOW", "26"))
        self.macd_signal = int(os.getenv("MACD_SIGNAL", "9"))
        
        # ボリンジャーバンド設定
        self.bb_period = int(os.getenv("BB_PERIOD", "20"))
        self.bb_std = float(os.getenv("BB_STD", "2.0"))
        
        # 複合シグナルの重み付け設定
        self.weight_ma = float(os.getenv("WEIGHT_MA", "0.3"))
        self.weight_rsi = float(os.getenv("WEIGHT_RSI", "0.2"))
        self.weight_macd = float(os.getenv("WEIGHT_MACD", "0.2"))
        self.weight_bb = float(os.getenv("WEIGHT_BB", "0.2"))
        self.weight_breakout = float(os.getenv("WEIGHT_BREAKOUT", "0.1"))
        
        # シグナル閾値
        self.buy_threshold = float(os.getenv("BUY_THRESHOLD", "0.5"))  # 買いシグナルの閾値
        self.sell_threshold = float(os.getenv("SELL_THRESHOLD", "-0.5"))  # 売りシグナルの閾値
        
        # フィルター設定
        self.use_complex_signal = os.getenv("USE_COMPLEX_SIGNAL", "true").lower() == "true"
        self.use_price_simulation = os.getenv("USE_PRICE_SIMULATION", "true").lower() == "true"
        
        # コストとスリッページ設定
        self.maker_fee = float(os.getenv("MAKER_FEE", "0.0010"))  # 0.1%
        self.taker_fee = float(os.getenv("TAKER_FEE", "0.0010"))  # 0.1%
        self.slippage_mean = float(os.getenv("SLIPPAGE_MEAN", "0.0005"))  # 0.05%
        self.slippage_std = float(os.getenv("SLIPPAGE_STD", "0.0003"))  # 標準偏差
        
        # バックテスト設定
        self.backtest_days = int(os.getenv("BACKTEST_DAYS", "90"))
        self.execution_delay = int(os.getenv("EXECUTION_DELAY", "1"))  # 次の足で約定
        self.price_simulation_steps = int(os.getenv("PRICE_SIMULATION_STEPS", "100"))  # 価格パスのステップ数
        self.use_cached_data = os.getenv("USE_CACHED_DATA", "true").lower() == "true"
        
        # 状態管理
        self.in_position = False
        self.entry_price = 0
        self.stop_loss = 0
        self.take_profit = 0
        self.current_trade = {}
        
        # パフォーマンス追跡
        self.trades = []
        self.balance_history = []
        
        # API制限処理
        self.api_request_count = 0
        self.last_api_reset = time.time()
        self.max_requests_per_minute = 1200  # Binanceの制限

        # リスク管理設定を追加
        self.MAX_CONSECUTIVE_LOSSES = 3
        self.max_drawdown_limit = 5.0  # パーセント
        self.risk_per_trade = 0.01  # 資本の1%
        self.consecutive_losses = 0
        self.initial_trade_quantity = float(os.getenv("QUANTITY", "0.001"))
        self.trade_quantity = self.initial_trade_quantity
        self.peak_balance = 10000  # バックテスト初期残高
        self.current_balance = 10000
        
        # データディレクトリの確認
        self._ensure_directories()
        
        # 設定のログ出力
        self._log_configuration()
    
    def _log_configuration(self):
        """現在の設定をログに出力"""
        # logger.info(f"=== ボット設定 ===")
        # logger.info(f"取引ペア: {self.symbol}, インターバル: {self.interval}")
        # logger.info(f"戦略: {'複合シグナル統合' if self.use_complex_signal else '移動平均クロスオーバー'}")
        # logger.info(f"移動平均: 短期={self.short_window}, 長期={self.long_window}")
        # logger.info(f"リスク設定: SL={self.stop_loss_percent}%, TP={self.take_profit_percent}%")
        
        # if self.use_complex_signal:
        #     logger.info(f"複合シグナル重み: MA={self.weight_ma}, RSI={self.weight_rsi}, "
        #                f"MACD={self.weight_macd}, BB={self.weight_bb}, ブレイクアウト={self.weight_breakout}")
        #     logger.info(f"シグナル閾値: 買い={self.buy_threshold}, 売り={self.sell_threshold}")
        
        # logger.info(f"価格シミュレーション: {'有効' if self.use_price_simulation else '無効'}")
        # logger.info(f"コスト設定: 手数料={self.taker_fee*100}%, "
        #            f"平均スリッページ={self.slippage_mean*100}%±{self.slippage_std*100}%")
        # logger.info(f"取引量: {self.trade_quantity} {self.symbol[:3]}")
        # logger.info("=" * 30)
    
    def _ensure_directories(self):
        """必要なディレクトリを作成"""
        for directory in ['data', 'logs', 'results', 'cache', 'models']:
            os.makedirs(directory, exist_ok=True)
    
    def _initialize_client(self):
        """APIクライアントを初期化（ライブモード用）"""
        if self.client is None:
            try:
                self.client = Client(self.api_key, self.api_secret)
                logger.info("Binance APIクライアント初期化成功")
            except Exception as e:
                logger.error(f"Binance APIクライアント初期化失敗: {e}")
                raise
    
    def _check_api_rate_limit(self):
        """API呼び出し制限をチェックし、必要に応じて待機"""
        current_time = time.time()
        # 1分経過していたらカウンターをリセット
        if current_time - self.last_api_reset > 60:
            self.api_request_count = 0
            self.last_api_reset = current_time
        
        # 制限に近づいたら待機
        if self.api_request_count > self.max_requests_per_minute * 0.9:
            wait_time = 60 - (current_time - self.last_api_reset)
            if wait_time > 0:
                logger.warning(f"API制限に近づいています。{wait_time:.2f}秒待機します")
                time.sleep(wait_time)
                self.api_request_count = 0
                self.last_api_reset = time.time()
        
        self.api_request_count += 1

    def get_historical_data(self, start_time=None, end_time=None, is_backtest=False):
        """
        start_time から end_time までのOHLCVデータをループで取得し、結合して返す
        """
        # キャッシュファイルパス
        cache_file = f"cache/{self.symbol}_{self.interval}_history.pkl"

        # start_time, end_time を datetime に変換
        start_dt = pd.to_datetime(start_time)
        end_dt = pd.to_datetime(end_time)
        
        logger.info(f"APIからデータをループで取得: {self.symbol}, {self.interval}")
        
        all_data = []
        current_time = start_dt
        self._initialize_client()


        while current_time < end_dt:
            # Binance API は最大1000本
            next_time = current_time + pd.Timedelta(minutes=60 * 1000 if self.interval.endswith('h') else 1)
            if next_time > end_dt:
                next_time = end_dt

            klines = self.client.get_historical_klines(
                symbol=self.symbol,
                interval=self.interval,
                start_str=current_time.strftime("%Y-%m-%d %H:%M:%S"),
                end_str=next_time.strftime("%Y-%m-%d %H:%M:%S"),
                limit=1000
            )

            if not klines:
                break

            df = pd.DataFrame(klines, columns=[
                'timestamp', 'open', 'high', 'low', 'close', 'volume',
                'close_time', 'quote_asset_volume', 'number_of_trades',
                'taker_buy_base_asset_volume', 'taker_buy_quote_asset_volume', 'ignore'
            ])

            df['timestamp'] = pd.to_datetime(df['timestamp'], unit='ms')
            for col in ['open', 'high', 'low', 'close', 'volume']:
                df[col] = df[col].astype(float)

            all_data.append(df)
            current_time = df['timestamp'].iloc[-1] + pd.Timedelta(hours=1)  # 次の開始時刻

            time.sleep(0.3)  # API制限対策

        if all_data:
            full_data = pd.concat(all_data).drop_duplicates('timestamp').sort_values('timestamp')
            
            # キャッシュ保存（オプション）
            if is_backtest:
                os.makedirs("cache", exist_ok=True)
                with open(cache_file, 'wb') as f:
                    pickle.dump(full_data, f)
                logger.info(f"キャッシュ保存完了: {len(full_data)} ロウソク足")

            return full_data

        return pd.DataFrame()

    
    def calculate_indicators(self, data):
        """
        テクニカル指標を計算
        
        Parameters:
        -----------
        data : pandas.DataFrame
            OHLCV データ
            
        Returns:
        --------
        pandas.DataFrame
            指標が追加されたデータフレーム
        """
        if data.empty:
            return data
            
        df = data.copy()
        
        # 移動平均の計算
        # 単純移動平均（SMA）
        df['SMA_short'] = df['close'].rolling(window=self.short_window).mean()
        df['SMA_long'] = df['close'].rolling(window=self.long_window).mean()
        
        # 指数移動平均（EMA）
        df['EMA_short'] = df['close'].ewm(span=self.short_window, adjust=False).mean()
        df['EMA_long'] = df['close'].ewm(span=self.long_window, adjust=False).mean()
        
        # 移動平均クロスオーバーシグナルの計算
        df['ma_signal'] = 0
        df.loc[df['EMA_short'] > df['EMA_long'], 'ma_signal'] = 1
        df.loc[df['EMA_short'] < df['EMA_long'], 'ma_signal'] = -1
        
        # RSIの計算
        delta = df['close'].diff()
        gain = delta.where(delta > 0, 0)
        loss = -delta.where(delta < 0, 0)
        
        avg_gain = gain.rolling(window=self.rsi_period).mean()
        avg_loss = loss.rolling(window=self.rsi_period).mean()
        
        rs = avg_gain / avg_loss
        df['RSI'] = 100 - (100 / (1 + rs))
        
        # RSIベースのシグナル
        df['rsi_signal'] = 0
        df.loc[df['RSI'] < self.rsi_oversold, 'rsi_signal'] = 1  # 買い
        df.loc[df['RSI'] > self.rsi_overbought, 'rsi_signal'] = -1  # 売り
        
        # ボリンジャーバンド
        df['BB_middle'] = df['close'].rolling(window=self.bb_period).mean()
        df['BB_std'] = df['close'].rolling(window=self.bb_period).std()
        df['BB_upper'] = df['BB_middle'] + self.bb_std * df['BB_std']
        df['BB_lower'] = df['BB_middle'] - self.bb_std * df['BB_std']
        
        # ボリンジャーバンドベースのシグナル
        df['bb_signal'] = 0
        df.loc[df['close'] < df['BB_lower'], 'bb_signal'] = 1  # 買い（下限突破）
        df.loc[df['close'] > df['BB_upper'], 'bb_signal'] = -1  # 売り（上限突破）
        
        # MACDの計算
        df['EMA_' + str(self.macd_fast)] = df['close'].ewm(span=self.macd_fast, adjust=False).mean()
        df['EMA_' + str(self.macd_slow)] = df['close'].ewm(span=self.macd_slow, adjust=False).mean()
        df['MACD'] = df['EMA_' + str(self.macd_fast)] - df['EMA_' + str(self.macd_slow)]
        df['MACD_signal'] = df['MACD'].ewm(span=self.macd_signal, adjust=False).mean()
        df['MACD_hist'] = df['MACD'] - df['MACD_signal']
        
        # MACDベースのシグナル
        df['macd_signal'] = 0
        df.loc[(df['MACD'] > df['MACD_signal']) & (df['MACD'].shift(1) <= df['MACD_signal'].shift(1)), 'macd_signal'] = 1  # 買い（MACD上抜け）
        df.loc[(df['MACD'] < df['MACD_signal']) & (df['MACD'].shift(1) >= df['MACD_signal'].shift(1)), 'macd_signal'] = -1  # 売り（MACD下抜け）
        
        # 高値安値ブレイクアウト
        n_periods = 14
        df['highest_high'] = df['high'].rolling(window=n_periods).max()
        df['lowest_low'] = df['low'].rolling(window=n_periods).min()
        
        # ブレイクアウトベースのシグナル
        df['breakout_signal'] = 0
        df.loc[df['close'] > df['highest_high'].shift(1), 'breakout_signal'] = 1  # 買い（高値ブレイク）
        df.loc[df['close'] < df['lowest_low'].shift(1), 'breakout_signal'] = -1  # 売り（安値ブレイク）
        
        # 出来高変化率
        df['volume_change'] = df['volume'].pct_change()
        df['volume_ma'] = df['volume'].rolling(window=20).mean()
        
        # 出来高ベースのシグナル
        df['volume_signal'] = 0
        df.loc[(df['volume'] > df['volume_ma'] * 1.5) & (df['close'] > df['open']), 'volume_signal'] = 1  # 大出来高の上昇
        df.loc[(df['volume'] > df['volume_ma'] * 1.5) & (df['close'] < df['open']), 'volume_signal'] = -1  # 大出来高の下落
        
        # ATR（Average True Range）- ボラティリティ指標
        high_low = df['high'] - df['low']
        high_close = abs(df['high'] - df['close'].shift())
        low_close = abs(df['low'] - df['close'].shift())
        
        tr = pd.concat([high_low, high_close, low_close], axis=1).max(axis=1)
        df['ATR'] = tr.rolling(14).mean()
        
        # 複合シグナルの計算
        if self.use_complex_signal:
            df['complex_signal'] = (
                self.weight_ma * df['ma_signal'] +
                self.weight_rsi * df['rsi_signal'] +
                self.weight_macd * df['macd_signal'] +
                self.weight_bb * df['bb_signal'] +
                self.weight_breakout * df['breakout_signal']
            )
            
            # シグナルのバイナリ化（閾値に基づく）
            df['signal'] = 0
            df.loc[df['complex_signal'] >= self.buy_threshold, 'signal'] = 1
            df.loc[df['complex_signal'] <= self.sell_threshold, 'signal'] = -1
        else:
            # 従来の移動平均ベースのシグナル
            df['signal'] = df['ma_signal']
        
        return df
        
    def generate_trading_signals(self, data):
        """
        トレーディングシグナルの生成
        """
        if data.empty or len(data) < 2:
            return {}
                
        # 最新のデータポイント
        current = data.iloc[-1]
        previous = data.iloc[-2]
        
        # 基本シグナル
        signal = 0
        
        # シグナル変化を検出
        if previous['signal'] == -1 and current['signal'] == 1:
            signal = 1  # 買いシグナル
        elif previous['signal'] == 1 and current['signal'] == -1:
            signal = -1  # 売りシグナル
        
        # シグナル情報をまとめる
        signal_info = {
            'timestamp': current['timestamp'],
            'open': current['open'],
            'high': current['high'],
            'low': current['low'],
            'close': current['close'],
            'signal': signal,
            'ma_signal': current['ma_signal'],
            'rsi_signal': current['rsi_signal'],
            'bb_signal': current.get('bb_signal', 0),
            'macd_signal': current.get('macd_signal', 0),
            'breakout_signal': current.get('breakout_signal', 0),
            'complex_signal': current.get('complex_signal', 0),
            'sma_short': current['SMA_short'],
            'sma_long': current['SMA_long'],
            'ema_short': current['EMA_short'],
            'ema_long': current['EMA_long'],
            'rsi': current['RSI'],
            'macd': current.get('MACD', 0),
            'macd_signal_line': current.get('MACD_signal', 0),
            'bb_upper': current.get('BB_upper', 0),
            'bb_lower': current.get('BB_lower', 0),
            'atr': current.get('ATR', 0)
        }
        
    # MACD履歴データの追加 (ヒストグラム傾きチェック用)
        if len(data) > 1:
            current = data.iloc[-1]
            previous = data.iloc[-2]
            signal_info['MACD_hist_prev'] = previous.get('MACD_hist', 0)
        
        # 最後に高度なフィルタリングを適用
        if signal != 0:
            filtered_signal = self.apply_advanced_filters(signal_info)
            signal_info['signal'] = filtered_signal
        
        return signal_info
            
    def calculate_slippage(self, is_buy: bool) -> float:
        """
        スリッページをシミュレート
        
        Parameters:
        -----------
        is_buy : bool
            買い注文かどうか
            
        Returns:
        --------
        float
            スリッページ率（正の値は価格上昇、負の値は価格下落）
        """
        # 正規分布に基づくランダムなスリッページ
        random_slippage = np.random.normal(self.slippage_mean, self.slippage_std)
        
        # 買い注文の場合は正のスリッページ（価格上昇）、売り注文の場合は負のスリッページ（価格下落）
        if is_buy:
            return abs(random_slippage)  # 買いは高くなる（不利）
        else:
            return -abs(random_slippage)  # 売りは安くなる（不利）
    
    def simulate_execution_price(self, signal_info: dict, is_buy: bool) -> float:
        """
        実行価格をシミュレート
        
        Parameters:
        -----------
        signal_info : dict
            シグナル情報
        is_buy : bool
            買い注文かどうか
            
        Returns:
        --------
        float
            実行価格
        """
        # シグナル発生時の終値
        close_price = signal_info['close']
        
        # 次の足の始値をシミュレート（現在の終値に±1%のランダム変動を加える）
        next_open_percent = np.random.normal(0, 0.01)  # 平均0、標準偏差1%
        next_open = close_price * (1 + next_open_percent)
        
        # スリッページを加算
        slippage_percent = self.calculate_slippage(is_buy)
        execution_price = next_open * (1 + slippage_percent)
        
        return execution_price
    
    def simulate_detailed_price_path(self, open_price, high_price, low_price, close_price, num_steps=None):
        """
        ローソク足内での詳細な価格パスをシミュレーション
        
        Parameters:
        -----------
        open_price, high_price, low_price, close_price : float
            ローソク足のOHLC値
        num_steps : int, optional
            シミュレーションするステップ数（精度）
            
        Returns:
        --------
        list
            時間的に整列された価格系列
        """
        if num_steps is None:
            num_steps = self.price_simulation_steps
            
        # ローソク足の方向性
        is_bullish = close_price > open_price
        
        # 価格変動の振れ幅
        price_range = high_price - low_price
        
        # ブラウン運動に基づく価格パスの生成
        price_path = []
        current_price = open_price
        
        # ランダムウォークに加えて、終値に向かうトレンド成分を追加
        trend_strength = 0.6  # 終値へ引き寄せる力の強さ (0-1)
        
        for i in range(num_steps):
            # 現在のステップの進捗率 (0-1)
            progress = i / (num_steps - 1)
            
            # ランダム成分（ボラティリティ）
            random_component = np.random.normal(0, price_range * 0.03)
            
            # トレンド成分（終値へ向かう力）
            trend_component = (close_price - current_price) * trend_strength * progress
            
            # 価格更新
            current_price += random_component + trend_component
            
            # 高値・安値の範囲内に制約
            current_price = max(min(current_price, high_price * 1.001), low_price * 0.999)
            
            price_path.append(current_price)
        
        # 最後の価格は必ず終値に一致させる
        price_path[-1] = close_price
        
        return price_path
    
    def check_sl_tp_on_price_path(self, price_path, stop_loss, take_profit):
        """
        価格パス上でのSL/TP発動を検出
        
        Parameters:
        -----------
        price_path : list
            時系列順の価格パス
        stop_loss : float
            ストップロス価格
        take_profit : float
            テイクプロフィット価格
            
        Returns:
        --------
        tuple
            (exit_type, exit_price, exit_index)
            exit_typeは 'Stop Loss', 'Take Profit', None のいずれか
        """
        for i, price in enumerate(price_path):
            if price <= stop_loss:
                return 'Stop Loss', price, i
            if price >= take_profit:
                return 'Take Profit', price, i
        
        return None, None, None
    
    def apply_trading_fees(self, amount: float, is_maker: bool = False) -> float:
        """
        取引手数料を適用
        
        Parameters:
        -----------
        amount : float
            取引金額
        is_maker : bool
            メーカー注文かどうか
            
        Returns:
        --------
        float
            手数料適用後の金額
        """
        fee_rate = self.maker_fee if is_maker else self.taker_fee
        return amount * (1 - fee_rate)
    
    def execute_trade(self, signal_info, is_backtest=False):
        """
        取引を実行
        
        Parameters:
        -----------
        signal_info : dict
            シグナル情報
        is_backtest : bool
            バックテストモードかどうか
        """
        
        """取引を実行"""
        signal = signal_info['signal']
        
        # リスク管理制限のチェック
        if self.consecutive_losses >= self.MAX_CONSECUTIVE_LOSSES:
            # 取引サイズを半分に減らす
            if self.trade_quantity > self.initial_trade_quantity / 4:  # 最小サイズまで
                self.trade_quantity = self.trade_quantity / 2
                logger.info(f"連続損失により取引サイズを削減: {self.trade_quantity}")
        
        # 最大ドローダウン制限
        current_drawdown = self.calculate_current_drawdown()
        if current_drawdown > self.max_drawdown_limit:
            # 取引を一時停止
            logger.warning(f"最大ドローダウン制限({self.max_drawdown_limit}%)に達したため取引を一時停止")
            return
        
        if signal == 1 and not self.in_position:
            # 買いシグナルかつポジションなし
            try:
                # 実行価格のシミュレーション
                execution_price = self.simulate_execution_price(signal_info, is_buy=True)

                # ここに動的ポジションサイジングを追加 ==================
                if hasattr(self, 'calculate_position_size'):
                    # 仮のストップロス計算（ポジションサイズの計算用）
                    temp_stop_loss = execution_price * (1 - self.stop_loss_percent/100)
                    # リスクベースのポジションサイズ計算
                    position_size = self.calculate_position_size(execution_price, temp_stop_loss)
                    # 取引サイズを更新
                    self.trade_quantity = position_size
                    logger.info(f"動的ポジションサイズ: {self.trade_quantity}")
                # ===============================================

                if not is_backtest:
                    self._initialize_client()
                    self._check_api_rate_limit()
                    # 実際の取引実行
                    order = self.client.create_order(
                        symbol=self.symbol,
                        side=Client.SIDE_BUY,
                        type=Client.ORDER_TYPE_MARKET,
                        quantity=self.trade_quantity
                    )
                    order_id = order['orderId']
                else:
                    # バックテスト用の仮想注文ID
                    order_id = f"backtest_buy_{datetime.now().timestamp()}"
                
                self.in_position = True
                self.entry_price = execution_price

                # 動的リスク/リワード比の適用（既存コードの代わりに）
                if hasattr(self, 'calculate_dynamic_risk_reward'):
                    # 市場状況に基づく動的な設定
                    sl_percent, tp_percent = self.calculate_dynamic_risk_reward(signal_info)
                    self.stop_loss = execution_price * (1 - sl_percent/100)
                    self.take_profit = execution_price * (1 + tp_percent/100)
                else:
                    # 従来の固定パーセンテージ
                    self.stop_loss = execution_price * (1 - self.stop_loss_percent/100)
                    self.take_profit = execution_price * (1 + self.take_profit_percent/100)
                
                # 取引情報
                trade_info = {
                    'type': 'BUY',
                    'timestamp': signal_info['timestamp'],
                    'signal_price': signal_info['close'],
                    'execution_price': execution_price,
                    'slippage_percent': (execution_price / signal_info['close'] - 1) * 100,
                    'quantity': self.trade_quantity,
                    'reason': self._get_signal_reason(signal_info),
                    'order_id': order_id,
                    'stop_loss': self.stop_loss,
                    'take_profit': self.take_profit,
                    'indicators': {
                        'rsi': signal_info['rsi'],
                        'macd': signal_info['macd'],
                        'sma_short': signal_info['sma_short'],
                        'sma_long': signal_info['sma_long'],
                        'complex_signal': signal_info.get('complex_signal', 0)
                    }
                }
                self.trades.append(trade_info)
                self.current_trade = trade_info
                
                # トレード情報の保存
                if not is_backtest:
                    self._save_trade_info(trade_info)
                
                logger.info(f"買い注文: {self.symbol} @ {execution_price:.2f} USDT (シグナル価格: {signal_info['close']:.2f})")
                logger.info(f"スリッページ: {trade_info['slippage_percent']:.2f}%")
                logger.info(f"ストップロス: {self.stop_loss:.2f} / テイクプロフィット: {self.take_profit:.2f}")
                
            except Exception as e:
                logger.error(f"買い注文エラー: {e}")
                logger.error(traceback.format_exc())
                
        elif signal == -1 and self.in_position:
            # 売りシグナルかつポジションあり
            try:
                # 実行価格のシミュレーション
                execution_price = self.simulate_execution_price(signal_info, is_buy=False)
                
                if not is_backtest:
                    self._initialize_client()
                    self._check_api_rate_limit()
                    # 実際の取引実行
                    order = self.client.create_order(
                        symbol=self.symbol,
                        side=Client.SIDE_SELL,
                        type=Client.ORDER_TYPE_MARKET,
                        quantity=self.trade_quantity
                    )
                    order_id = order['orderId']
                else:
                    # バックテスト用の仮想注文ID
                    order_id = f"backtest_sell_{datetime.now().timestamp()}"
                
                # 手数料を考慮した利益計算
                gross_profit = (execution_price - self.entry_price) * self.trade_quantity
                net_profit = gross_profit * (1 - self.taker_fee)  # 手数料を差し引く
                # 損益によって連続損失カウンターを更新
                if net_profit <= 0:
                    self.consecutive_losses += 1
                else:
                    self.consecutive_losses = 0  # 利益が出たらリセット
                # バランス更新
                self.current_balance += net_profit

                # 手数料を考慮
                profit_percent = (execution_price / self.entry_price - 1) * 100
                
                trade_info = {
                    'type': 'SELL',
                    'timestamp': signal_info['timestamp'],
                    'signal_price': signal_info['close'],
                    'execution_price': execution_price,
                    'slippage_percent': (execution_price / signal_info['close'] - 1) * 100,
                    'quantity': self.trade_quantity,
                    'gross_profit': gross_profit,
                    'net_profit': net_profit,  # 手数料を考慮した純利益
                    'profit_percent': profit_percent,
                    'fees': gross_profit * self.taker_fee,
                    'reason': self._get_signal_reason(signal_info),
                    'order_id': order_id,
                    'entry_price': self.entry_price,
                    'hold_duration': self._calculate_hold_duration(self.current_trade['timestamp'], signal_info['timestamp']),
                    'indicators': {
                        'rsi': signal_info['rsi'],
                        'macd': signal_info['macd'],
                        'sma_short': signal_info['sma_short'],
                        'sma_long': signal_info['sma_long'],
                        'complex_signal': signal_info.get('complex_signal', 0)
                    }
                }
                self.trades.append(trade_info)
                
                # トレード情報の保存
                if not is_backtest:
                    self._save_trade_info(trade_info)
                
                logger.info(f"売り注文: {self.symbol} @ {execution_price:.2f} USDT (シグナル価格: {signal_info['close']:.2f})")
                logger.info(f"スリッページ: {trade_info['slippage_percent']:.2f}%")
                logger.info(f"純利益: {net_profit:.4f} USDT ({profit_percent:.2f}%)")
                
                self.in_position = False
                self.current_trade = {}
                
            except Exception as e:
                logger.error(f"売り注文エラー: {e}")
                logger.error(traceback.format_exc())
        
    def optimize_parameters(self, param_grid=None):
        """
        パラメータ最適化を実行
        
        Parameters:
        -----------
        param_grid : dict, optional
            最適化するパラメータのグリッド
        """
        if param_grid is None:
            # デフォルトのパラメータグリッド - 探索範囲を拡大
            param_grid = {
                'short_window': [2, 3, 4, 5],
                'long_window': [8, 10, 12],
                'stop_loss_percent': [2.0, 3.0],
                'take_profit_percent': [3.0, 5.0, 8.0],
                'weight_ma': [0.2],
                'weight_rsi': [0.3],
                'weight_macd': [0.2],
                'weight_bb': [0.2],
                'weight_breakout': [0.0],  # オフにしてもOK
                'buy_threshold': [-0.05, 0.0, 0.05],
                'sell_threshold': [-0.1, -0.2, -0.3]
            }

                
        logger.info("パラメータ最適化を開始...")
        logger.info(f"パラメータグリッド: {param_grid}")
        
        # 全組み合わせ数を計算
        total_combinations = 1
        for param_values in param_grid.values():
            total_combinations *= len(param_values)
        
        logger.info(f"最適化する組み合わせ数: {total_combinations}")
        
        # バックテスト用のデータを取得（一度だけ）
#        end_time = int(time.time() * 1000)
#        start_time = end_time - (self.backtest_days * 24 * 60 * 60 * 1000)

        start_time = os.getenv("START_TIME")
        end_time = os.getenv("END_TIME")

        if start_time:
            start_time = pd.to_datetime(start_time)
        if end_time:
            end_time = pd.to_datetime(end_time)
        
        data = self.get_historical_data(
            start_time=start_time, 
            end_time=end_time, 
            is_backtest=True
        )
        
        if data.empty:
            logger.error("最適化用データが取得できませんでした")
            return
        
        # 結果保存用
        results = []
        
        # 現在の設定をバックアップ
        original_params = {
            'short_window': self.short_window,
            'long_window': self.long_window,
            'stop_loss_percent': self.stop_loss_percent,
            'take_profit_percent': self.take_profit_percent,
            'weight_ma': self.weight_ma,
            'weight_rsi': self.weight_rsi,
            'weight_macd': self.weight_macd,
            'weight_bb': self.weight_bb,
            'weight_breakout': self.weight_breakout
        }
        
        # すべてのパラメータ組み合わせを生成
        param_names = list(param_grid.keys())
        param_values = list(param_grid.values())
        
        # 進捗表示用
        progress_counter = 0
        
        # グリッドサーチ
        def grid_search(params_dict, level=0, current_params={}):
            nonlocal progress_counter
            
            if level == len(param_names):
                # すべてのパラメータが設定された
                progress_counter += 1
                logger.info(f"組み合わせ {progress_counter}/{total_combinations} をテスト中: {current_params}")
                
                # パラメータを適用
                for param, value in current_params.items():
                    setattr(self, param, value)
                
                # このパラメータセットでバックテスト実行
                result = self._run_backtest_for_optimization(data.copy())
                
                # 結果を保存
                result_dict = {**current_params, **result}
                results.append(result_dict)
                
                return
            
            # 現在のレベルのパラメータに対してすべての値を試す
            param_name = param_names[level]
            for param_value in param_grid[param_name]:
                new_params = current_params.copy()
                new_params[param_name] = param_value
                grid_search(params_dict, level + 1, new_params)
        
        # グリッドサーチを実行
        grid_search(param_grid)
        
        # 結果をDataFrameに変換
        results_df = pd.DataFrame(results)
        
        # 最良の結果を見つける
        best_result = results_df.sort_values('net_profit', ascending=False).iloc[0]
        
        logger.info("=" * 80)
        logger.info("最適化結果")
        logger.info("=" * 80)
        logger.info(f"最適パラメータ: {best_result[param_names].to_dict()}")
        logger.info(f"純利益: {best_result['net_profit']:.2f} USDT ({best_result['profit_percent']:.2f}%)")
        logger.info(f"勝率: {best_result['win_rate']:.2f}%")
        logger.info(f"損益比率: {best_result['profit_factor']:.2f}")
        logger.info(f"最大ドローダウン: {best_result['max_drawdown']:.2f}%")
        
        # 結果をCSVとして保存
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        results_df.to_csv(f"results/optimization_{self.symbol}_{timestamp}.csv", index=False)
        
        # ベストな組み合わせをJSONとして保存
        with open(f"results/best_params_{self.symbol}_{timestamp}.json", 'w') as f:
            json.dump(best_result.to_dict(), f, default=str, indent=4)
        
        # 元のパラメータに戻す
        for param, value in original_params.items():
            setattr(self, param, value)
        
        # パラメータの重要度分析
        self._analyze_parameter_importance(results_df, param_names)
        
        return best_result
    
    def _run_backtest_for_optimization(self, data):
        """最適化用の簡易バックテスト実行"""
        # 指標計算
        df = self.calculate_indicators(data)
        
        # 初期資本
        initial_balance = 10000  # USDT
        balance = initial_balance
        self.in_position = False
        self.trades = []
        balance_history = [(df.iloc[0]['timestamp'], balance)]
        
        # データポイントが十分かチェック
        min_required_points = max(self.long_window, self.macd_slow) + 5
        if len(df) <= min_required_points:
            return {'net_profit': 0, 'profit_percent': 0, 'total_trades': 0, 'win_rate': 0, 
                    'profit_factor': 0, 'max_drawdown': 0}
        
        # バックテスト実行
        for i in range(min_required_points, len(df) - 1):
            prev_data = df.iloc[:i+1]
            current_data = df.iloc[i]
            signal_info = self.generate_trading_signals(prev_data)
            
            # ポジションがある場合、SL/TPチェック
            if self.in_position:
                exit_reason, exit_price = self.simulate_intracandle_execution(
                    current_data, self.stop_loss, self.take_profit
                )
                
                if exit_reason:
                    # スリッページを適用
                    slippage = self.calculate_slippage(is_buy=False)
                    execution_price = exit_price * (1 + slippage)
                    
                    # 手数料を考慮した利益計算
                    gross_profit = (execution_price - self.entry_price) * self.trade_quantity
                    fees = gross_profit * self.taker_fee
                    net_profit = gross_profit - fees
                    
                    # 残高に純利益を加算
                    balance += net_profit
                    
                    # 取引情報
                    self.trades.append({
                        'type': 'SELL',
                        'timestamp': current_data['timestamp'],
                        'execution_price': execution_price,
                        'quantity': self.trade_quantity,
                        'gross_profit': gross_profit,
                        'net_profit': net_profit,
                        'fees': fees,
                        'profit_percent': (execution_price / self.entry_price - 1) * 100,
                        'reason': exit_reason
                    })
                    
                    self.in_position = False
            
            # 次の足でのエントリー
            next_candle_idx = i + self.execution_delay
            if next_candle_idx < len(df):
                next_candle = df.iloc[next_candle_idx]
                
                # シグナルに基づく取引
                if signal_info['signal'] == 1 and not self.in_position:
                    # 買い注文
                    execution_price = float(next_candle['open'])
                    slippage = self.calculate_slippage(is_buy=True)
                    execution_price *= (1 + slippage)
                    
                    self.entry_price = execution_price
                    self.stop_loss = execution_price * (1 - self.stop_loss_percent/100)
                    self.take_profit = execution_price * (1 + self.take_profit_percent/100)
                    self.in_position = True
                    
                    self.trades.append({
                        'type': 'BUY',
                        'timestamp': next_candle['timestamp'],
                        'execution_price': execution_price,
                        'quantity': self.trade_quantity
                    })
                    
                elif signal_info['signal'] == -1 and self.in_position:
                    # 売り注文
                    execution_price = float(next_candle['open'])
                    slippage = self.calculate_slippage(is_buy=False)
                    execution_price *= (1 + slippage)
                    
                    # 手数料を考慮した利益計算
                    gross_profit = (execution_price - self.entry_price) * self.trade_quantity
                    fees = gross_profit * self.taker_fee
                    net_profit = gross_profit - fees
                    
                    # 残高に純利益を加算
                    balance += net_profit
                    
                    self.trades.append({
                        'type': 'SELL',
                        'timestamp': next_candle['timestamp'],
                        'execution_price': execution_price,
                        'quantity': self.trade_quantity,
                        'gross_profit': gross_profit,
                        'net_profit': net_profit,
                        'fees': fees,
                        'profit_percent': (execution_price / self.entry_price - 1) * 100,
                        'reason': 'Signal'
                    })
                    
                    self.in_position = False
            
            # 残高履歴を更新
            balance_history.append((current_data['timestamp'], balance))
        
        # 最後のポジションがまだ残っている場合、クローズ
        if self.in_position:
            last_price = df.iloc[-1]['close']
            gross_profit = (last_price - self.entry_price) * self.trade_quantity
            fees = gross_profit * self.taker_fee
            net_profit = gross_profit - fees
            
            balance += net_profit
            
            self.trades.append({
                'type': 'SELL',
                'timestamp': df.iloc[-1]['timestamp'],
                'execution_price': last_price,
                'quantity': self.trade_quantity,
                'gross_profit': gross_profit,
                'net_profit': net_profit,
                'fees': fees,
                'profit_percent': (last_price / self.entry_price - 1) * 100,
                'reason': 'End of Backtest'
            })
            
            self.in_position = False
        
        # 結果分析
        profit = balance - initial_balance
        profit_percent = (balance / initial_balance - 1) * 100
        
        # 取引統計
        total_trades = len([t for t in self.trades if t['type'] == 'BUY'])
        closed_trades = len([t for t in self.trades if t['type'] == 'SELL'])
        winning_trades = len([t for t in self.trades if t['type'] == 'SELL' and t.get('net_profit', 0) > 0])
        
        # 勝率
        win_rate = (winning_trades / closed_trades * 100) if closed_trades > 0 else 0
        
        # 損益比率
        total_profit = sum([t.get('net_profit', 0) for t in self.trades if t['type'] == 'SELL' and t.get('net_profit', 0) > 0])
        total_loss = sum([t.get('net_profit', 0) for t in self.trades if t['type'] == 'SELL' and t.get('net_profit', 0) <= 0])
        profit_factor = abs(total_profit / total_loss) if total_loss != 0 else float('inf')
        
        # 最大ドローダウン
        balance_series = pd.DataFrame(balance_history, columns=['timestamp', 'balance'])['balance']
        rolling_max = balance_series.cummax()
        drawdown = (rolling_max - balance_series) / rolling_max * 100
        max_drawdown = drawdown.max()
        
        return {
            'net_profit': profit,
            'profit_percent': profit_percent,
            'total_trades': total_trades,
            'closed_trades': closed_trades,
            'winning_trades': winning_trades,
            'win_rate': win_rate,
            'profit_factor': profit_factor,
            'max_drawdown': max_drawdown
        }
    
    def _analyze_parameter_importance(self, results_df, param_names):
            """パラメータの重要度を分析"""
            try:
                # 重要度分析のグラフを生成
                plt.figure(figsize=(12, 8))
                
                # 各パラメータと利益の相関を可視化
                for i, param in enumerate(param_names):
                    plt.subplot(3, 3, i+1)
                    sns.boxplot(x=param, y='profit_percent', data=results_df)
                    plt.title(f'{param} vs Profit')
                    plt.xticks(rotation=45)
                    
                plt.tight_layout()
                
                # 保存
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                plt.savefig(f'results/param_importance_{self.symbol}_{timestamp}.png')
                plt.close()
                
                # 相関分析
                correlation = results_df[param_names + ['profit_percent']].corr()['profit_percent'].sort_values(ascending=False)
                
                logger.info("パラメータ重要度分析 (利益との相関):")
                for param, corr in correlation.items():
                    if param != 'profit_percent':
                        logger.info(f"  {param}: {corr:.4f}")
                        
            except Exception as e:
                logger.error(f"パラメータ重要度分析エラー: {e}")


    def run_backtest(self):
        """バックテストを実行する（マルチ戦略バージョン）"""
        logger.info("マルチ戦略バックテストモードを開始")
        
        # 環境変数から読み込み
        start_time_str = os.getenv("START_TIME")
        end_time_str = os.getenv("END_TIME")
        
        # 時間変換
        start_time = pd.to_datetime(start_time_str) if start_time_str else None
        end_time = pd.to_datetime(end_time_str) if end_time_str else None
        
        try:
            # データ取得
            data = self.get_historical_data(
                start_time=start_time, 
                end_time=end_time, 
                is_backtest=True
            )
            
            if data.empty:
                logger.error("バックテスト用データが取得できませんでした")
                return
            
            logger.info(f"取得データ: {len(data)} ロウソク足 ({data['timestamp'].min()} - {data['timestamp'].max()})")
            
            # 指標計算
            df = self.calculate_indicators(data)
            
            # 初期資本
            initial_balance = 10000  # USDT
            balance = initial_balance
            self.in_position = False
            self.trades = []
            self.balance_history = [(df.iloc[0]['timestamp'], balance)]
            
            # データポイントが十分かチェック
            min_required_points = max(self.long_window, self.macd_slow) + 5
            if len(df) <= min_required_points:
                logger.error(f"バックテスト用データが不足しています（必要: {min_required_points}, 取得: {len(df)}）")
                return
                
            # シグナルログ（デバッグ用）
            strategy_signals_log = []
            
            # バックテスト実行
            for i in range(min_required_points, len(df) - 1):
                prev_data = df.iloc[:i+1]
                current_data = df.iloc[i]
                
                # マルチ戦略統合シグナルの生成
                signal_info = self.integrate_multiple_strategies(prev_data)
                current_price = current_data['close']
                
                # シグナルログ記録
                if signal_info.get('signal', 0) != 0:
                    strategy_signals_log.append({
                        'timestamp': signal_info['timestamp'],
                        'price': current_price,
                        'signal': signal_info.get('signal', 0),
                        'weighted_signal': signal_info.get('weighted_signal', 0),
                        'adx': signal_info.get('adx', 0),
                        'is_trending': signal_info.get('is_trending', False),
                        'strategy_signals': signal_info.get('strategy_signals', {}),
                        'strategy_weights': signal_info.get('strategy_weights', {})
                    })
                
                # ポジションがある場合のSL/TPチェック処理 (既存コード)
                if self.in_position:
                    # 既存のSL/TPチェックロジック
                    exit_reason, exit_price = self.simulate_intracandle_execution(
                        current_data, self.stop_loss, self.take_profit
                    )
                    
                    if exit_reason:
                        # 既存の決済処理
                        # ...
                        pass
                
                # デイトレードでは通常、次のローソク足の始値でエントリー
                next_candle_idx = i + self.execution_delay
                if next_candle_idx < len(df):
                    next_candle = df.iloc[next_candle_idx]
                    
                    # シグナルに基づく取引
                    if signal_info.get('signal', 0) == 1 and not self.in_position:
                        # 実行価格をシミュレート
                        execution_price = float(next_candle['open'])
                        slippage = self.calculate_slippage(is_buy=True)
                        execution_price *= (1 + slippage)
                        
                        # 動的リスク/リワード比の計算
                        sl_percent, tp_percent = self.adaptive_risk_reward(signal_info)
                        
                        # 買い注文を実行
                        self.entry_price = execution_price
                        self.stop_loss = execution_price * (1 - sl_percent/100)
                        self.take_profit = execution_price * (1 + tp_percent/100)
                        self.in_position = True
                        
                        # 取引手数料を適用
                        execution_cost = execution_price * self.trade_quantity
                        fees = execution_cost * self.taker_fee
                        
                        # 主要戦略の特定（トレードの理由として記録）
                        dominant_strategy = max(signal_info.get('strategy_signals', {}), 
                                            key=lambda k: abs(signal_info['strategy_signals'][k]) * signal_info['strategy_weights'][k])
                        
                        # トレード情報
                        trade_info = {
                            'type': 'BUY',
                            'timestamp': next_candle['timestamp'],
                            'signal_timestamp': df.iloc[i]['timestamp'],
                            'signal_price': current_price,
                            'execution_price': execution_price,
                            'quantity': self.trade_quantity,
                            'slippage_percent': (execution_price / float(next_candle['open']) - 1) * 100,
                            'fees': fees,
                            'reason': f'戦略: {dominant_strategy} (加重シグナル: {signal_info["weighted_signal"]:.2f})',
                            'stop_loss': self.stop_loss,
                            'take_profit': self.take_profit,
                            'sl_percent': sl_percent,
                            'tp_percent': tp_percent,
                            'is_trending': signal_info.get('is_trending', False),
                            'adx': signal_info.get('adx', 0),
                            'strategy_signals': signal_info.get('strategy_signals', {})
                        }
                        
                        self.trades.append(trade_info)
                        
                        # 現在の取引情報を更新
                        self.current_trade = trade_info
                        
                    elif signal_info.get('signal', 0) == -1 and self.in_position:
                        # 実行価格をシミュレート
                        execution_price = float(next_candle['open'])
                        slippage = self.calculate_slippage(is_buy=False)
                        execution_price *= (1 + slippage)
                        
                        # 手数料を考慮した利益計算
                        gross_profit = (execution_price - self.entry_price) * self.trade_quantity
                        fees = gross_profit * self.taker_fee
                        net_profit = gross_profit - fees
                        
                        # 残高に純利益を加算
                        balance += net_profit
                        
                        # 主要戦略の特定
                        dominant_strategy = max(signal_info.get('strategy_signals', {}), 
                                            key=lambda k: abs(signal_info['strategy_signals'][k]) * signal_info['strategy_weights'][k])
                        
                        self.trades.append({
                            'type': 'SELL',
                            'timestamp': next_candle['timestamp'],
                            'signal_timestamp': df.iloc[i]['timestamp'],
                            'signal_price': current_price,
                            'execution_price': execution_price,
                            'quantity': self.trade_quantity,
                            'gross_profit': gross_profit,
                            'net_profit': net_profit,
                            'fees': fees,
                            'profit_percent': (execution_price / self.entry_price - 1) * 100,
                            'reason': f'戦略: {dominant_strategy} (加重シグナル: {signal_info["weighted_signal"]:.2f})',
                            'slippage_percent': (execution_price / float(next_candle['open']) - 1) * 100,
                            'entry_price': self.entry_price,
                            'hold_duration': self._calculate_hold_duration(
                                self.current_trade.get('timestamp', df.iloc[i]['timestamp']), 
                                next_candle['timestamp']
                            ) if hasattr(self, '_calculate_hold_duration') else 0,
                            'adx': signal_info.get('adx', 0),
                            'is_trending': signal_info.get('is_trending', False),
                            'strategy_signals': signal_info.get('strategy_signals', {})
                        })
                        
                        self.in_position = False
                        self.current_trade = {}
                
                # 残高履歴を更新
                self.balance_history.append((current_data['timestamp'], balance))
                self.current_balance = balance
                self.peak_balance = max(self.peak_balance, balance)
            
            # 最後のポジションがまだ残っている場合、クローズ
            if self.in_position:
                last_price = df.iloc[-1]['close']
                gross_profit = (last_price - self.entry_price) * self.trade_quantity
                fees = gross_profit * self.taker_fee
                net_profit = gross_profit - fees
                
                balance += net_profit
                
                self.trades.append({
                    'type': 'SELL',
                    'timestamp': df.iloc[-1]['timestamp'],
                    'execution_price': last_price,
                    'quantity': self.trade_quantity,
                    'gross_profit': gross_profit,
                    'net_profit': net_profit,
                    'fees': fees,
                    'profit_percent': (last_price / self.entry_price - 1) * 100,
                    'reason': 'バックテスト終了',
                    'entry_price': self.entry_price,
                    'hold_duration': self._calculate_hold_duration(
                        self.current_trade.get('timestamp', df.iloc[-1]['timestamp']), 
                        df.iloc[-1]['timestamp']
                    ) if hasattr(self, '_calculate_hold_duration') else 0
                })
                
                self.in_position = False
                self.current_trade = {}
                
                # 最終残高を更新
                self.balance_history.append((df.iloc[-1]['timestamp'], balance))
            
            # 戦略シグナルの分析
            if strategy_signals_log:
                logger.info(f"マルチ戦略シグナル数: {len(strategy_signals_log)}")
                
                strategy_stats = {strategy: {'count': 0, 'avg_weight': 0} 
                                for strategy in ['trend', 'breakout', 'mean_reversion']}
                
                for log in strategy_signals_log:
                    for strategy, signal in log.get('strategy_signals', {}).items():
                        if signal != 0:
                            strategy_stats[strategy]['count'] += 1
                            strategy_stats[strategy]['avg_weight'] += log.get('strategy_weights', {}).get(strategy, 0)
                
                for strategy, stats in strategy_stats.items():
                    if stats['count'] > 0:
                        stats['avg_weight'] /= stats['count']
                        logger.info(f"戦略 '{strategy}': {stats['count']}回シグナル発生, 平均重み: {stats['avg_weight']:.3f}")
            
            # バックテスト結果の出力
            self._print_enhanced_results(initial_balance, balance)
            
            # 戦略別のパフォーマンス分析
            self._analyze_strategy_performance()
            
        except Exception as e:
            logger.error(f"バックテストエラー: {e}")
            logger.error(traceback.format_exc())

    def _print_enhanced_results(self, initial_balance, final_balance):
        """拡張されたバックテスト結果の出力"""
        profit = final_balance - initial_balance
        profit_percent = (final_balance / initial_balance - 1) * 100
        annual_return = profit_percent  # バックテスト期間が1年の場合
        
        # 取引統計
        buy_trades = [t for t in self.trades if t['type'] == 'BUY']
        sell_trades = [t for t in self.trades if t['type'] == 'SELL']
        
        winning_trades = [t for t in sell_trades if t.get('net_profit', 0) > 0]
        losing_trades = [t for t in sell_trades if t.get('net_profit', 0) <= 0]
        
        win_rate = (len(winning_trades) / len(sell_trades) * 100) if sell_trades else 0
        
        # 保有期間の統計
        hold_durations = [t.get('hold_duration', 0) for t in sell_trades if 'hold_duration' in t]
        avg_hold_duration = sum(hold_durations) / len(hold_durations) if hold_durations else 0
        
        # 最大ドローダウンの計算
        balance_df = pd.DataFrame(self.balance_history, columns=['timestamp', 'balance'])
        balance_df['peak'] = balance_df['balance'].cummax()
        balance_df['drawdown'] = (balance_df['peak'] - balance_df['balance']) / balance_df['peak'] * 100
        max_drawdown = balance_df['drawdown'].max()
        
        # リスク調整後リターン指標（シャープレシオ）
        returns = balance_df['balance'].pct_change().dropna()
        sharpe_ratio = (returns.mean() / returns.std()) * (252 ** 0.5) if len(returns) > 1 and returns.std() > 0 else 0
        
        # 結果表示
        logger.info("=" * 60)
        logger.info("マルチ戦略バックテスト結果")
        logger.info("=" * 60)
        logger.info(f"初期資本: {initial_balance:.2f} USDT")
        logger.info(f"最終資本: {final_balance:.2f} USDT")
        logger.info(f"純利益: {profit:.2f} USDT ({profit_percent:.2f}%)")
        logger.info(f"年間収益率: {annual_return:.2f}%")
        logger.info(f"取引数: {len(buy_trades)}")
        logger.info(f"勝率: {win_rate:.2f}%（{len(winning_trades)}勝 / {len(losing_trades)}敗）")
        logger.info(f"最大ドローダウン: {max_drawdown:.2f}%")
        logger.info(f"シャープレシオ: {sharpe_ratio:.3f}")
        logger.info(f"平均保有期間: {avg_hold_duration:.1f}時間")
        
        if winning_trades:
            avg_win = sum(t.get('net_profit', 0) for t in winning_trades) / len(winning_trades)
            max_win = max(t.get('profit_percent', 0) for t in winning_trades)
            logger.info(f"平均利益: {avg_win:.4f} USDT")
            logger.info(f"最大の勝ち: {max_win:.2f}%")
        
        if losing_trades:
            avg_loss = sum(t.get('net_profit', 0) for t in losing_trades) / len(losing_trades)
            max_loss = min(t.get('profit_percent', 0) for t in losing_trades)
            logger.info(f"平均損失: {avg_loss:.4f} USDT")
            logger.info(f"最大の負け: {max_loss:.2f}%")
        
        # プロフィットファクター（総利益 / 総損失）
        total_profit = sum(t.get('net_profit', 0) for t in winning_trades)
        total_loss = abs(sum(t.get('net_profit', 0) for t in losing_trades))
        profit_factor = total_profit / total_loss if total_loss > 0 else float('inf')
        logger.info(f"プロフィットファクター: {profit_factor:.2f}")
        
        logger.info("=" * 60)

    def _analyze_strategy_performance(self):
        """戦略別のパフォーマンス分析"""
        strategy_performance = {}
        
        # 取引ごとに戦略を特定し、パフォーマンスを集計
        for trade in self.trades:
            if trade['type'] != 'SELL' or 'reason' not in trade:
                continue
            
            # 戦略名の抽出（例: '戦略: trend' から 'trend' を抽出）
            strategy_match = re.search(r'戦略: (\w+)', trade.get('reason', ''))
            if not strategy_match:
                continue
                
            strategy = strategy_match.group(1)
            
            if strategy not in strategy_performance:
                strategy_performance[strategy] = {
                    'count': 0,
                    'wins': 0,
                    'losses': 0,
                    'profit': 0,
                    'profit_percent': 0
                }
            
            performance = strategy_performance[strategy]
            performance['count'] += 1
            
            if trade.get('net_profit', 0) > 0:
                performance['wins'] += 1
            else:
                performance['losses'] += 1
                
            performance['profit'] += trade.get('net_profit', 0)
            performance['profit_percent'] += trade.get('profit_percent', 0)
        
        # 各戦略のパフォーマンス結果を表示
        if strategy_performance:
            logger.info("戦略別パフォーマンス")
            logger.info("-" * 40)
            
            for strategy, performance in strategy_performance.items():
                total_trades = performance['count']
                if total_trades == 0:
                    continue
                    
                win_rate = performance['wins'] / total_trades * 100 if total_trades > 0 else 0
                avg_profit_percent = performance['profit_percent'] / total_trades if total_trades > 0 else 0
                
                logger.info(f"戦略: {strategy}")
                logger.info(f"  取引数: {total_trades}")
                logger.info(f"  勝率: {win_rate:.2f}%")
                logger.info(f"  総利益: {performance['profit']:.4f} USDT")
                logger.info(f"  平均リターン: {avg_profit_percent:.2f}%")
                logger.info("-" * 40)


    def _print_basic_results(self, initial_balance, final_balance):
        """基本的なバックテスト結果を出力"""
        profit = final_balance - initial_balance
        profit_percent = (final_balance / initial_balance - 1) * 100
        
        buy_trades = [t for t in self.trades if t['type'] == 'BUY']
        sell_trades = [t for t in self.trades if t['type'] == 'SELL']
        
        winning_trades = [t for t in sell_trades if t.get('net_profit', 0) > 0]
        losing_trades = [t for t in sell_trades if t.get('net_profit', 0) <= 0]
        
        win_rate = (len(winning_trades) / len(sell_trades) * 100) if sell_trades else 0
        
        logger.info("=" * 50)
        logger.info("バックテスト結果")
        logger.info("=" * 50)
        logger.info(f"初期資本: {initial_balance:.2f} USDT")
        logger.info(f"最終資本: {final_balance:.2f} USDT")
        logger.info(f"純利益: {profit:.2f} USDT ({profit_percent:.2f}%)")
        logger.info(f"取引数: {len(buy_trades)}")
        logger.info(f"勝率: {win_rate:.2f}%（{len(winning_trades)}勝 / {len(losing_trades)}敗）")
        
        if winning_trades:
            avg_win = sum(t.get('net_profit', 0) for t in winning_trades) / len(winning_trades)
            logger.info(f"平均利益: {avg_win:.4f} USDT")
        
        if losing_trades:
            avg_loss = sum(t.get('net_profit', 0) for t in losing_trades) / len(losing_trades)
            logger.info(f"平均損失: {avg_loss:.4f} USDT")
        
        logger.info("=" * 50)

    def simulate_intracandle_execution(self, candle_data, stop_loss, take_profit):
        """ローソク足内での価格変動を使ってストップロスとテイクプロフィットをシミュレート"""
        # 価格パスが無効な場合はシミュレーションしない
        if not self.use_price_simulation:
            # 単純にローソク足の高値と安値を使って判定
            if candle_data['low'] <= stop_loss:
                return 'Stop Loss', stop_loss
            elif candle_data['high'] >= take_profit:
                return 'Take Profit', take_profit
            return None, None
            
        # ローソク足内での詳細な価格パスをシミュレート
        price_path = self.simulate_detailed_price_path(
            candle_data['open'], 
            candle_data['high'], 
            candle_data['low'], 
            candle_data['close'],
            self.price_simulation_steps
        )
        
        # 価格パス上でのSL/TP発動を検出
        exit_type, exit_price, _ = self.check_sl_tp_on_price_path(price_path, stop_loss, take_profit)
        
        return exit_type, exit_price

    def adapt_parameters_to_market(self, data):
        """市場ボラティリティに基づいてパラメータを調整"""
        # 最近のボラティリティを計算
        recent_data = data.tail(50)
        volatility = recent_data['close'].pct_change().std() * 100
        
        # ボラティリティに基づいて閾値を調整
        if volatility > 3.0:  # 高ボラティリティ
            self.buy_threshold = 0.4
            self.sell_threshold = -0.4
        elif volatility > 1.5:  # 中ボラティリティ
            self.buy_threshold = 0.3
            self.sell_threshold = -0.3
        else:  # 低ボラティリティ
            self.buy_threshold = 0.2
            self.sell_threshold = -0.2
            
        # トレンド強度に基づいた重み付け調整
        adx = self.calculate_adx(data)  # ADX実装が必要
        if adx > 25:  # 強いトレンド
            self.weight_ma = 0.45
            self.weight_macd = 0.35
            self.weight_rsi = 0.1
            self.weight_bb = 0.1
        else:  # 弱いトレンド/レンジ相場
            self.weight_ma = 0.3
            self.weight_macd = 0.2
            self.weight_rsi = 0.2
            self.weight_bb = 0.3

    def generate_multi_timeframe_signals(self):
        """複数の時間枠からのシグナルを統合"""
        # 4時間足データの取得
        h4_data = self.get_historical_data(interval="4h", is_backtest=True)
        h4_indicators = self.calculate_indicators(h4_data)
        h4_signal = self.generate_trading_signals(h4_indicators)
        
        # 1時間足データの取得
        h1_data = self.get_historical_data(interval="1h", is_backtest=True)
        h1_indicators = self.calculate_indicators(h1_data)
        h1_signal = self.generate_trading_signals(h1_indicators)
        
        # シグナルの統合（例：両方がポジティブなら強いシグナル）
        if h4_signal['signal'] == 1 and h1_signal['signal'] == 1:
            return 1  # 強い買いシグナル
        elif h4_signal['signal'] == -1 and h1_signal['signal'] == -1:
            return -1  # 強い売りシグナル
        
        return 0  # 中立シグナル

    def apply_advanced_filters(self, signal_info):
        """シグナル品質向上フィルター - バランス調整版"""
        signal = signal_info['signal']
        
        # シグナルがない場合はすぐに終了
        if signal == 0:
            return 0
        
        # トレンド一致度の確認
        trend_agreement = 0
        if signal > 0:  # 買いシグナル
            if signal_info['ma_signal'] > 0: trend_agreement += 1
            if signal_info['macd_signal'] > 0: trend_agreement += 1
            if signal_info['rsi_signal'] > 0: trend_agreement += 1
            if signal_info['bb_signal'] > 0: trend_agreement += 1
            
            # より現実的な条件: 最低2つの指標が一致が必要
            if trend_agreement < 2:
                return 0
                
            # RSIに基づく追加フィルター (オーバーソールドに近い状態)
            if signal_info['rsi'] > 65:  # 過度な買われすぎには買わない
                return 0
                
        elif signal < 0:  # 売りシグナル
            if signal_info['ma_signal'] < 0: trend_agreement += 1
            if signal_info['macd_signal'] < 0: trend_agreement += 1
            if signal_info['rsi_signal'] < 0: trend_agreement += 1
            if signal_info['bb_signal'] < 0: trend_agreement += 1
            
            # より現実的な条件: 最低2つの指標が一致が必要
            if trend_agreement < 2:
                return 0
                
            # RSIに基づく追加フィルター (オーバーボウトに近い状態)
            if signal_info['rsi'] < 35:  # 過度な売られすぎには売らない
                return 0
        
        # 過度なボラティリティの場合は取引を避ける (極端な場合のみ)
        if signal_info.get('atr', 0) / signal_info['close'] > 0.02:  # 2%以上の非常に高いボラティリティ
            return 0
        
        # 全フィルターを通過した場合のみシグナルを返す
        return signal

    def walk_forward_optimization(self):
        """ウォークフォワード最適化の実行"""
        # 例：データを3つの期間に分割
        total_days = 180
        in_sample_days = 30
        out_sample_days = 15
        
        end_time = int(time.time() * 1000)
        
        results = []
        
        # 3つの期間で最適化とテストを繰り返す
        for i in range(3):
            # インサンプル期間（最適化用）
            in_sample_end = end_time - (i * (in_sample_days + out_sample_days) * 24 * 60 * 60 * 1000)
            in_sample_start = in_sample_end - (in_sample_days * 24 * 60 * 60 * 1000)
            
            # 最適化実行
            best_params = self.optimize_for_period(in_sample_start, in_sample_end)
            
            # アウトオブサンプル期間（検証用）
            out_sample_end = in_sample_start
            out_sample_start = out_sample_end - (out_sample_days * 24 * 60 * 60 * 1000)
            
            # 最適化されたパラメータで検証
            performance = self.backtest_with_params(best_params, out_sample_start, out_sample_end)
            results.append(performance)
        
        # 結果の分析
        robustness_score = self.analyze_walk_forward_results(results)
        return robustness_score, results


    def calculate_current_drawdown(self):
        """現在のドローダウンをパーセンテージで計算"""
        if not self.balance_history:
            return 0.0
        
        # 履歴からの残高推移
        current_balance = self.balance_history[-1][1]
        # これまでの残高のピーク
        peak_balance = max([b[1] for b in self.balance_history])
        
        if peak_balance == 0:
            return 0.0
        
        drawdown_percent = (peak_balance - current_balance) / peak_balance * 100
        return drawdown_percent


    def _get_signal_reason(self, signal_info):
        """シグナルの理由を判断"""
        reasons = []
        
        if signal_info.get('ma_signal', 0) != 0:
            reasons.append('移動平均')
        
        if signal_info.get('rsi_signal', 0) != 0:
            reasons.append('RSI')
        
        if signal_info.get('macd_signal', 0) != 0:
            reasons.append('MACD')
        
        if signal_info.get('bb_signal', 0) != 0:
            reasons.append('ボリンジャーバンド')
        
        if signal_info.get('breakout_signal', 0) != 0:
            reasons.append('ブレイクアウト')
        
        if not reasons:
            return '複合シグナル'
        
        return '+'.join(reasons)

    def _calculate_hold_duration(self, start_time, end_time):
        """ポジションの保有期間を計算（時間単位）"""
        if isinstance(start_time, pd.Timestamp) and isinstance(end_time, pd.Timestamp):
            duration = (end_time - start_time).total_seconds() / 3600  # 時間に変換
            return round(duration, 1)
        return 0


    def calculate_adx(self, data, period=14):
        """ADX（平均方向性指数）の計算"""
        df = data.copy()
        
        # True Range
        df['tr0'] = abs(df['high'] - df['low'])
        df['tr1'] = abs(df['high'] - df['close'].shift())
        df['tr2'] = abs(df['low'] - df['close'].shift())
        df['tr'] = df[['tr0', 'tr1', 'tr2']].max(axis=1)
        
        # +DM, -DM
        df['up_move'] = df['high'] - df['high'].shift()
        df['down_move'] = df['low'].shift() - df['low']
        
        df['plus_dm'] = np.where((df['up_move'] > df['down_move']) & (df['up_move'] > 0), df['up_move'], 0)
        df['minus_dm'] = np.where((df['down_move'] > df['up_move']) & (df['down_move'] > 0), df['down_move'], 0)
        
        # 14期間の平均
        df['plus_di'] = 100 * (df['plus_dm'].rolling(window=period).mean() / df['tr'].rolling(window=period).mean())
        df['minus_di'] = 100 * (df['minus_dm'].rolling(window=period).mean() / df['tr'].rolling(window=period).mean())
        
        # DX
        df['dx'] = 100 * abs(df['plus_di'] - df['minus_di']) / (df['plus_di'] + df['minus_di'])
        
        # ADX
        df['adx'] = df['dx'].rolling(window=period).mean()
        
        return df['adx'].iloc[-1] if not df['adx'].empty else 0

    def calculate_dynamic_risk_reward(self, signal_info):
        """
        バランスの取れた動的リスク/リワード設定
        """
        # 基本設定
        sl_percent = self.stop_loss_percent
        tp_percent = self.take_profit_percent
        
        # トレンド状況に応じた調整
        if signal_info['ma_signal'] == signal_info['macd_signal']:
            # トレンド一致度が高い場合は利益目標を上げる
            tp_percent *= 1.1
        
        # ボラティリティに基づく調整
        atr_ratio = signal_info.get('atr', 0) / signal_info['close']
        if atr_ratio < 0.005:  # 低ボラティリティ
            # 低ボラティリティ時はより狭い範囲
            tp_percent *= 0.9
            sl_percent *= 0.9
        elif atr_ratio > 0.01:  # 高ボラティリティ
            # 高ボラティリティ時は広い範囲
            tp_percent *= 1.1
            sl_percent *= 1.1
        
        # RSIに基づく調整
        rsi = signal_info['rsi']
        if signal_info['signal'] > 0 and rsi < 30:  # 強いオーバーソールド
            tp_percent *= 1.2  # より大きな反発を期待
        elif signal_info['signal'] < 0 and rsi > 70:  # 強いオーバーボウト
            tp_percent *= 1.2  # より大きな調整を期待
        
        # 最終チェック - 値を合理的な範囲に収める
        sl_percent = max(1.0, min(sl_percent, 2.0))  # 1.0%〜2.0%
        tp_percent = max(3.0, min(tp_percent, 8.0))  # 3.0%〜8.0%
        
        return sl_percent, tp_percent

    def calculate_position_size(self, entry_price, stop_loss_price):
        """リスクに基づくポジションサイズの計算"""
        # リスク計算：資本の1%をリスクに
        risk_amount = self.current_balance * 0.01
        
        # 価格あたりのリスク（ストップロスまでの距離）
        price_risk = abs(entry_price - stop_loss_price)
        
        if price_risk == 0:
            return self.trade_quantity  # デフォルト値
        
        # 許容リスクに基づく数量計算
        quantity = risk_amount / price_risk
        
        # 最小・最大取引サイズの制限
        min_trade = 0.0005
        max_trade = 0.005
        
        return max(min(quantity, max_trade), min_trade)



    def optimize_parameters_parallel(self, param_grid=None):
        if param_grid is None:
            param_grid = {
                'short_window': [3],
                'long_window': [16],
                'stop_loss_percent': [1.5],
                'take_profit_percent': [8.0],
                'weight_ma': [0.2],
                'weight_rsi': [0.3],
                'weight_macd': [0.2],
                'weight_bb': [0.2],
                'weight_breakout': [0.1],
                'buy_threshold': [0.15],
                'sell_threshold': [0.05],
            }

        logger.info("パラメータ最適化（並列処理）を開始")

        param_keys = list(param_grid.keys())
        all_combinations = [dict(zip(param_keys, values)) for values in itertools.product(*param_grid.values())]
        logger.info(f"全組み合わせ数: {len(all_combinations)}")

        # データを1回だけ取得（使い回し）
        start_time = os.getenv("START_TIME")
        end_time = os.getenv("END_TIME")

        common_data = self.get_historical_data(start_time=start_time, end_time=end_time, is_backtest=True)

        logger.info(f"start_time: {start_time}")
        logger.info(f"end_time: {end_time}")



        if common_data.empty:
            logger.error("データ取得に失敗")
            return

        # .env の環境変数を取得して渡す
        env_dict = dict(os.environ)

        results = []
        with ProcessPoolExecutor(max_workers=7) as executor:
            futures = [executor.submit(evaluate_combination, combo, common_data, env_dict) for combo in all_combinations]
            for i, future in enumerate(as_completed(futures), 1):
                try:
                    res = future.result()
                    results.append(res)
                    if i % 100 == 0:
                        logger.info(f"進捗: {i}/{len(all_combinations)}")
                except Exception as e:
                    logger.error(f"評価エラー: {e}")

        results_df = pd.DataFrame(results)
        best_result = results_df.sort_values('net_profit', ascending=False).iloc[0]

        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        results_df.to_csv(f"results/optimization_parallel_{timestamp}.csv", index=False)
        with open(f"results/best_params_parallel_{timestamp}.json", 'w') as f:
            json.dump(best_result.to_dict(), f, indent=4)

        logger.info("\n" + "=" * 80)
        logger.info("最適化完了（並列版）")
        logger.info(f"最良結果: {best_result.to_dict()}")
        logger.info("=" * 80)

        return best_result

    # trading_bot.py に追加する新しいメソッド

    def is_favorable_market_context(self, data):
        """
        市場コンテキストが取引に適しているかを判断
        
        Parameters:
        -----------
        data : pandas.DataFrame
            過去のOHLCVデータと指標
            
        Returns:
        --------
        bool
            取引に適した市場環境ならTrue、そうでなければFalse
        """
        if data.empty or len(data) < 50:
            return False
        
        recent_data = data.tail(50)
        
        # 1. トレンド強度の確認
        adx = self.calculate_adx(recent_data)
        
        # 2. ボラティリティの確認
        atr_ratio = recent_data['ATR'].iloc[-1] / recent_data['close'].iloc[-1]
        
        # 3. 最近の価格変動方向
        price_direction = recent_data['close'].pct_change(10).iloc[-1]
        
        # 4. 市場の方向性（トレンドか、レンジか）
        high_low_range = (recent_data['high'].max() - recent_data['low'].min()) / recent_data['close'].mean()
        
        # 5. 最近の取引シグナル頻度
        recent_signals = abs(recent_data['complex_signal']).mean()
        
        # 6. 状況に基づく評価
        # トレンド状況での条件
        if adx > 25:  # 強いトレンドがある
            if atr_ratio > 0.015:  # ボラティリティが高い
                return False  # 不安定な強トレンド - 避ける
            else:
                return True  # 安定した強トレンド - 好ましい
        else:  # 弱いトレンドまたはレンジ相場
            if high_low_range < 0.05:  # 狭いレンジ
                return False  # 狭いレンジは避ける
            if atr_ratio < 0.003:  # 極端に低いボラティリティ
                return False  # 動きが少なすぎる
            if recent_signals > 0.2:  # シグナル過多
                return False  # ノイズが多い可能性
        
        # デフォルトでは取引を許可
        return True


    # trading_bot.py に追加する新しいメソッド

    def calculate_support_resistance(self, data, lookback=20):
        """
        過去の価格データからサポート・レジスタンスレベルを計算
        
        Parameters:
        -----------
        data : pandas.DataFrame
            OHLCV データ
        lookback : int
            検索する期間
            
        Returns:
        --------
        tuple
            (サポートレベル, レジスタンスレベル)
        """
        if len(data) < lookback:
            return None, None
        
        recent_data = data.tail(lookback)
        
        # 簡易サポート・レジスタンス計算
        resistance = recent_data['high'].max()
        support = recent_data['low'].min()
        
        # より洗練された方法：スイングハイ・ローの検出
        swing_highs = []
        swing_lows = []
        
        for i in range(2, len(recent_data) - 2):
            # ローカルトップ（スイングハイ）の検出
            if (recent_data['high'].iloc[i] > recent_data['high'].iloc[i-1] and 
                recent_data['high'].iloc[i] > recent_data['high'].iloc[i-2] and
                recent_data['high'].iloc[i] > recent_data['high'].iloc[i+1] and
                recent_data['high'].iloc[i] > recent_data['high'].iloc[i+2]):
                swing_highs.append(recent_data['high'].iloc[i])
            
            # ローカルボトム（スイングロー）の検出
            if (recent_data['low'].iloc[i] < recent_data['low'].iloc[i-1] and 
                recent_data['low'].iloc[i] < recent_data['low'].iloc[i-2] and
                recent_data['low'].iloc[i] < recent_data['low'].iloc[i+1] and
                recent_data['low'].iloc[i] < recent_data['low'].iloc[i+2]):
                swing_lows.append(recent_data['low'].iloc[i])
        
        # レベルのクラスタリング（近いレベルをグループ化）
        def cluster_levels(levels, threshold=0.01):
            if not levels:
                return []
            
            sorted_levels = sorted(levels)
            clusters = [[sorted_levels[0]]]
            
            for level in sorted_levels[1:]:
                latest_cluster = clusters[-1]
                latest_level = latest_cluster[-1]
                
                # 現在のレベルと最新のクラスタの最後のレベルとの差が閾値以内かチェック
                if abs(level - latest_level) / latest_level <= threshold:
                    latest_cluster.append(level)
                else:
                    clusters.append([level])
            
            # 各クラスタの平均値を計算
            return [sum(cluster) / len(cluster) for cluster in clusters]
        
        # クラスタリングされたレベル
        clustered_highs = cluster_levels(swing_highs)
        clustered_lows = cluster_levels(swing_lows)
        
        # 複数のレジスタンスレベルが見つかった場合は最も近いものを使用
        if clustered_highs:
            current_price = data['close'].iloc[-1]
            resistance_levels = [r for r in clustered_highs if r > current_price]
            if resistance_levels:
                resistance = min(resistance_levels)  # 現在価格より上で最も近いレベル
        
        # 複数のサポートレベルが見つかった場合は最も近いものを使用
        if clustered_lows:
            current_price = data['close'].iloc[-1]
            support_levels = [s for s in clustered_lows if s < current_price]
            if support_levels:
                support = max(support_levels)  # 現在価格より下で最も近いレベル
        
        return support, resistance

    def generate_breakout_signals(self, data):
        """
        ブレイクアウトに基づいたトレーディングシグナルを生成
        
        Parameters:
        -----------
        data : pandas.DataFrame
            OHLCV データと指標
            
        Returns:
        --------
        dict
            シグナル情報
        """
        if data.empty or len(data) < 30:  # 十分なデータが必要
            return {}
        
        # 最新のデータポイント
        current = data.iloc[-1]
        previous = data.iloc[-2]
        
        # ATRの計算（ボラティリティ測定用）
        atr = current.get('ATR', current['close'] * 0.01)  # ATRがない場合は推定
        
        # サポート・レジスタンスの計算
        lookback = 30  # 過去30本のローソク足を考慮
        support, resistance = self.calculate_support_resistance(data, lookback)
        
        # 基本シグナル
        signal = 0
        
        # レジスタンスブレイクアウト（買い）
        if resistance is not None:
            # 価格がレジスタンスを上回った場合（ブレイクアウト）
            if previous['close'] <= resistance and current['close'] > resistance:
                # 確認：十分な上昇勢い（より確実なブレイクアウト）
                if current['close'] > resistance * 1.002:  # 0.2%以上の突破
                    signal = 1
        
        # サポートブレイクダウン（売り）
        if support is not None:
            # 価格がサポートを下回った場合（ブレイクダウン）
            if previous['close'] >= support and current['close'] < support:
                # 確認：十分な下落勢い（より確実なブレイクダウン）
                if current['close'] < support * 0.998:  # 0.2%以上の下抜け
                    signal = -1
        
        # ボラティリティに基づいたフィルタリング
        vol_filter = True
        atr_ratio = atr / current['close']
        
        # 低ボラティリティ環境ではブレイクアウトが偽シグナルになりやすい
        if atr_ratio < 0.005:  # 極端に低いボラティリティ
            vol_filter = False
        
        # トレンド確認（移動平均の傾きでトレンドを確認）
        trend_filter = True
        if 'SMA_short' in current and 'SMA_long' in current:
            short_slope = (current['SMA_short'] - data['SMA_short'].iloc[-5]) / data['SMA_short'].iloc[-5]
            
            # 買いシグナルなのに短期MAが下降トレンドの場合、フィルタリング
            if signal > 0 and short_slope < -0.002:
                trend_filter = False
                
            # 売りシグナルなのに短期MAが上昇トレンドの場合、フィルタリング
            if signal < 0 and short_slope > 0.002:
                trend_filter = False
        
        # すべてのフィルターを適用
        if not (vol_filter and trend_filter):
            signal = 0
        
        # シグナル情報をまとめる
        signal_info = {
            'timestamp': current['timestamp'],
            'open': current['open'],
            'high': current['high'],
            'low': current['low'],
            'close': current['close'],
            'signal': signal,
            'support': support,
            'resistance': resistance,
            'atr': atr,
            'breakout_detected': True if signal != 0 else False
        }
        
        # 既存の指標情報も追加
        for key in ['SMA_short', 'SMA_long', 'RSI', 'MACD', 'BB_upper', 'BB_lower']:
            if key in current:
                signal_info[key] = current[key]
        
        return signal_info


# trading_bot.py に追加する新しいメソッド

    def generate_mean_reversion_signals(self, data):
        """
        平均回帰（Mean Reversion）に基づくトレーディングシグナルを生成
        
        Parameters:
        -----------
        data : pandas.DataFrame
            OHLCV データと指標
            
        Returns:
        --------
        dict
            シグナル情報
        """
        if data.empty or len(data) < 30:
            return {}
        
        # 最新のデータポイント
        current = data.iloc[-1]
        
        # 基本シグナル
        signal = 0
        
        # ボリンジャーバンドを利用した平均回帰
        if 'BB_upper' in current and 'BB_middle' in current and 'BB_lower' in current:
            # 過度な逸脱を検出（統計的に異常な値）
            
            # オーバーソールド状態（買い）
            if current['close'] < current['BB_lower'] * 0.995:  # 下限から0.5%以上下に逸脱
                # RSIによる確認（過度な売られすぎ）
                if current['RSI'] < 30:
                    signal = 1
            
            # オーバーボウト状態（売り）
            elif current['close'] > current['BB_upper'] * 1.005:  # 上限から0.5%以上上に逸脱
                # RSIによる確認（過度な買われすぎ）
                if current['RSI'] > 70:
                    signal = -1
        
        # Z-スコア計算（標準偏差を使った偏差の測定）
        price_series = data['close'].tail(30)
        mean_price = price_series.mean()
        std_price = price_series.std()
        z_score = (current['close'] - mean_price) / std_price if std_price > 0 else 0
        
        # Z-スコアによるフィルタリング
        if abs(z_score) < 2.0:  # 標準偏差の2倍以内は正常範囲とみなす
            signal = 0
        
        # トレンドとの一致確認（トレンドに逆らう取引を避ける）
        if 'ma_signal' in current:
            # 買いシグナルなのに下降トレンドの場合、注意
            if signal > 0 and current['ma_signal'] < 0:
                # ただし強いオーバーソールドの場合は許可
                if current['RSI'] >= 30:
                    signal = 0
            
            # 売りシグナルなのに上昇トレンドの場合、注意
            if signal < 0 and current['ma_signal'] > 0:
                # ただし強いオーバーボウトの場合は許可
                if current['RSI'] <= 70:
                    signal = 0
        
        # ボラティリティフィルター
        atr_ratio = current.get('ATR', current['close'] * 0.01) / current['close']
        
        # 平均回帰はボラティリティが低い環境で効果的
        if atr_ratio > 0.015:  # 高ボラティリティ環境では平均回帰を避ける
            signal = 0
        
        # シグナル情報をまとめる
        signal_info = {
            'timestamp': current['timestamp'],
            'open': current['open'],
            'high': current['high'],
            'low': current['low'],
            'close': current['close'],
            'signal': signal,
            'mean_price': mean_price,
            'std_price': std_price,
            'z_score': z_score,
            'atr_ratio': atr_ratio,
            'mean_reversion_detected': True if signal != 0 else False
        }
        
        # 既存の指標情報も追加
        for key in ['RSI', 'BB_upper', 'BB_middle', 'BB_lower', 'ma_signal']:
            if key in current:
                signal_info[key] = current[key]
        
        return signal_info

    # trading_bot.py に追加する新しいメソッド
    def integrate_multiple_strategies(self, data):
        """
        複数の取引戦略からシグナルを統合
        
        Parameters:
        -----------
        data : pandas.DataFrame
            OHLCV データと指標
            
        Returns:
        --------
        dict
            統合されたシグナル情報
        """
        if data.empty:
            return {}
        
        # 各戦略からのシグナルを取得
        trend_signal = self.generate_trading_signals(data)
        breakout_signal = self.generate_breakout_signals(data)
        mean_reversion_signal = self.generate_mean_reversion_signals(data)
        
        # 最新のデータポイント
        current = data.iloc[-1]
        
        # シグナルと信頼度スコア
        signals = {
            'trend': trend_signal.get('signal', 0),
            'breakout': breakout_signal.get('signal', 0),
            'mean_reversion': mean_reversion_signal.get('signal', 0)
        }
        
        # 市場環境の分析（トレンド/レンジ判定）
        # ADXを使ってトレンドの強さを評価
        adx_value = self.calculate_adx(data)
        is_trending = adx_value > 25  # ADX 25以上はトレンド相場とみなす
        
        # ボラティリティ評価
        atr = current.get('ATR', current['close'] * 0.01)
        atr_ratio = atr / current['close']
        is_high_volatility = atr_ratio > 0.012
        is_low_volatility = atr_ratio < 0.006
        
        # 戦略の重み付け（市場環境に基づいて調整）
        weights = {
            'trend': 0.0,
            'breakout': 0.0,
            'mean_reversion': 0.0
        }
        
        # トレンド環境での重み付け
        if is_trending:
            weights['trend'] = 0.6
            weights['breakout'] = 0.3
            weights['mean_reversion'] = 0.1
            
            # 高ボラティリティならブレイクアウトの重みを上げる
            if is_high_volatility:
                weights['trend'] = 0.5
                weights['breakout'] = 0.4
                weights['mean_reversion'] = 0.1
        
        # レンジ環境での重み付け
        else:
            weights['trend'] = 0.2
            weights['breakout'] = 0.3
            weights['mean_reversion'] = 0.5
            
            # 低ボラティリティなら平均回帰の重みを上げる
            if is_low_volatility:
                weights['trend'] = 0.1
                weights['breakout'] = 0.2
                weights['mean_reversion'] = 0.7
        
        # 加重平均でシグナルを統合
        weighted_signal = 0
        for strategy, signal in signals.items():
            weighted_signal += signal * weights[strategy]
        
        # 最終シグナルの決定（閾値を適用）
        final_signal = 0
        if weighted_signal >= 0.3:  # 買いシグナル閾値
            final_signal = 1
        elif weighted_signal <= -0.3:  # 売りシグナル閾値
            final_signal = -1
        
        # 戦略間の一貫性チェック（オプション）
        strategy_agreement = sum(1 for s in signals.values() if s > 0) - sum(1 for s in signals.values() if s < 0)
        
        # 強い一貫性がある場合、シグナルを強化
        if abs(strategy_agreement) >= 2 and strategy_agreement * final_signal > 0:
            # シグナルの方向と一致する戦略が2つ以上ある場合
            # これは既に final_signal に反映されているのでここでは何もしない
            pass
        
        # 戦略間で強い矛盾がある場合、シグナルを無効化
        if abs(strategy_agreement) == 0 and abs(weighted_signal) < 0.4:
            # 戦略間で意見が分かれている場合、確信度が高くない限りシグナルを出さない
            final_signal = 0
        
        # 統合されたシグナル情報をまとめる
        integrated_info = {
            'timestamp': current['timestamp'],
            'open': current['open'],
            'high': current['high'],
            'low': current['low'],
            'close': current['close'],
            'signal': final_signal,
            'weighted_signal': weighted_signal,
            'adx': adx_value,
            'is_trending': is_trending,
            'atr_ratio': atr_ratio,
            'strategy_agreement': strategy_agreement,
            'strategy_signals': signals,
            'strategy_weights': weights
        }
        
        # 利用可能な指標情報を追加
        for key in ['RSI', 'MACD', 'BB_upper', 'BB_lower', 'SMA_short', 'SMA_long']:
            if key in current:
                integrated_info[key] = current[key]
        
        return integrated_info

    # リスク/リワード比を市場環境に合わせて調整
    def adaptive_risk_reward(self, signal_info):
        """
        市場環境とシグナルタイプに基づいて動的にリスク/リワード比を調整
        
        Parameters:
        -----------
        signal_info : dict
            統合されたシグナル情報
            
        Returns:
        --------
        tuple
            (stop_loss_percent, take_profit_percent)
        """
        # 基本のリスク/リワード設定
        sl_percent = self.stop_loss_percent
        tp_percent = self.take_profit_percent
        
        # どの戦略がシグナルを出したか特定
        dominant_strategy = None
        max_weight = 0
        
        for strategy, weight in signal_info['strategy_weights'].items():
            strategy_signal = signal_info['strategy_signals'][strategy]
            if strategy_signal != 0 and weight > max_weight:
                max_weight = weight
                dominant_strategy = strategy
        
        # 戦略タイプに応じた調整
        if dominant_strategy == 'trend':
            # トレンドフォロー戦略ではより広いTP設定
            tp_percent *= 1.2
        elif dominant_strategy == 'breakout':
            # ブレイクアウト戦略では迅速なTP/SL
            tp_percent *= 1.1
            sl_percent *= 0.9
        elif dominant_strategy == 'mean_reversion':
            # 平均回帰戦略では狭いTP/SL
            tp_percent *= 0.8
            sl_percent *= 0.8
        
        # 市場環境（トレンド/レンジ）に基づく調整
        if signal_info.get('is_trending', False):
            # トレンド相場ではより広いTP
            tp_percent *= 1.2
        else:
            # レンジ相場ではより狭いTP
            tp_percent *= 0.9
        
        # ボラティリティに基づく調整
        atr_ratio = signal_info.get('atr_ratio', 0.01)
        if atr_ratio > 0.015:  # 高ボラティリティ
            # 高ボラティリティ環境ではSLを広く
            sl_percent *= 1.3
            tp_percent *= 1.2
        elif atr_ratio < 0.006:  # 低ボラティリティ
            # 低ボラティリティ環境ではSL/TPを狭く
            sl_percent *= 0.8
            tp_percent *= 0.8
        
        # 戦略間の一貫性に基づく調整
        agreement = signal_info.get('strategy_agreement', 0)
        if abs(agreement) >= 2:  # 強い一貫性
            # 戦略間の強い一貫性があればリスクを減らし、リワードを増やす
            sl_percent *= 0.9
            tp_percent *= 1.1
        
        # 最小リスク/リワード比の保証
        min_risk_reward = 2.0
        if tp_percent / sl_percent < min_risk_reward:
            tp_percent = sl_percent * min_risk_reward
        
        # 最終値を妥当な範囲に収める
        sl_percent = max(0.8, min(sl_percent, 2.5))
        tp_percent = max(2.0, min(tp_percent, 10.0))
        
        return sl_percent, tp_percent




def evaluate_combination(params_dict, common_data, env_dict):
        os.environ.update(env_dict)  # .env の値を再設定（必要なら）
        bot = EnhancedTradingBot()
        for k, v in params_dict.items():
            setattr(bot, k, v)
        result = bot._run_backtest_for_optimization(common_data.copy())
        return {**params_dict, **result}

def main():
    """メイン関数"""
    parser = argparse.ArgumentParser(description='高度なBinanceトレーディングボット')
    parser.add_argument('--mode', choices=['backtest', 'live', 'optimize'], default='backtest',
                        help='実行モード: backtest, live, optimize')
    args = parser.parse_args()
    
    bot = EnhancedTradingBot()

    if args.mode == 'backtest':
        bot.run_backtest()
    elif args.mode == 'live':
        bot.run_live_trading()
    elif args.mode == 'optimize':
    ##    bot.optimize_parameters()
        bot.optimize_parameters_parallel()



if __name__ == "__main__":
    main()