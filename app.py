"""
Anti-Fragile Stock & Startup Screener (Streamlit)
=================================================
Run locally:  streamlit run app.py
Deploy:       put app.py and requirements.txt in the root of a GitHub repo, then point
              Streamlit Community Cloud at app.py.

Two lenses
  1. Public Equity Screen - 15 independent pillars for profitable listed companies (US and India).
  2. Venture Lens         - 6 pillars plus a cash-runway / breakeven model for pre-profit companies.

Version 2 adds an optional macro overlay. Every part of it is OFF by default, so out of the box the
scores, labels, gates and forward valuation are exactly those of version 1:
  * Rate links     - tie the required return to the 10-year yield, and the exit-multiple floor to rates.
  * Stress tests   - information only: interest cover if rates rise, debt due within a year, earnings
                     cyclicality, gross-margin pricing power, and a regulation flag that you set yourself.
  * Macro backdrop - US and India market readings (rates, inflation, volatility, trend), side by side.
Nothing macro-related changes a pillar weight or a pillar score.

Version 2.1 adds one more optional tab, also OFF by default and also information only:
  * Sector & market context - the stock's sector against the market, trend health, how the sector held
                     up in past sell-offs, an all-sector leaderboard, headlines, ownership figures and a
                     checklist for your own research on a catalyst. It never touches a score or a label.

Version 2.2 adds two more sections inside that tab, with the same rules (off by default, information only):
  * Capital allocation - asset growth, capital spending against depreciation, cash paid for acquisitions,
                     goodwill, debt and share-count changes, worked out from the annual statements the app
                     has already loaded (no extra fetching).
  * Company filings - a US company's recent SEC 8-K reports with their item codes (agreements, completed
                     acquisitions, equity sales, officer changes and so on). It needs a contact email, which
                     the SEC asks every automated request to carry; nothing is fetched without one.

Design rules
  * Nothing is invented. A metric that cannot be sourced shows "n/a", is left out of the score and
    the remaining weights are rescaled. Data coverage is shown next to every score.
  * Every underlying metric is used once (no double counting).
  * Safety gates cap the result however high the composite score is.
  * Banks, insurers and REITs are blocked by default; utilities and cyclicals get a caution.
  * Output is a screen result (Strong / Mixed / Weak), not a buy or sell call.
"""
from __future__ import annotations

import html as html_lib
import json
import math
import re
import time
import urllib.request
from dataclasses import dataclass
from datetime import datetime, timedelta, timezone
from typing import Optional

import pandas as pd
import plotly.express as px
import streamlit as st
import yfinance as yf

st.set_page_config(
    page_title="Anti-Fragile Stock & Startup Screener",
    page_icon="🛡️",
    layout="wide",
)

# ══════════════════════════════════════════════════════════════════════════════
# 1. CONFIGURATION  (tune thresholds here)
# ══════════════════════════════════════════════════════════════════════════════
CACHE_TTL = 60 * 60            # seconds a Yahoo snapshot stays cached
MIN_COVERAGE_PUBLIC = 0.70     # share of pillar weight that must have data to issue a result
MIN_COVERAGE_VENTURE = 0.65
STRONG_MIN = 3.8               # composite >= this -> Strong
MIXED_MIN = 3.0                # composite >= this -> Mixed, otherwise Weak
ROUTE_GROWTH_MIN = 0.15        # loss-making and revenue growth >= this -> Venture lens
MIN_PE = 15.0                  # lowest exit P/E the PEG rule can produce (about the long-run market average).
                               # PEG logic breaks down at low growth (5% growth would imply 7.5x), so it is floored.
EPS_GROWTH_FADE = 0.85         # year-2 EPS growth = year-1 growth x this
PROJECTION_YEARS = 5
PROJECTION_GROWTH_CAP = 1.5    # starting growth used in the venture projection is capped at 150%
DEFAULT_FADE = 0.80
DEFAULT_COST_RATIO = 0.60

# Macro overlay (version 2). All of it is optional and off by default.
APP_VERSION = "2.2 (macro, context, capital-allocation and filings options)"
MACRO_TTL = 3 * 60 * 60        # seconds fetched macro data stays cached
HTTP_TIMEOUT = 10              # seconds to wait for FRED before giving up on it
REQ_RETURN_MIN = 0.08          # a rate-linked required return is held inside this band
REQ_RETURN_MAX = 0.15
FLOOR_PE_MIN = 10.0            # a rate-linked exit-multiple floor is held inside this band
FLOOR_PE_MAX = 25.0
DEFAULT_ERP = 0.055            # equity risk premium added to the 10-year yield (published estimates run about 4% to 6%)
DEFAULT_G_US = 0.03            # long-run growth used for the floor: US-dollar stocks
DEFAULT_G_IN = 0.05            # same for Indian stocks (higher inflation, so higher nominal growth)
DEFAULT_SHOCK = 0.02           # rate rise used by the interest-cover stress test (2 percentage points)
COVER_RISK, COVER_WATCH = 1.5, 3.0            # same cut-offs as the interest-coverage safety gates
CYC_DROP_WATCH, CYC_DROP_RISK = -0.15, -0.30  # worst year-over-year fall in operating income
CYC_RANGE_WATCH, CYC_RANGE_RISK = 0.04, 0.08  # spread between the best and worst operating margin
CAUTION_VIX = {"US": 25.0, "IN": 20.0}        # volatility-index levels usually read as elevated
CAUTION_CPI = {"US": 0.04, "IN": 0.06}        # inflation levels treated as high
CAUTION_DRAWDOWN = -0.10       # an index 10% or more below its 52-week high
CAUTION_UNEMP_RISE = 0.5       # unemployment up half a point or more from its 12-month low
REG_LEVELS = ["Not assessed", "Low", "Moderate", "High"]

MODE_PUBLIC = "Public equity screen (profitable companies)"
MODE_VENTURE = "Pre-profit / venture lens"
MODE_MACRO = "Macro backdrop (US and India)"
SRC_MANUAL = "Manual inputs"
SRC_TICKER = "Public ticker (auto-fetch)"
LOSS_AUTO = "Auto: growth companies go to the venture lens"
LOSS_VENTURE = "Always use the venture lens"
LOSS_SCREEN = "Always run the quality screen (capped at Weak)"
LOSS_OPTIONS = [LOSS_AUTO, LOSS_VENTURE, LOSS_SCREEN]

GROWTH_BASES = {
    "Conservative: lower of NI / revenue CAGR": min,
    "Balanced: average": lambda xs: sum(xs) / len(xs),
    "Optimistic: higher": max,
}

TAM_OPTIONS = ["Massive (10B+)", "Large (1B to 10B)", "Niche (under 1B)"]
TAM_UNKNOWN = "Unknown (leave out of score)"
TAM_CHOICES = TAM_OPTIONS + [TAM_UNKNOWN]
TAM_SCORES = {TAM_OPTIONS[0]: 5, TAM_OPTIONS[1]: 3, TAM_OPTIONS[2]: 1}

LABELS = {"strong": "Strong", "mixed": "Mixed", "weak": "Weak", "insufficient": "Insufficient data"}

# Sector / industry rules. "exclude" blocks the screen unless the user ticks the override;
# "caution" runs it with a warning. Yahoo files lenders and payment networks under the same sector,
# so Financial Services is decided by industry rather than blocked wholesale.
LENDER_KEYWORDS = ("Bank", "Insurance", "Mortgage", "Credit Services", "Capital Markets", "Thrift", "Conglomerate")
LENDER_TEXT = (
    "Banks, insurers, NBFCs and other lenders run on deposits and leverage, so gross margin, debt/equity "
    "and free cash flow do not mean what this rubric assumes. Use a bank-specific lens (net interest "
    "margin, gross/net NPA, capital adequacy, ROA, price/book). Yahoo files payment networks such as Visa "
    "and Mastercard under the same industry even though they do not lend: tick the sidebar checkbox to "
    "run them anyway."
)
FIN_CAUTION_TEXT = (
    "Financial-sector business model: gross margin and debt/equity may not be meaningful, so some "
    "pillars can read low for structural reasons."
)
REAL_ESTATE_TEXT = (
    "Real-estate and REIT cash flow and leverage are structurally different (depreciation, mortgage "
    "debt, FFO), so this rubric would mislead."
)
CYCLICAL_TEXT = "Cyclical sector: trailing margins and returns may reflect a commodity peak or trough."
UTILITY_TEXT = (
    "Regulated utilities carry high debt and capex by design, which this rubric penalises. "
    "Read low scores in that light."
)


def sector_rule(sector, industry=""):
    """Return (rule, explanation) for sectors the rubric fits poorly, else None."""
    sector, industry = sector or "", industry or ""
    if sector == "Financial Services":
        unknown = industry in ("", "Unknown")
        brokers = "Insurance Brokers" in industry
        if unknown or (any(k in industry for k in LENDER_KEYWORDS) and not brokers):
            return "exclude", LENDER_TEXT
        return "caution", FIN_CAUTION_TEXT
    if sector == "Real Estate":
        return "exclude", REAL_ESTATE_TEXT
    if sector == "Utilities":
        return "caution", UTILITY_TEXT
    if sector in ("Energy", "Basic Materials"):
        return "caution", CYCLICAL_TEXT
    return None

DISCLAIMER = (
    "Educational screening tool, not investment advice or a research report. Data comes from Yahoo "
    "Finance through the unofficial yfinance library and can be delayed, incomplete or wrong, "
    "especially for Indian tickers. Thresholds are uncalibrated heuristics. Check company filings "
    "before acting, and speak to a licensed adviser where the rules of your jurisdiction require it."
)


# ══════════════════════════════════════════════════════════════════════════════
# 2. SMALL UTILITIES
# ══════════════════════════════════════════════════════════════════════════════
class DataError(Exception):
    """A usable data snapshot could not be built (bad ticker, empty response, ...)."""


def num(x):
    """Return x as a finite float, else None (handles None, NaN, inf, 'Infinity', strings)."""
    if x is None or isinstance(x, bool):
        return None
    try:
        v = float(x)
    except (TypeError, ValueError):
        return None
    return v if math.isfinite(v) else None


def first_num(d, *keys):
    for k in keys:
        v = num(d.get(k))
        if v is not None:
            return v
    return None


def coalesce(*vals):
    for v in vals:
        if v is not None:
            return v
    return None


def pos(x):
    """Keep only strictly positive values (prices and market caps can never be zero or negative)."""
    return x if x is not None and x > 0 else None


def nz(x):
    """Treat an exact zero as missing. Yahoo reports 0 for margins it could not compute (for example
    when a company has no gross-profit line), and a real margin is never exactly zero."""
    return None if x is None or x == 0 else x


def fmt_pct(v, d=1):
    return "n/a" if v is None else f"{v * 100:.{d}f}%"


def fmt_x(v, d=1):
    return "n/a" if v is None else f"{v:.{d}f}x"


def fmt_price(v, sym="$"):
    return "n/a" if v is None else f"{sym}{v:,.2f}"


def fmt_big(v, sym="$"):
    """Compact money: $1.20B, ₹12,345 Cr."""
    if v is None:
        return "n/a"
    sign, a = ("-" if v < 0 else ""), abs(v)
    if sym == "₹":
        return f"{sign}₹{a / 1e7:,.0f} Cr" if a >= 1e7 else f"{sign}₹{a:,.0f}"
    for div, suffix in ((1e12, "T"), (1e9, "B"), (1e6, "M"), (1e3, "K")):
        if a >= div:
            return f"{sign}{sym}{a / div:,.2f}{suffix}"
    return f"{sign}{sym}{a:,.2f}"


def fmt_mm(v, sym="$"):
    """Format a value that is stored in millions."""
    return "n/a" if v is None else fmt_big(v * 1e6, sym)


CURRENCY_SYMBOLS = {
    "USD": "$", "INR": "₹", "EUR": "€", "GBP": "£", "JPY": "¥",
    "CNY": "¥", "CAD": "C$", "AUD": "A$", "HKD": "HK$", "SGD": "S$",
}


def currency_symbol(code, ticker=""):
    if code in CURRENCY_SYMBOLS:
        return CURRENCY_SYMBOLS[code]
    if not code:
        return "₹" if ticker.endswith((".NS", ".BO")) else "$"
    return f"{code} "


def esc(text):
    """Streamlit renders $...$ as LaTeX; escape dollar signs in markdown text."""
    return text.replace("$", "\\$")


def say(kind, text):
    """Show an info / success / warning / error box with dollar signs escaped."""
    getattr(st, kind)(esc(text))


# ══════════════════════════════════════════════════════════════════════════════
# 3. DATA LAYER  (yfinance -> plain numbers; everything below is pure and testable)
# ══════════════════════════════════════════════════════════════════════════════
def stmt_series(df, *labels):
    """Oldest-to-newest [(period_end, value)] for the first row label found in a yfinance statement."""
    if not isinstance(df, pd.DataFrame) or df.empty:
        return []
    for label in labels:
        if label not in df.index:
            continue
        row = df.loc[label]
        if isinstance(row, pd.DataFrame):  # duplicated row labels
            row = row.iloc[0]
        row = pd.to_numeric(row, errors="coerce").dropna()
        pts = [(idx, float(v)) for idx, v in row.items() if math.isfinite(v)]
        try:
            pts.sort(key=lambda p: p[0])
        except TypeError:
            pass
        if pts:
            return pts
    return []


def latest(df, *labels):
    pts = stmt_series(df, *labels)
    return pts[-1][1] if pts else None


def margin_series(num_pts, den_pts):
    den = dict(den_pts)
    return [(d, n / den[d]) for d, n in num_pts if d in den and den[d] > 0]


def cagr(points, min_points=3):
    """Compound annual growth across (date, value) points -> (rate, years); (None, 0) if not computable."""
    if len(points) < min_points:
        return None, 0
    (d0, v0), (d1, v1) = points[0], points[-1]
    if v0 <= 0 or v1 <= 0:
        return None, 0
    try:
        years = (pd.Timestamp(d1) - pd.Timestamp(d0)).days / 365.25
    except Exception:
        years = len(points) - 1
    if years < 1:
        return None, 0
    return (v1 / v0) ** (1 / years) - 1, int(round(years))


def fcf_series(cf):
    pts = stmt_series(cf, "Free Cash Flow")
    if pts:
        return pts
    ocf = dict(stmt_series(cf, "Operating Cash Flow", "Cash Flow From Continuing Operating Activities"))
    capex = dict(stmt_series(cf, "Capital Expenditure"))
    return [(d, ocf[d] - abs(capex[d])) for d in sorted(ocf) if d in capex]


def avg_return_on_capital(inc, bal, n_years=3):
    """Average ROIC = EBIT x (1 - tax) / invested capital over the latest n_years."""
    ebit = dict(stmt_series(inc, "EBIT", "Operating Income"))
    tax_calc = dict(stmt_series(inc, "Tax Rate For Calcs"))
    pretax = dict(stmt_series(inc, "Pretax Income"))
    tax = dict(stmt_series(inc, "Tax Provision"))
    inv = dict(stmt_series(bal, "Invested Capital"))
    debt = dict(stmt_series(bal, "Total Debt"))
    eq = dict(stmt_series(bal, "Stockholders Equity", "Common Stock Equity"))
    cash = dict(stmt_series(bal, "Cash Cash Equivalents And Short Term Investments", "Cash And Cash Equivalents"))
    vals = []
    for d in sorted(ebit):
        ic = inv.get(d)
        if ic is None and d in debt and d in eq:
            ic = debt[d] + eq[d] - cash.get(d, 0.0)
        if ic is None or ic <= 0:
            continue
        rate = tax_calc.get(d)
        if rate is None and pretax.get(d, 0) > 0 and d in tax:
            rate = tax[d] / pretax[d]
        rate = 0.25 if rate is None else min(max(rate, 0.0), 0.40)
        vals.append(ebit[d] * (1 - rate) / ic)
    vals = vals[-n_years:]
    return (sum(vals) / len(vals), len(vals)) if vals else (None, 0)


def avg_roe(inc, bal, n_years=3):
    ni = dict(stmt_series(inc, "Net Income", "Net Income Common Stockholders"))
    eq = dict(stmt_series(bal, "Stockholders Equity", "Common Stock Equity"))
    vals = [ni[d] / eq[d] for d in sorted(ni) if d in eq and eq[d] > 0][-n_years:]
    return (sum(vals) / len(vals), len(vals)) if vals else (None, 0)


def share_trend(points):
    """Annual change in share count -> (rate, note). Rejects series that look split-distorted."""
    if len(points) < 3:
        return None, "Fewer than 3 years of share-count data."
    vals = [v for _, v in points]
    for a, b in zip(vals, vals[1:]):
        if a <= 0 or abs(b / a - 1) > 0.35:
            return None, "Share count jumps by more than 35% in a year (likely a split), so it is excluded."
    rate, _ = cagr(points)
    return rate, ""


@st.cache_data(ttl=CACHE_TTL, max_entries=64, show_spinner=False)
def fetch_snapshot(ticker: str) -> dict:
    """Pull info and the three annual statements from Yahoo. Raises (and so is not cached) on failure."""
    tk = yf.Ticker(ticker)
    info = tk.info
    if not isinstance(info, dict) or not info:
        raise DataError(f"Yahoo returned no data for '{ticker}'. Check the symbol and try again.")
    price = first_num(info, "currentPrice", "regularMarketPrice", "previousClose")
    if price is None and not (info.get("longName") or info.get("shortName")):
        raise DataError(
            f"No market data found for '{ticker}'. Check the symbol: Indian stocks need .NS (NSE) or .BO (BSE), "
            "for example RELIANCE.NS."
        )
    if len(info) < 8:  # a real equity has 100+ fields; a handful means Yahoo answered badly (often rate limiting)
        raise DataError(
            f"Yahoo returned only partial data for '{ticker}' ({len(info)} fields), which often happens when it is "
            "rate-limiting a shared server. Wait a minute and click Run audit again."
        )
    frames = {}
    for key, attr in (("income", "financials"), ("balance", "balance_sheet"), ("cashflow", "cashflow")):
        try:
            df = getattr(tk, attr)
        except Exception:  # statements are optional; missing ones just reduce data coverage
            df = None
        frames[key] = df if isinstance(df, pd.DataFrame) else pd.DataFrame()
    return {
        "ticker": ticker,
        "info": dict(info),
        "fetched_at": datetime.now(timezone.utc).strftime("%d %b %Y %H:%M UTC"),
        **frames,
    }


def extract_public_metrics(snap):
    """Turn a snapshot into the plain metrics the public screen needs. Missing -> None, never a default."""
    info, inc, bal, cf = snap["info"], snap["income"], snap["balance"], snap["cashflow"]
    t = snap["ticker"]
    cur, fcur = info.get("currency"), info.get("financialCurrency")
    m = {
        "ticker": t,
        "fetched_at": snap["fetched_at"],
        "name": info.get("longName") or info.get("shortName") or t,
        "sector": info.get("sector") or "Unknown",
        "industry": info.get("industry") or "Unknown",
        "currency": cur,
        "fin_currency": fcur,
        "sym": currency_symbol(cur, t),
        "fin_sym": currency_symbol(fcur or cur, t),
        "currency_mismatch": bool(cur and fcur and cur != fcur),
        "price": pos(first_num(info, "currentPrice", "regularMarketPrice", "previousClose")),
        "market_cap": pos(first_num(info, "marketCap")),
        "pb": first_num(info, "priceToBook"),
        "roe_latest": first_num(info, "returnOnEquity"),
    }

    # Income statement ---------------------------------------------------------
    rev_pts = stmt_series(inc, "Total Revenue", "Operating Revenue")
    ni_pts = stmt_series(inc, "Net Income", "Net Income Common Stockholders")
    gp_pts = stmt_series(inc, "Gross Profit")
    ebit_pts = stmt_series(inc, "EBIT", "Operating Income")
    int_pts = stmt_series(inc, "Interest Expense", "Interest Expense Non Operating")
    m["rev_ttm"] = coalesce(first_num(info, "totalRevenue"), rev_pts[-1][1] if rev_pts else None)
    m["ni_ttm"] = coalesce(first_num(info, "netIncomeToCommon"), ni_pts[-1][1] if ni_pts else None)
    m["rev_growth_yoy"] = first_num(info, "revenueGrowth")
    m["earn_growth"] = first_num(info, "earningsGrowth")

    gm_pts = margin_series(gp_pts, rev_pts)
    m["gross_margin"] = coalesce(nz(first_num(info, "grossMargins")), gm_pts[-1][1] if gm_pts else None)
    m["gm_trend_pp"] = (gm_pts[-1][1] - gm_pts[0][1]) * 100 if len(gm_pts) >= 3 else None
    om_pts = margin_series(ebit_pts, rev_pts)
    m["op_margin"] = coalesce(nz(first_num(info, "operatingMargins")), om_pts[-1][1] if om_pts else None)
    m["rev_cagr"], m["rev_years"] = cagr(rev_pts)
    m["ni_cagr"], m["ni_years"] = cagr(ni_pts)

    # Balance sheet and leverage -------------------------------------------------
    eq_pts = stmt_series(bal, "Stockholders Equity", "Common Stock Equity", "Total Equity Gross Minority Interest")
    m["equity"] = eq_pts[-1][1] if eq_pts else None
    m["total_debt"] = coalesce(first_num(info, "totalDebt"), latest(bal, "Total Debt"))
    m["cash"] = coalesce(
        first_num(info, "totalCash"),
        latest(bal, "Cash Cash Equivalents And Short Term Investments", "Cash And Cash Equivalents"),
    )
    de = first_num(info, "debtToEquity")  # Yahoo reports this as a percentage
    if de is None and m["total_debt"] is not None and m["equity"] and m["equity"] > 0:
        de = m["total_debt"] / m["equity"] * 100
    m["neg_equity"] = bool((m["equity"] is not None and m["equity"] <= 0) or (de is not None and de < 0))
    m["de"] = None if m["neg_equity"] else de

    ebit_latest = ebit_pts[-1][1] if ebit_pts else None
    int_latest = abs(int_pts[-1][1]) if int_pts else None
    m["no_debt"] = False
    if ebit_latest is not None and int_latest:
        m["int_cov"] = ebit_latest / int_latest
    elif m["total_debt"] is not None and m["total_debt"] <= 0:
        m["int_cov"], m["no_debt"] = 99.0, True
    else:
        m["int_cov"] = None

    ebitda = first_num(info, "ebitda")
    td, cash = m["total_debt"], m["cash"]
    m["nd_ebitda"] = (td - cash) / ebitda if (td is not None and cash is not None and ebitda and ebitda > 0) else None

    # Returns on capital ---------------------------------------------------------
    roic, n = avg_return_on_capital(inc, bal)
    if roic is not None:
        m["roc"], m["roc_label"] = roic, f"ROIC (avg {n}y)"
    else:
        roe, n = avg_roe(inc, bal)
        if roe is not None:
            m["roc"], m["roc_label"] = roe, f"ROE (avg {n}y)"
        elif m["roe_latest"] is not None and not m["neg_equity"]:
            m["roc"], m["roc_label"] = m["roe_latest"], "ROE (latest)"
        else:
            m["roc"], m["roc_label"] = None, "ROIC"

    # Cash flow ------------------------------------------------------------------
    fcf_pts = fcf_series(cf)[-4:]
    m["fcf_ttm"] = coalesce(first_num(info, "freeCashflow"), fcf_pts[-1][1] if fcf_pts else None)
    m["fcf_years"] = len(fcf_pts)
    m["fcf_neg_years"] = sum(1 for _, v in fcf_pts if v < 0)
    ni, fcf, mc = m["ni_ttm"], m["fcf_ttm"], m["market_cap"]
    m["fcf_conv"] = fcf / ni if (fcf is not None and ni is not None and ni > 0) else None
    # FCF is in the reporting currency and market cap in the trading currency: only compare if they match.
    m["fcf_yield"] = fcf / mc if (fcf is not None and mc and mc > 0 and not m["currency_mismatch"]) else None
    sbc = latest(cf, "Stock Based Compensation")
    rev_latest = rev_pts[-1][1] if rev_pts else None
    m["sbc_pct"] = sbc / rev_latest if (sbc is not None and rev_latest and rev_latest > 0) else None

    # Valuation ------------------------------------------------------------------
    m["eps_ttm"] = first_num(info, "trailingEps")
    pe = first_num(info, "trailingPE")
    if pe is None and m["price"] and m["eps_ttm"] and m["eps_ttm"] > 0:
        pe = m["price"] / m["eps_ttm"]
    m["pe_ttm"] = pe if (pe is not None and pe > 0) else None
    peg = next((v for v in (num(info.get("pegRatio")), num(info.get("trailingPegRatio"))) if v is not None and v > 0), None)
    m["peg_source"] = "Yahoo"
    if peg is None and m["pe_ttm"] and m["ni_cagr"] and m["ni_cagr"] >= 0.03:
        peg, m["peg_source"] = m["pe_ttm"] / (m["ni_cagr"] * 100), "P/E ÷ NI CAGR"
    m["peg"] = peg

    # Governance and sentiment ------------------------------------------------------
    ins = first_num(info, "heldPercentInsiders")
    m["insider_pct"] = ins * 100 if ins is not None else None
    m["share_cagr"], m["share_note"] = share_trend(stmt_series(bal, "Ordinary Shares Number", "Share Issued"))
    mean, n_an = first_num(info, "recommendationMean"), first_num(info, "numberOfAnalystOpinions")
    m["analyst_mean"] = mean if (mean is not None and n_an is not None and n_an >= 3) else None
    m["analyst_n"] = n_an
    m["analyst_target"] = first_num(info, "targetMeanPrice")  # shown for reference only, never used for valuation
    return m


# ══════════════════════════════════════════════════════════════════════════════
# 3b. MACRO DATA LAYER  (optional: a failed fetch can never change a stock's score)
# ══════════════════════════════════════════════════════════════════════════════
def fred_start():
    """Start date for FRED requests: 1 January two years back, so the cache key stays stable all year."""
    return f"{datetime.now(timezone.utc).year - 2}-01-01"


def parse_fred_csv(text):
    """FRED graph CSV -> [(date, value)], oldest first. Columns are read by position (FRED has renamed its header
    before) and '.' marks a missing observation. A line that is not 'date,number' is skipped, so an HTML error page
    gives an empty list rather than nonsense."""
    rows = []
    for i, line in enumerate((text or "").splitlines()):
        parts = line.split(",")
        if i == 0 or len(parts) < 2:
            continue
        d, v = parts[0].strip(), num(parts[1].strip())
        if v is not None and len(d) == 10 and d[4] == "-" and d[7] == "-":
            rows.append((d, v))
    return rows


@st.cache_data(ttl=MACRO_TTL, max_entries=32, show_spinner=False)
def fetch_fred(series_id: str, start: str) -> list:
    """One FRED series as [(date, value)]. Raises (and so is not cached) when FRED cannot be reached."""
    url = f"https://fred.stlouisfed.org/graph/fredgraph.csv?id={series_id}&cosd={start}"
    request = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (compatible; stock-screener)"})
    with urllib.request.urlopen(request, timeout=HTTP_TIMEOUT) as response:
        text = response.read().decode("utf-8", errors="replace")
    rows = parse_fred_csv(text)
    if not rows:
        raise DataError(f"FRED returned no usable data for {series_id}.")
    return rows


def _yahoo_closes(symbol, period):
    """Daily closes of a Yahoo symbol as [(date, close)], oldest first. Raises DataError when there are none."""
    hist = yf.Ticker(symbol).history(period=period, auto_adjust=False)
    if not isinstance(hist, pd.DataFrame) or hist.empty or "Close" not in hist.columns:
        raise DataError(f"Yahoo returned no price history for {symbol}.")
    closes = pd.to_numeric(hist["Close"], errors="coerce").dropna()
    pts = [(pd.Timestamp(idx).strftime("%Y-%m-%d"), float(v)) for idx, v in closes.items() if math.isfinite(v)]
    if not pts:
        raise DataError(f"Yahoo returned no usable closes for {symbol}.")
    return pts


@st.cache_data(ttl=MACRO_TTL, max_entries=16, show_spinner=False)
def fetch_market_close(symbol: str, period: str) -> list:
    """Daily closes of a Yahoo symbol (an index, a volatility index or a yield) as [(date, close)]."""
    return _yahoo_closes(symbol, period)


def yield_reading(sym, fred_id, get_mkt, get_fred, errors):
    """Latest yield in percent -> (value, as_of, source), or None. Yahoo first, FRED as the backup."""
    attempts = (
        (f"Yahoo {sym}", lambda: get_mkt(sym, "1mo")),
        (f"FRED {fred_id}", lambda: get_fred(fred_id, fred_start())),
    )
    for source, fetch in attempts:
        try:
            as_of, v = fetch()[-1]
        except Exception as exc:  # noqa: BLE001 - any network or parsing problem just moves on to the next source
            errors.append(f"{source}: {type(exc).__name__}")
            continue
        if 0 < v < 25:
            return v, as_of, source
        errors.append(f"{source}: implausible yield")
    return None


def trend_stats(pts):
    """[(date, close)] oldest first -> last close, its date, gap to the 200-day average and to the 52-week high."""
    if not pts:
        return None
    closes = [v for _, v in pts]
    last = closes[-1]
    ma200 = sum(closes[-200:]) / 200 if len(closes) >= 200 else None
    high = max(closes[-252:])
    return {"last": last, "as_of": pts[-1][0],
            "vs_ma200": (last / ma200 - 1) if ma200 else None,
            "drawdown": (last / high - 1) if high > 0 else None}


def yoy_change(rows):
    """Monthly [(date, value)] -> (date, change over the same month a year earlier), or None."""
    if not rows:
        return None
    d1, v1 = rows[-1]
    prior = dict(rows).get(f"{int(d1[:4]) - 1}{d1[4:]}")
    return (d1, v1 / prior - 1) if prior and prior > 0 else None


def rise_from_low(rows, window=12):
    """[(date, value)] -> (date, latest value minus the lowest of the last `window` readings), or None."""
    if len(rows) < 3:
        return None
    return rows[-1][0], rows[-1][1] - min(v for _, v in rows[-window:])


def _pct1(v):
    return f"{v:.1f}%"


def _pct2(v):
    return f"{v:.2f}%"


def _gap(v):
    """Gap to a high, shown as a plain negative number (0.0% when at the high, never '-0.0%')."""
    return f"{round(v, 1) + 0.0:.1f}%"


def macro_row(key, label, value, disp, as_of="", source="", rule="", signal=None):
    """One line of the macro panel. signal: True = caution active, False = not, None = not a signal or no data."""
    return {"key": key, "label": label, "value": value, "disp": disp, "as_of": as_of, "source": source,
            "rule": rule, "signal": signal}


def add_reading(rows, key, label, reading, fmt, rule="", signal=None, missing="n/a"):
    """reading = (value, as_of, source) or None."""
    if reading is None:
        rows.append(macro_row(key, label, None, missing))
        return
    v, as_of, source = reading
    rows.append(macro_row(key, label, v, fmt(v), as_of, source, rule, signal(v) if signal else None))


def collect_macro(mc, get_mkt=None, get_fred=None):
    """US and India readings -> {"us": [rows], "in": [rows], "y10": {"US": fraction or None, "IN": ...},
    "errors": [...], "fetched_at": text}. Each indicator is fetched on its own, so one failure leaves the rest."""
    get_mkt = get_mkt or fetch_market_close
    get_fred = get_fred or fetch_fred
    errors, start = [], fred_start()

    def fetch(fn, *args):
        try:
            return fn(*args)
        except Exception as exc:  # noqa: BLE001 - one failed indicator must not hide the others
            errors.append(f"{args[0]}: {type(exc).__name__}")
            return None

    def latest_of(rows, source):
        return (rows[-1][1], rows[-1][0], source) if rows else None

    def index_rows(out, key, name, symbol):
        ts = trend_stats(fetch(get_mkt, symbol, "1y"))
        source = f"Yahoo {symbol}"
        ma = None if ts is None or ts["vs_ma200"] is None else (ts["vs_ma200"] * 100, ts["as_of"], source)
        add_reading(out, key + "_ma", f"{name} vs its 200-day average", ma, lambda v: f"{v:+.1f}%",
                    "below the 200-day average", lambda v: v < 0)
        dd = None if ts is None or ts["drawdown"] is None else (ts["drawdown"] * 100, ts["as_of"], source)
        add_reading(out, key + "_dd", f"{name} vs its 52-week high", dd, _gap,
                    f"{abs(CAUTION_DRAWDOWN) * 100:.0f}% or more below the high", lambda v: v <= CAUTION_DRAWDOWN * 100)

    # United States ------------------------------------------------------------------------------
    us = []
    override = mc.get("us_y10")
    y10 = (override * 100, "", "entered by you") if override else yield_reading("^TNX", "DGS10", get_mkt, get_fred, errors)
    y3m = yield_reading("^IRX", "DTB3", get_mkt, get_fred, errors)
    add_reading(us, "y10", "10-year Treasury yield", y10, _pct2)
    add_reading(us, "y3m", "3-month Treasury bill yield", y3m, _pct2)
    curve = (y10[0] - y3m[0], max(y10[1], y3m[1]), "calculated") if (y10 and y3m) else None
    add_reading(us, "curve", "Yield curve (10-year minus 3-month)", curve, lambda v: f"{v:+.2f} pts",
                "10-year below 3-month (inverted)", lambda v: v < 0)
    add_reading(us, "ff", "Fed funds rate (effective)", latest_of(fetch(get_fred, "DFF", start), "FRED DFF"), _pct2)
    yoy = yoy_change(fetch(get_fred, "CPIAUCSL", start) or [])
    cpi = (yoy[1] * 100, yoy[0], "FRED CPIAUCSL") if yoy else None
    add_reading(us, "cpi", "Consumer price inflation (year on year)", cpi, _pct1,
                f"at or above {CAUTION_CPI['US'] * 100:.0f}%", lambda v: v >= CAUTION_CPI["US"] * 100)
    real = (y10[0] - cpi[0], cpi[1], "calculated") if (y10 and cpi) else None
    add_reading(us, "real", "10-year yield minus latest inflation (crude real yield)", real, lambda v: f"{v:+.2f} pts")
    unemp = fetch(get_fred, "UNRATE", start) or []
    rise = rise_from_low(unemp)
    if rise is None:
        add_reading(us, "unemp", "Unemployment rate", None, _pct1)
    else:
        us.append(macro_row("unemp", "Unemployment rate", rise[1],
                            f"{unemp[-1][1]:.1f}% ({rise[1]:+.1f} pts vs its 12-month low)", rise[0], "FRED UNRATE",
                            f"up {CAUTION_UNEMP_RISE:.1f} pts or more from the 12-month low",
                            rise[1] >= CAUTION_UNEMP_RISE))
    add_reading(us, "vix", "VIX (US equity volatility)", latest_of(fetch(get_mkt, "^VIX", "1y"), "Yahoo ^VIX"),
                lambda v: f"{v:.1f}", f"at or above {CAUTION_VIX['US']:.0f}", lambda v: v >= CAUTION_VIX["US"])
    index_rows(us, "spx", "S&P 500", "^GSPC")

    # India: market data is automatic, policy rate / yield / inflation are typed in -----------------------
    ind = []
    index_rows(ind, "nifty", "Nifty 50", "^NSEI")
    add_reading(ind, "ivix", "India VIX (equity volatility)",
                latest_of(fetch(get_mkt, "^INDIAVIX", "1y"), "Yahoo ^INDIAVIX"), lambda v: f"{v:.1f}",
                f"at or above {CAUTION_VIX['IN']:.0f}", lambda v: v >= CAUTION_VIX["IN"])

    def typed(key):
        return None if mc.get(key) is None else (mc[key] * 100, "", "entered by you")

    repo, g10, cpi_in = typed("in_repo"), typed("in_y10"), typed("in_cpi")
    add_reading(ind, "repo", "RBI repo rate", repo, _pct2, missing="not entered")
    add_reading(ind, "g10", "India 10-year government bond yield", g10, _pct2, missing="not entered")
    add_reading(ind, "cpi", "Consumer price inflation (latest, year on year)", cpi_in, _pct1,
                f"at or above {CAUTION_CPI['IN'] * 100:.0f}%", lambda v: v >= CAUTION_CPI["IN"] * 100,
                missing="not entered")
    real_in = (g10[0] - cpi_in[0], "", "calculated") if (g10 and cpi_in) else None
    add_reading(ind, "real", "10-year yield minus latest inflation (crude real yield)", real_in,
                lambda v: f"{v:+.2f} pts", missing="needs the two inputs above")

    return {"us": us, "in": ind, "errors": errors,
            "y10": {"US": y10[0] / 100 if y10 else None, "IN": mc.get("in_y10")},
            "fetched_at": datetime.now(timezone.utc).strftime("%d %b %Y %H:%M UTC")}


# ══════════════════════════════════════════════════════════════════════════════
# 3c. SECTOR AND MARKET CONTEXT  (version 2.1, optional: information only, never part of a score or a label)
# ══════════════════════════════════════════════════════════════════════════════
CTX_TTL = 3 * 60 * 60              # seconds fetched price series stay cached
NEWS_TTL = 30 * 60                 # headlines go stale faster
NEWS_LIMIT = 8
CTX_WINDOWS = (("1M", 21), ("3M", 63), ("6M", 126), ("12M", 252))     # label, trading days
CTX_SLACK_DAYS = 7                 # a fixed span may start or end this many calendar days inside the series

CTX_BENCH = {"US": ("SPY", "S&P 500 fund (SPY)"), "IN": ("^NSEI", "Nifty 50 (^NSEI)")}
# Leaderboard rows are (label, Yahoo symbol). The US rows are the Select Sector SPDR funds, labelled with Yahoo's own
# sector names so that a stock's sector maps straight across. The Indian rows are NSE sector indexes.
CTX_US_BOARD = (
    ("Technology", "XLK"), ("Consumer Cyclical", "XLY"), ("Consumer Defensive", "XLP"), ("Healthcare", "XLV"),
    ("Financial Services", "XLF"), ("Industrials", "XLI"), ("Energy", "XLE"), ("Basic Materials", "XLB"),
    ("Utilities", "XLU"), ("Real Estate", "XLRE"), ("Communication Services", "XLC"),
)
CTX_IN_BOARD = (
    ("Nifty IT", "^CNXIT"), ("Nifty FMCG", "^CNXFMCG"), ("Nifty Pharma", "^CNXPHARMA"), ("Nifty Auto", "^CNXAUTO"),
    ("Nifty Metal", "^CNXMETAL"), ("Nifty Energy", "^CNXENERGY"), ("Nifty Realty", "^CNXREALTY"),
    ("Nifty Infrastructure", "^CNXINFRA"), ("Nifty Financial Services", "^CNXFIN"), ("Nifty Bank", "^NSEBANK"),
)
CTX_IN_PROXY = {                   # Yahoo sector -> (index, caution about how well it fits)
    "Technology": ("^CNXIT", ""),
    "Consumer Defensive": ("^CNXFMCG", ""),
    "Healthcare": ("^CNXPHARMA", ""),
    "Basic Materials": ("^CNXMETAL", "This index covers metals and mining only."),
    "Energy": ("^CNXENERGY", ""),
    "Utilities": ("^CNXENERGY", "A loose fit: this index mixes oil, gas and power companies."),
    "Real Estate": ("^CNXREALTY", ""),
    "Industrials": ("^CNXINFRA", "A loose fit: there is no industrials index, so the infrastructure index is used."),
    "Financial Services": ("^CNXFIN", ""),
}
CTX_TAPE = {                       # defensive and cyclical groups, by symbol (the same split used in the back-test)
    "US": {"defensive": ("XLU", "XLP", "XLV"), "cyclical": ("XLK", "XLY", "XLI", "XLB", "XLE")},
    "IN": {"defensive": ("^CNXFMCG", "^CNXPHARMA"), "cyclical": ("^CNXAUTO", "^CNXMETAL", "^CNXREALTY", "^CNXINFRA")},
}
# Past sell-offs, as (name, earliest peak, latest peak, latest trough). The peak and the trough are then found in the
# market's own closing prices: the highest close in the first range, and the lowest close after it.
CTX_EPISODES = {
    "US": (("Financial crisis", "2007-01-01", "2008-06-30", "2010-01-01"),
           ("Covid crash", "2020-01-01", "2020-03-01", "2020-06-30"),
           ("2022 bear market", "2021-10-01", "2022-03-01", "2023-01-01")),
    "IN": (("2008 crash", "2007-10-01", "2008-06-30", "2009-06-30"),
           ("Covid crash", "2020-01-01", "2020-03-01", "2020-06-30")),
}
NEWS_TOPICS = (                    # topic hints by keyword, only to help the eye scan a list of headlines
    ("Ownership or policy", re.compile(
        r"\bstakes?\b|\bgovernment|\bgovt\b|\bfederal\b|\bsubsid|\btariffs?\b|\bsanction|\bantitrust|\bregulat"
        r"|\bchips act\b|\bnationali[sz]|\bsovereign\b|\bexport (?:controls?|curbs?|bans?)\b", re.I)),
    ("Deal or partnership", re.compile(
        r"\bacquir|\bacquisition|\bmerger|\bmerges?\b|\bmerged\b|\btakeover|\bbuyout|\bspin-?off|\bdivest"
        r"|\bpartnership|\bpartners with\b|\bjoint venture|\binvests?\b|\binvested\b|\binvestments?\b|\bagreement"
        r"|\bcontract", re.I)),
    ("Legal or risk", re.compile(
        r"\blawsuit|\bsues?\b|\bsued\b|\bprobe\b|\binvestigat|\brecalls?\b|\bfraud|\bbankrupt|\bclass action"
        r"|\bsettle|\bfined?\b|\bfines\b|\bdefault", re.I)),
    ("Financing", re.compile(
        r"\bshare sale|\bstock offering|\bpublic offering|\boffering\b|\bdilut|\bbuybacks?\b|\brepurchase"
        r"|\bconvertible|\bdividend", re.I)),
    ("Earnings or guidance", re.compile(
        r"\bearnings|\bguidance|\boutlook|\bforecast|\bquarterly|\bq[1-4]\b|\b(?:first|second|third|fourth)[- ]quarter"
        r"|\bresults\b|\brevenue", re.I)),
    ("Analyst view", re.compile(r"\bupgrades?\b|\bdowngrades?\b|\bprice targets?\b|\binitiates\b|\banalysts?\b", re.I)),
)

CTX_NOTE = (
    "Information only. Nothing on this tab changes the score, the label or the safety gates. In a three-year "
    "back-test on about 50 large US companies, a sector's recent trend did not reliably predict which stocks did "
    "better, and whether defensive or cyclical sectors led was not the same in every year. The sample was small, so "
    "that is not proof either way. Use this tab as background for your own research, not as a signal."
)
CTX_CHECKLIST = (
    "**Who is behind the news** (a government, a strategic partner, an activist, insiders), and have they paid in "
    "cash, signed a binding commitment, or only said something?",
    "**What price did they pay** compared with today's price? A stake bought at a discount is not available to you at "
    "that price.",
    "**What does the company's own filing or exchange announcement say**, compared with the headline?",
    "**Does it change revenue, margins or cash flow** within about two years, or only sentiment?",
    "**How much has the price already moved** since the news? Put the date in the sidebar to see the move for the "
    "stock, its sector and the market.",
    "**What could go wrong that the news does not cover:** dilution, a guidance cut, a lost customer, a policy reversal?",
    "**Do the pillar scores on the first tab support the story**, or does the story ask you to look past weak numbers?",
    "**How much could you lose if the story is wrong,** and is that an amount you are comfortable with?",
)


@st.cache_data(ttl=CTX_TTL, max_entries=48, show_spinner=False)
def fetch_context_close(symbol: str, period: str) -> list:
    """Daily closes for the context tab, price only (dividends are not added back). Raises, and so is not cached,
    when Yahoo has nothing."""
    return _yahoo_closes(symbol, period)


@st.cache_data(ttl=NEWS_TTL, max_entries=32, show_spinner=False)
def fetch_news(symbol: str) -> list:
    """Raw Yahoo headlines for one ticker. Raises (and so is not cached) when Yahoo cannot be reached."""
    raw = yf.Ticker(symbol).news
    return list(raw) if isinstance(raw, (list, tuple)) else []


def _days_between(a, b):
    """Calendar days from date text a to date text b (negative when b is earlier)."""
    return (datetime.fromisoformat(b) - datetime.fromisoformat(a)).days


def _vs_average(closes, n):
    if len(closes) < n:
        return None
    avg = sum(closes[-n:]) / n
    return closes[-1] / avg - 1 if avg > 0 else None


def window_returns(pts, windows=CTX_WINDOWS):
    """[(date, close)] oldest first -> {label: price return over that many trading days, or None}."""
    closes = [v for _, v in pts or []]
    out = {}
    for label, n in windows:
        base = closes[-1 - n] if len(closes) > n else None
        out[label] = closes[-1] / base - 1 if base is not None and base > 0 else None
    return out


def trend_health(pts):
    """Where the last close sits against its 50- and 200-day averages and its 52-week range. None without data."""
    closes = [v for _, v in pts or []]
    if not closes:
        return None
    year = closes[-252:]
    hi, lo, last = max(year), min(year), closes[-1]
    return {
        "last": last, "as_of": pts[-1][0], "days": len(closes), "full_year": len(closes) >= 252,
        "vs_ma50": _vs_average(closes, 50), "vs_ma200": _vs_average(closes, 200),
        "from_high": last / hi - 1 if hi > 0 else None,
        "range_pos": (last - lo) / (hi - lo) if hi > lo else None,
    }


def ma_state(trend):
    """'above both', 'below both' or 'mixed' for the 50- and 200-day averages; None when either is unknown."""
    if not trend or trend.get("vs_ma50") is None or trend.get("vs_ma200") is None:
        return None
    a, b = trend["vs_ma50"], trend["vs_ma200"]
    return "above both" if a > 0 and b > 0 else "below both" if a < 0 and b < 0 else "mixed"


def span_return(pts, start, end, slack=CTX_SLACK_DAYS):
    """Price return from the first close on or after `start` to the last close on or before `end`. None unless the
    history covers the whole span (a fund or stock that did not exist yet, or a gap in the data)."""
    if not pts or start >= end:
        return None
    if _days_between(start, pts[0][0]) > slack or _days_between(pts[-1][0], end) > slack:
        return None
    seg = [v for d, v in pts if start <= d <= end]
    return seg[-1] / seg[0] - 1 if len(seg) >= 2 and seg[0] > 0 else None


def find_episode(pts, peak_from, peak_to, trough_to, slack=CTX_SLACK_DAYS):
    """The highest close inside [peak_from, peak_to] and the lowest close after it, up to trough_to ->
    (peak date, trough date), or None when the history does not cover the search or has no fall in it."""
    if not pts or _days_between(peak_from, pts[0][0]) > slack or _days_between(pts[-1][0], trough_to) > slack:
        return None
    window = [(d, v) for d, v in pts if peak_from <= d <= peak_to]
    if not window:
        return None
    peak_date, peak_val = max(window, key=lambda t: t[1])
    after = [(d, v) for d, v in pts if peak_date < d <= trough_to]
    if not after:
        return None
    trough_date, trough_val = min(after, key=lambda t: t[1])
    return (peak_date, trough_date) if trough_val < peak_val else None


def since_date(pts, start, slack=CTX_SLACK_DAYS):
    """From the first close on or after `start` to the latest close, with the highest close in between.
    None when the history starts after that date or has no later close."""
    if not pts or _days_between(start, pts[0][0]) > slack:
        return None
    seg = [(d, v) for d, v in pts if d >= start]
    if len(seg) < 2 or seg[0][1] <= 0:
        return None
    first_date, first = seg[0]
    high_date, high = max(seg, key=lambda t: t[1])
    last = seg[-1][1]
    return {"from": first_date, "ret": last / first - 1, "high_date": high_date, "high_ret": high / first - 1,
            "off_high": last / high - 1}


def sector_proxy(m, market, override=""):
    """The fund or index that stands in for this stock's sector -> (symbol or None, label, note)."""
    typed = (override or "").strip().upper()
    if typed:
        return typed, typed, "The comparison fund or index is the symbol you typed."
    sector, industry = str(m.get("sector") or ""), str(m.get("industry") or "").lower()
    if market == "US":
        symbol = dict(CTX_US_BOARD).get(sector)
        if symbol:
            return symbol, f"{sector} ({symbol})", ""
    elif market == "IN":
        symbol, note = CTX_IN_PROXY.get(sector, (None, ""))
        if sector == "Consumer Cyclical" and "auto" in industry:
            symbol, note = "^CNXAUTO", ""
        elif sector == "Financial Services" and "bank" in industry:
            symbol, note = "^NSEBANK", ""
        if symbol:
            label = next((name for name, sym in CTX_IN_BOARD if sym == symbol), symbol)
            return symbol, f"{label} ({symbol})", note
    return None, "", (f"No sector fund or index is mapped to '{sector or 'unknown'}'"
                      + (f" ({m.get('industry')})" if m.get("industry") else "")
                      + ". Type a symbol in the sidebar to compare against one.")


def _news_date(value):
    try:
        if isinstance(value, (int, float)) and not isinstance(value, bool):
            return datetime.fromtimestamp(value, timezone.utc).strftime("%Y-%m-%d")
        if isinstance(value, str) and value.strip():
            return datetime.fromisoformat(value.strip().replace("Z", "+00:00")).strftime("%Y-%m-%d")
    except (ValueError, OverflowError, OSError):
        pass
    return ""


def _clean_url(url):
    """Only http(s) links, with the characters that could break a markdown link or start LaTeX encoded."""
    url = str(url or "").strip()
    if not url.lower().startswith(("http://", "https://")):
        return ""
    for ch, code in ((" ", "%20"), ("(", "%28"), (")", "%29"), ("[", "%5B"), ("]", "%5D"), ("$", "%24")):
        url = url.replace(ch, code)
    return url


def tag_headline(title):
    """Up to two topic hints for a headline, by keyword. They help the eye scan a list; they are not a reading of
    the news."""
    return [name for name, pattern in NEWS_TOPICS if pattern.search(title or "")][:2]


def parse_news(raw, limit=NEWS_LIMIT):
    """Yahoo headlines, in either the older flat shape or the newer {"content": {...}} shape ->
    [{"title", "publisher", "date", "url", "tags"}], newest first. Anything unreadable is skipped."""
    out, seen = [], set()
    for item in raw or []:
        if not isinstance(item, dict):
            continue
        c = item["content"] if isinstance(item.get("content"), dict) else item
        title = " ".join(str(c.get("title") or "").split())
        if not title or title.lower() in seen:
            continue
        seen.add(title.lower())
        provider = c.get("provider")
        publisher = provider.get("displayName") if isinstance(provider, dict) else c.get("publisher")
        link = ""
        for key in ("canonicalUrl", "clickThroughUrl"):
            v = c.get(key)
            link = link or (v.get("url") if isinstance(v, dict) else "")
        out.append({
            "title": title, "publisher": str(publisher or "").strip(),
            "date": _news_date(c.get("pubDate") or c.get("displayTime") or c.get("providerPublishTime")),
            "url": _clean_url(link or c.get("link")), "tags": tag_headline(title),
        })
    out.sort(key=lambda r: r["date"], reverse=True)       # stable: undated items keep Yahoo's order, after the dated
    return out[:limit]


def ctx_info(snap):
    """Ownership and positioning figures from the Yahoo snapshot (None where Yahoo has none). Fractions, not percent."""
    info = snap.get("info") or {}
    return {
        "insiders": first_num(info, "heldPercentInsiders"), "institutions": first_num(info, "heldPercentInstitutions"),
        "short_float": first_num(info, "shortPercentOfFloat"), "short_days": first_num(info, "shortRatio"),
        "analyst_mean": first_num(info, "recommendationMean"), "analyst_n": first_num(info, "numberOfAnalystOpinions"),
        "target": first_num(info, "targetMeanPrice"),
    }


def _describe(symbol, label, pts):
    if not pts:
        return None
    return {"symbol": symbol, "label": label, "ret": window_returns(pts), "trend": trend_health(pts),
            "as_of": pts[-1][0]}


def _gaps(a, b):
    """{window label: a's return minus b's}, with None where either is missing. Empty when a series is missing."""
    if not a or not b:
        return {}
    return {lab: (None if a["ret"][lab] is None or b["ret"][lab] is None else a["ret"][lab] - b["ret"][lab])
            for lab, _ in CTX_WINDOWS}


def collect_context(m, cfg, get_mkt=None, get_news=None):
    """Everything the context tab shows. Each fetch is separate, so a failure leaves a gap and a line in "errors"
    and never raises. Information only: nothing here feeds a pillar, a gate or the label."""
    get_mkt = get_mkt or fetch_context_close
    get_news = get_news or fetch_news
    errors, notes, memo = [], [], {}

    def series(symbol):
        if symbol not in memo:
            try:
                memo[symbol] = get_mkt(symbol, "max")
            except Exception as exc:  # noqa: BLE001 - one missing series must not hide the others
                errors.append(f"{symbol}: {type(exc).__name__}")
                memo[symbol] = None
        return memo[symbol]

    ticker = str(m.get("ticker") or "")
    market = market_for(m)
    out = {"ticker": ticker, "market": market, "proxy": None, "stock": None, "sector": None, "bench": None, "gaps": {},
           "episodes": [], "board": [], "tape": None, "since": None, "news": None, "info": m.get("ctx_info"),
           "notes": notes, "errors": errors,
           "fetched_at": datetime.now(timezone.utc).strftime("%d %b %Y %H:%M UTC")}

    s_pts = series(ticker) if ticker else None
    out["stock"] = _describe(ticker, f"{m.get('name') or ticker} ({ticker})", s_pts)
    b_pts = p_pts = None
    if market is None:
        notes.append(f"Sector and market comparisons cover US-dollar and Indian-rupee stocks. This one trades in "
                     f"{m.get('currency') or 'an unknown currency'}, so only its own trend, headlines and ownership "
                     "are shown.")
    else:
        bench_symbol, bench_label = CTX_BENCH[market]
        b_pts = series(bench_symbol)
        out["bench"] = _describe(bench_symbol, bench_label, b_pts)
        proxy, proxy_label, note = sector_proxy(m, market, cfg.get("ctx_proxy", ""))
        if note:
            notes.append(note)
        p_pts = series(proxy) if proxy else None
        out["proxy"] = proxy
        out["sector"] = _describe(proxy, proxy_label, p_pts) if proxy else None
        out["gaps"] = {"sector_vs_market": _gaps(out["sector"], out["bench"]),
                       "stock_vs_sector": _gaps(out["stock"], out["sector"]),
                       "stock_vs_market": _gaps(out["stock"], out["bench"])}

        for name, peak_from, peak_to, trough_to in CTX_EPISODES.get(market, ()):
            span = find_episode(b_pts, peak_from, peak_to, trough_to)
            if span is None:
                continue
            row = {"name": name, "start": span[0], "end": span[1], "market": span_return(b_pts, *span),
                   "sector": span_return(p_pts, *span), "stock": span_return(s_pts, *span)}
            row["sector_vs_market"] = (None if row["sector"] is None or row["market"] is None
                                       else row["sector"] - row["market"])
            out["episodes"].append(row)

        if cfg.get("ctx_board", True):
            bench_ret = (out["bench"] or {}).get("ret") or {}
            rows = []
            for label, symbol in (CTX_US_BOARD if market == "US" else CTX_IN_BOARD):
                pts = series(symbol)
                ret = window_returns(pts) if pts else {lab: None for lab, _ in CTX_WINDOWS}
                rel = {lab: (None if ret[lab] is None or bench_ret.get(lab) is None else ret[lab] - bench_ret[lab])
                       for lab, _ in CTX_WINDOWS}
                rows.append({"label": label, "symbol": symbol, "ret": ret, "rel": rel, "is_this": symbol == proxy})
            out["board"] = sorted(rows, key=lambda r: (r["rel"]["3M"] is None, -(r["rel"]["3M"] or 0.0)))
            groups = {}
            for key, symbols in CTX_TAPE[market].items():
                members = [(sym, window_returns(memo[sym])) for sym in symbols if memo.get(sym)]
                avg = {}
                for lab, _ in CTX_WINDOWS:
                    vals = [r[lab] for _, r in members if r[lab] is not None]
                    avg[lab] = sum(vals) / len(vals) if vals else None
                groups[key] = {"avg": avg, "used": len(members), "of": len(symbols)}
            groups["diff"] = {lab: (None if groups["defensive"]["avg"][lab] is None or groups["cyclical"]["avg"][lab] is None
                                    else groups["defensive"]["avg"][lab] - groups["cyclical"]["avg"][lab])
                              for lab, _ in CTX_WINDOWS}
            out["tape"] = groups

    typed_day = str(cfg.get("ctx_date") or "").strip()
    if typed_day:
        try:
            day = datetime.strptime(typed_day, "%Y-%m-%d").date().isoformat()     # '2026-1-1' becomes '2026-01-01'
        except ValueError:
            notes.append(f"Could not read the catalyst date '{typed_day}'. Use the form YYYY-MM-DD, for example "
                         "2025-08-22.")
        else:
            since = {"date": day, "stock": since_date(s_pts, day), "sector": since_date(p_pts, day),
                     "bench": since_date(b_pts, day)}
            if since["stock"] is None:
                notes.append(f"Not enough price history to measure from {day}: the stock's history has to start by "
                             "then and include at least one later close.")
            else:
                out["since"] = since

    ends = [d["as_of"] for d in (out["stock"], out["sector"], out["bench"]) if d]
    if len(ends) > 1 and _days_between(min(ends), max(ends)) > 5:
        notes.append("The price series end on different dates (see the As of column), so comparisons between them "
                     "are approximate.")

    try:
        out["news"] = parse_news(get_news(ticker)) if ticker else None
    except Exception as exc:  # noqa: BLE001 - headlines are an extra
        errors.append(f"headlines: {type(exc).__name__}")
    return out


def ctx_glance(ctx):
    """A few plain sentences that restate the numbers on the tab. Descriptive: no verdict, no signal."""
    lines = []

    def ahead(gaps, subject, other):
        known = [(lab, v) for lab, v in (gaps or {}).items() if v is not None]
        if known:
            won = [lab for lab, v in known if v > 0]
            lines.append(f"{subject} is ahead of {other} over {len(won)} of {len(known)} periods"
                         + (f" ({', '.join(won)})." if won else "."))

    def state(subject, trend):
        s = ma_state(trend)
        if s == "mixed":
            lines.append(f"{subject} is above one of its 50-day and 200-day averages and below the other.")
        elif s:
            lines.append(f"{subject} is {s} its 50-day and 200-day averages.")

    g = ctx.get("gaps") or {}
    ahead(g.get("sector_vs_market"), "The sector", "the market")
    ahead(g.get("stock_vs_sector"), "The stock", "its sector")
    state("The sector", (ctx.get("sector") or {}).get("trend"))
    state("The stock", (ctx.get("stock") or {}).get("trend"))
    t = (ctx.get("stock") or {}).get("trend")
    if t and t.get("from_high") is not None:
        lines.append(f"The stock is {abs(t['from_high']) * 100:.1f}% below its 52-week high."
                     if t["from_high"] < -0.0005 else "The stock is at its 52-week high.")
    return lines


# ══════════════════════════════════════════════════════════════════════════════
# 3d. CAPITAL ALLOCATION AND COMPANY FILINGS  (version 2.2, optional: information only, never part of a score or a label)
# ══════════════════════════════════════════════════════════════════════════════
ALLOC_YEARS = 4                    # annual periods shown, newest first
ALLOC_GAP_DAYS = (300, 430)        # two period ends count as consecutive years when this many days apart
ALLOC_SPLIT_JUMP = 0.35            # a share count that moves more than this in a year is read as a split (as in pillar 4.2)
ALLOC_ROWS = (                     # key, label, how the figure is shown
    ("asset_growth", "Total assets: change on the year before", "chg"),
    ("capex_to_da", "Capital spending ÷ depreciation and amortisation", "x"),
    ("capex_to_ocf", "Capital spending ÷ operating cash flow", "pct"),
    ("acq_to_ocf", "Cash paid for acquisitions ÷ operating cash flow", "pct"),
    ("goodwill_share", "Goodwill ÷ total assets", "pct"),
    ("debt_change", "Total debt: change on the year before", "chg"),
    ("share_change", "Shares outstanding: change on the year before", "chg"),
    ("stock_to_ocf", "Cash raised by issuing shares ÷ operating cash flow", "pct"),
)
ALLOC_HELP = (
    "**Total assets, change:** this year's total assets against last year's. A large rise usually means the company "
    "has expanded, bought something or raised money.",
    "**Capital spending ÷ depreciation and amortisation:** above 1x means the company is spending more on equipment "
    "and buildings than it is writing off each year, which is what expansion looks like in the accounts.",
    "**Capital spending ÷ operating cash flow:** the share of the cash the business generates that goes back into it.",
    "**Cash paid for acquisitions ÷ operating cash flow:** cash deals only. A deal paid for in shares never shows up "
    "in cash flow; it shows up in goodwill, total assets and the share count instead.",
    "**Goodwill ÷ total assets:** goodwill is what was paid for acquired businesses above the value of their assets. "
    "It can be written down later if a deal disappoints (the 8-K item for that is 2.06, material impairments).",
    "**Total debt and shares outstanding, change; cash raised by issuing shares:** how the growth was paid for. The "
    "share-issuing figure includes shares issued to employees. A share count that moves more than 35% in a year is "
    "read as a stock split and left out.",
)
ALLOC_RESEARCH = (
    "Why these figures are shown and not scored: studies of US companies found that, on average, firms that sharply "
    "raised capital spending or grew their assets quickly went on to earn weaker returns (Titman, Wei and Xie, 2004; "
    "Cooper, Gulen and Schill, 2008, a result a later critique questions), and that acquirers paying in shares "
    "lagged while cash tender offers did better (Loughran and Vijh, 1997). Those are averages from older samples, "
    "published patterns have tended to weaken once they became known (McLean and Pontiff, 2016), and none of it says "
    "anything about this particular company."
)


def _iso_day(d):
    """A statement's period-end label as 'YYYY-MM-DD', or '' when it is not a date."""
    try:
        return pd.Timestamp(d).strftime("%Y-%m-%d")
    except Exception:  # noqa: BLE001 - an unreadable column label is simply left out
        return ""


def _by_day(df, *labels):
    """{period end: value} for the first statement row found, dropping any column that is not a date."""
    out = {}
    for d, v in stmt_series(df, *labels):
        day = _iso_day(d)
        if day:
            out[day] = v
    return out


def _year_before(days, d):
    """The period end about a year before d, or None. A missing year is never bridged, so a gap gives no figure."""
    earlier = [x for x in days if x < d]
    if not earlier:
        return None
    p = max(earlier)
    return p if ALLOC_GAP_DAYS[0] <= _days_between(p, d) <= ALLOC_GAP_DAYS[1] else None


def _change(series, d):
    """Change from the year before to d as a fraction, for positive values only (None otherwise)."""
    if d not in series:
        return None
    p = _year_before(sorted(series), d)
    if p is None:
        return None
    a, b = series[p], series[d]
    return b / a - 1 if a > 0 and b > 0 else None


def _ratio(top, bottom, d):
    a, b = top.get(d), bottom.get(d)
    return a / b if a is not None and b is not None and b > 0 else None


def capital_allocation(snap):
    """Capital-allocation figures from the annual statements already in the snapshot, newest year first. Information
    only. Every figure is None where the statements do not give it; nothing is estimated."""
    bal, cf, inc = snap.get("balance"), snap.get("cashflow"), snap.get("income")
    assets, goodwill, debt = _by_day(bal, "Total Assets"), _by_day(bal, "Goodwill"), _by_day(bal, "Total Debt")
    shares = _by_day(bal, "Ordinary Shares Number", "Share Issued")
    ocf = _by_day(cf, "Operating Cash Flow", "Cash Flow From Continuing Operating Activities")
    capex = {d: abs(v) for d, v in _by_day(cf, "Capital Expenditure").items()}
    da = (_by_day(cf, "Depreciation And Amortization", "Depreciation Amortization Depletion")
          or _by_day(inc, "Reconciled Depreciation"))
    issued = {d: v for d, v in _by_day(cf, "Issuance Of Capital Stock", "Common Stock Issuance").items() if v >= 0}
    bought = _by_day(cf, "Purchase Of Business")
    net_only = False
    if bought:
        acq = {d: abs(v) for d, v in bought.items()}
    else:                          # fall back to the net line: only a year with a net purchase gives a known amount
        net = _by_day(cf, "Net Business Purchase And Sale")
        acq = {d: abs(v) for d, v in net.items() if v <= 0}
        net_only = bool(net)

    pool = sorted(set(assets) | set(goodwill) | set(debt) | set(shares) | set(ocf) | set(capex) | set(da) | set(acq))
    dates = pool[-ALLOC_YEARS:][::-1]
    values = {key: {} for key, _, _ in ALLOC_ROWS}
    split_seen = False
    for d in dates:
        values["asset_growth"][d] = _change(assets, d)
        values["capex_to_da"][d] = _ratio(capex, da, d)
        values["capex_to_ocf"][d] = _ratio(capex, ocf, d)
        values["acq_to_ocf"][d] = _ratio(acq, ocf, d)
        values["goodwill_share"][d] = _ratio(goodwill, assets, d)
        values["debt_change"][d] = _change(debt, d)
        move = _change(shares, d)
        if move is not None and abs(move) > ALLOC_SPLIT_JUMP:
            move, split_seen = None, True
        values["share_change"][d] = move
        values["stock_to_ocf"][d] = _ratio(issued, ocf, d)

    acq3 = None                    # cash paid for acquisitions over the latest three consecutive years
    last3 = dates[:3]
    if (len(last3) == 3 and all(d in acq and d in ocf for d in last3)
            and all(_year_before(pool, last3[i]) == last3[i + 1] for i in range(2))):
        cash = sum(ocf[d] for d in last3)
        if cash > 0:
            acq3 = {"years": 3, "ratio": sum(acq[d] for d in last3) / cash}

    notes = []
    if not dates:
        notes.append("Yahoo returned no annual statements for this company, so none of these figures can be worked out.")
    else:
        if not acq:
            notes.append("Yahoo has no acquisitions line for this company, so cash paid for acquisitions is not shown. A "
                         "deal paid for in shares never appears there: look at goodwill and the share count.")
        elif net_only:
            notes.append("Only a net figure for business purchases and sales was available, so a year with a net sale "
                         "shows n/a.")
        if any(d in ocf and ocf[d] <= 0 for d in dates):
            notes.append("In a year when operating cash flow was zero or negative, the figures that divide by it show n/a.")
        if split_seen:
            notes.append("A share count that moved by more than 35% in one year was read as a stock split and left out.")
        if not goodwill:
            notes.append("n/a for goodwill means Yahoo shows no goodwill line, which can simply mean the company has none.")
    out = {"dates": dates, "values": values, "acq3": acq3, "notes": notes}
    out["glance"] = alloc_glance(out)
    return out


def alloc_glance(a):
    """A few plain sentences that restate the figures. Descriptive: no verdict, no signal."""
    lines, dates, vals = [], a.get("dates") or [], a.get("values") or {}
    if not dates:
        return lines
    d0 = dates[0]
    growth = vals["asset_growth"].get(d0)
    if growth is not None:
        lines.append(f"Total assets {'grew' if growth >= 0 else 'shrank'} {abs(growth) * 100:.1f}% in the year to {d0}.")
    spend = vals["capex_to_da"].get(d0)
    if spend is not None:
        lines.append(f"Capital spending was {spend:.1f} times depreciation and amortisation in the year to {d0}.")
    if a.get("acq3"):
        lines.append(f"Cash paid for acquisitions over the last {a['acq3']['years']} years came to "
                     f"{a['acq3']['ratio'] * 100:.0f}% of operating cash flow over the same years.")
    share = vals["goodwill_share"].get(d0)
    if share is not None:
        before = vals["goodwill_share"].get(dates[1]) if len(dates) > 1 else None
        lines.append(f"Goodwill is {share * 100:.0f}% of total assets"
                     + (f" (against {before * 100:.0f}% a year earlier)." if before is not None else "."))
    move = vals["share_change"].get(d0)
    if move is not None:
        pct = round(move * 100, 1)
        lines.append("The share count was unchanged to one decimal place in the year to " + d0 + "." if pct == 0 else
                     f"The share count {'rose' if pct > 0 else 'fell'} {abs(pct):.1f}% in the year to {d0}.")
    return lines


# ---- company filings (SEC EDGAR) ------------------------------------------------------------------------------
SEC_AGENT = "AntiFragileStockScreener"
SEC_TIMEOUT = 20                   # seconds to wait for the SEC before giving up
SEC_PAUSE = 0.12                   # seconds between live requests (the SEC allows far more; this is only politeness)
SEC_JSON_LIMIT = 15_000_000        # bytes: refuse an answer bigger than this
SEC_TEXT_LIMIT = 3_000_000
SEC_TEXT_CHARS = 400_000           # how much of a filing is read when its item codes are taken from the text
SEC_TICKERS_TTL = 24 * 60 * 60
SEC_FILINGS_TTL = 60 * 60
SEC_TEXT_TTL = 24 * 60 * 60
SEC_TICKERS_URL = "https://www.sec.gov/files/company_tickers.json"
SEC_SUBMISSIONS_URL = "https://data.sec.gov/submissions/CIK{cik:010d}.json"
SEC_ARCHIVE_URL = "https://www.sec.gov/Archives/edgar/data/{cik}/{acc}/{doc}"
SEC_BROWSE_URL = "https://www.sec.gov/cgi-bin/browse-edgar?action=getcompany&CIK={cik:010d}&type=8-K&dateb=&owner=include&count=40"
FILING_FORMS = ("8-K", "8-K/A", "6-K")
FILINGS_WINDOW_DAYS = 365          # the list starts this far back, or at the catalyst date if that is earlier
FILINGS_MAX_WINDOW_DAYS = 1100
FILINGS_LIST_ROWS = 40
FILINGS_TEXT_READS = 10            # filings whose text is opened to find item codes the SEC's list did not give
FILINGS_SHOWN_FIRST = 12

# Item names follow the headings of Form 8-K (checked against the Wikipedia list of items). A code that is not in this
# table is shown as "not described in this app".
FILING_ITEMS = {
    "1.01": ("Entry into a material definitive agreement", "Deals and agreements"),
    "1.02": ("Termination of a material definitive agreement", "Deals and agreements"),
    "1.03": ("Bankruptcy or receivership", "Distress and listing"),
    "2.01": ("Completion of an acquisition or disposition of assets", "Deals and agreements"),
    "2.02": ("Results of operations and financial condition", "Results"),
    "2.03": ("Creation of a direct financial obligation or an off-balance-sheet obligation", "Financing"),
    "2.04": ("Triggering events that accelerate or increase a financial obligation", "Distress and listing"),
    "2.05": ("Costs associated with exit or disposal activities", "Restructuring and write-downs"),
    "2.06": ("Material impairments", "Restructuring and write-downs"),
    "3.01": ("Notice of delisting or failure to meet a listing rule; transfer of listing", "Distress and listing"),
    "3.02": ("Unregistered sales of equity securities", "Financing"),
    "3.03": ("Material modification to the rights of security holders", "Financing"),
    "4.01": ("Change in the company's certifying accountant", "Accounting and audit"),
    "4.02": ("Non-reliance on previously issued financial statements", "Accounting and audit"),
    "5.01": ("Change in control of the company", "Control and people"),
    "5.02": ("Departure or appointment of directors or certain officers", "Control and people"),
    "5.03": ("Amendments to articles or bylaws; change in fiscal year", "Control and people"),
    "7.01": ("Regulation FD disclosure", "Announcements and other"),
    "8.01": ("Other events", "Announcements and other"),
    "9.01": ("Financial statements and exhibits", "Exhibits"),
}
FILING_READ_FIRST = ("1.03", "2.04", "2.06", "3.01", "4.01", "4.02")     # the app's own shortlist, not a verdict
_ITEM_CODE = re.compile(r"\b[1-9]\.[0-9]{2}\b")
_ITEM_HEADING = re.compile(r"(?im)^[ \t]*item[ \t]+([1-9]\.[0-9]{2})\b")


def plain(text):
    """Text that came from outside the app (a company name), made safe to show in markdown."""
    text = re.sub(r"(?i)\b(?:https?|ftp)://\S*|\bwww\.\S*", " ", str(text or ""))
    return " ".join(re.sub(r"[\\`*_{}\[\]()<>#+!|~$@]", " ", text).split())


def _clean_day(text):
    """'2026-1-5' -> '2026-01-05'; None when it is not a date."""
    try:
        return datetime.strptime(str(text).strip(), "%Y-%m-%d").strftime("%Y-%m-%d")
    except ValueError:
        return None


def _add_days(day, n):
    return (datetime.strptime(day, "%Y-%m-%d") + timedelta(days=n)).strftime("%Y-%m-%d")


def valid_contact(text):
    """A plain email address: the SEC wants a way to reach whoever is sending automated requests."""
    return bool(re.fullmatch(r"[A-Za-z0-9._%+\-]{1,64}@[A-Za-z0-9.\-]{1,200}\.[A-Za-z]{2,24}", text or ""))


def sec_contact(cfg):
    """The contact email typed in the sidebar, else SEC_CONTACT from the app's secrets, else ''."""
    typed = str(cfg.get("sec_contact") or "").strip()
    if typed:
        return typed
    try:
        return str(st.secrets.get("SEC_CONTACT", "") or "").strip()
    except Exception:  # noqa: BLE001 - no secrets file is the normal case
        return ""


def _sec_error(exc):
    code = getattr(exc, "code", None)
    return type(exc).__name__ + (f" (HTTP {code})" if isinstance(code, int) and not isinstance(code, bool) else "")


def _sec_get(url, contact, limit):
    """One polite request to the SEC. The SEC asks automated requests to say who is sending them."""
    if not url.startswith(("https://www.sec.gov/", "https://data.sec.gov/")):
        raise ValueError("not an SEC address")
    request = urllib.request.Request(url, headers={"User-Agent": f"{SEC_AGENT} {contact}", "Accept-Encoding": "identity"})
    time.sleep(SEC_PAUSE)
    with urllib.request.urlopen(request, timeout=SEC_TIMEOUT) as response:
        body = response.read(limit + 1)
    if len(body) > limit:
        raise DataError("The SEC sent more data than expected.")
    return body


@st.cache_data(ttl=SEC_TICKERS_TTL, max_entries=2, show_spinner=False)
def fetch_sec_tickers(_contact: str) -> dict:
    """The SEC's list of tickers and company numbers. Raises (and so is not cached) when the SEC cannot be reached."""
    return json.loads(_sec_get(SEC_TICKERS_URL, _contact, SEC_JSON_LIMIT).decode("utf-8"))


@st.cache_data(ttl=SEC_FILINGS_TTL, max_entries=32, show_spinner=False)
def fetch_sec_submissions(cik: int, _contact: str) -> dict:
    """One company's filing list from the SEC. Raises (and so is not cached) on any problem."""
    return json.loads(_sec_get(SEC_SUBMISSIONS_URL.format(cik=int(cik)), _contact, SEC_JSON_LIMIT).decode("utf-8"))


@st.cache_data(ttl=SEC_TEXT_TTL, max_entries=64, show_spinner=False)
def fetch_sec_text(url: str, _contact: str) -> str:
    """The text of one filing document. Only addresses under the SEC's filing archive are accepted."""
    if not url.startswith("https://www.sec.gov/Archives/edgar/data/"):
        raise ValueError("not a filing address")
    return _sec_get(url, _contact, SEC_TEXT_LIMIT).decode("utf-8", errors="replace")


def sec_find_company(table, ticker):
    """(company number, name) for a ticker in the SEC's company list, or None. Class-share tickers are tried both as
    BRK.B and as BRK-B."""
    rows = table.values() if isinstance(table, dict) else table if isinstance(table, list) else ()
    exact = str(ticker or "").strip().upper()
    found = {}
    for r in rows:
        if not isinstance(r, dict):
            continue
        t = str(r.get("ticker") or "").strip().upper()
        raw = r.get("cik_str", r.get("cik"))
        if not t or isinstance(raw, bool):
            continue
        try:
            cik = int(raw)
        except (TypeError, ValueError, OverflowError):
            continue
        if cik > 0 and t not in found:
            found[t] = (cik, plain(r.get("title"))[:80])
    return found.get(exact) or found.get(exact.replace(".", "-"))


def parse_item_codes(value):
    """'2.02,9.01' (or a list of such text) -> ['2.02', '9.01'], each code once, in the order given."""
    text = " ".join(str(x) for x in value) if isinstance(value, (list, tuple)) else str(value or "")
    out = []
    for code in _ITEM_CODE.findall(text):
        if code not in out:
            out.append(code)
    return out


def filing_url(cik, accession, doc):
    """Link to a filing document, built only from checked pieces (None when any piece looks wrong)."""
    if not (isinstance(accession, str) and re.fullmatch(r"[0-9]{10}-[0-9]{2}-[0-9]{6}", accession)):
        return None
    if not (isinstance(doc, str) and re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.\-]{0,120}", doc)):
        return None
    return SEC_ARCHIVE_URL.format(cik=int(cik), acc=accession.replace("-", ""), doc=doc)


def sec_filing_rows(raw, cik=None):
    """The SEC's filing list for one company -> (event filings newest first, earliest filing date of any kind, name).
    An event filing is a Form 8-K, 8-K/A or 6-K. Item codes come from the list when it gives them (items is None when
    it does not). Anything unreadable is skipped, never raised."""
    if not isinstance(raw, dict):
        return [], None, ""
    name = plain(raw.get("name"))[:80]
    filings = raw.get("filings")
    recent = filings.get("recent") if isinstance(filings, dict) else None
    if not isinstance(recent, dict):
        return [], None, name
    forms, days = recent.get("form"), recent.get("filingDate")
    if not isinstance(forms, list) or not isinstance(days, list):
        return [], None, name
    n = min(len(forms), len(days))

    def column(key):
        col = recent.get(key)
        return col if isinstance(col, list) and len(col) >= n else None

    items_col, acc_col, doc_col = column("items"), column("accessionNumber"), column("primaryDocument")
    rows, earliest = [], None
    for i in range(n):
        day = _clean_day(days[i])
        if day is None:
            continue
        if earliest is None or day < earliest:
            earliest = day
        form = str(forms[i] or "").strip().upper()
        if form not in FILING_FORMS:
            continue
        codes = parse_item_codes(items_col[i]) if items_col is not None and form.startswith("8-K") else []
        rows.append({
            "date": day, "form": form, "items": (codes or None) if form.startswith("8-K") else [],
            "items_from": "feed" if codes else None,
            "url": filing_url(cik, acc_col[i] if acc_col is not None else None, doc_col[i] if doc_col is not None else None)
            if cik else None,
        })
    rows.sort(key=lambda r: r["date"], reverse=True)         # stable: filings on one day keep the SEC's order
    return rows, earliest, name


def items_from_text(document):
    """Item codes read from the text of an 8-K, taken from lines that start with 'Item x.xx' (a best-effort reading)."""
    text = str(document or "")[:SEC_TEXT_CHARS]
    text = re.sub(r"(?i)<\s*(?:br|/p|/div|/tr|/li|/h[1-6]|/table)\b[^<>]{0,200}>", "\n", text)
    text = re.sub(r"<[^<>]{0,2000}>", " ", text)
    text = html_lib.unescape(text).replace("\xa0", " ")
    out = []
    for code in _ITEM_HEADING.findall(text):
        if code not in out:
            out.append(code)
    return out


def collect_filings(m, cfg, get_tickers=None, get_submissions=None, get_text=None, today=None):
    """Recent SEC event filings for a US-listed company. Information only. Never raises: each fetch is separate, and a
    failure becomes a status or a line in "errors". Nothing is fetched until a contact email has been given."""
    now = datetime.now(timezone.utc)
    ticker = str(m.get("ticker") or "").strip().upper()
    out = {"status": "ok", "ticker": ticker, "cik": None, "name": "", "rows": [], "counts": [], "forms": {},
           "window_start": None, "coverage_start": None, "short_coverage": False, "catalyst": None, "browse_url": None,
           "text_read": 0, "text_unread": 0, "n_window": 0, "n_after": 0, "notes": [], "errors": [],
           "fetched_at": now.strftime("%d %b %Y %H:%M UTC")}
    errors = out["errors"]
    if not ticker or market_for(m) != "US":
        out["status"] = "not_us"
        return out
    contact = sec_contact(cfg)
    if not contact:
        out["status"] = "needs_contact"
        return out
    if not valid_contact(contact):
        out["status"] = "bad_contact"
        return out
    get_tickers = get_tickers or (lambda: fetch_sec_tickers(contact))
    get_submissions = get_submissions or (lambda cik: fetch_sec_submissions(cik, contact))
    get_text = get_text or (lambda url: fetch_sec_text(url, contact))

    try:
        found = sec_find_company(get_tickers(), ticker)
    except Exception as exc:  # noqa: BLE001 - the SEC being down must not touch the rest of the tab
        errors.append(f"SEC company list: {_sec_error(exc)}")
        out["status"] = "error"
        return out
    if found is None:
        out["status"] = "not_found"
        return out
    cik, title = found
    out["cik"], out["name"], out["browse_url"] = cik, title, SEC_BROWSE_URL.format(cik=cik)
    try:
        raw = get_submissions(cik)
    except Exception as exc:  # noqa: BLE001
        errors.append(f"SEC filing list: {_sec_error(exc)}")
        out["status"] = "error"
        return out
    rows, earliest, name = sec_filing_rows(raw, cik)
    if name and not out["name"]:
        out["name"] = name

    today_iso = _clean_day(today) if today else None
    today_iso = today_iso or now.strftime("%Y-%m-%d")
    start = _add_days(today_iso, -FILINGS_WINDOW_DAYS)
    catalyst = _clean_day(cfg.get("ctx_date")) if str(cfg.get("ctx_date") or "").strip() else None
    if catalyst:
        out["catalyst"] = catalyst
        if catalyst < start:
            start = max(catalyst, _add_days(today_iso, -FILINGS_MAX_WINDOW_DAYS))
    window = [r for r in rows if r["date"] >= start]
    out["window_start"], out["coverage_start"] = start, earliest
    out["short_coverage"] = earliest is not None and earliest > start

    reads, failed, last_exc = 0, 0, None
    for r in window:                                         # item codes the SEC's list did not give: read the filing
        if r["form"].startswith("8-K") and r["items"] is None:
            if not r["url"] or reads >= FILINGS_TEXT_READS:
                out["text_unread"] += 1
                continue
            reads += 1
            try:
                codes = items_from_text(get_text(r["url"]))
            except Exception as exc:  # noqa: BLE001
                failed, last_exc = failed + 1, exc
                out["text_unread"] += 1
                continue
            if codes:
                r["items"], r["items_from"] = codes, "text"
                out["text_read"] += 1
            else:
                out["text_unread"] += 1
    if failed:
        errors.append(f"SEC filing text: {_sec_error(last_exc)} ({failed} filing{'s' if failed != 1 else ''})")

    counts, forms = {}, {}
    for r in window:
        forms[r["form"]] = forms.get(r["form"], 0) + 1
        if r["form"] == "8-K":                               # an amendment repeats an earlier event, so it is not counted
            for code in r["items"] or ():
                if code != "9.01":
                    c = counts.setdefault(code, {"code": code, "n": 0, "latest": r["date"]})
                    c["n"] += 1
                    c["latest"] = max(c["latest"], r["date"])
    out["counts"] = sorted(counts.values(), key=lambda c: (-c["n"], c["code"]))
    out["forms"] = forms
    out["rows"] = [{**r, "after": bool(catalyst and r["date"] >= catalyst)} for r in window[:FILINGS_LIST_ROWS]]
    out["n_window"] = len(window)
    out["n_after"] = sum(1 for r in window if catalyst and r["date"] >= catalyst)
    return out


def filings_glance(fl):
    """A few plain sentences that restate the list. Descriptive: no verdict, no signal."""
    lines = []
    if fl.get("status") != "ok":
        return lines
    start, forms = fl["window_start"], fl.get("forms") or {}
    n8, n6, na = forms.get("8-K", 0), forms.get("6-K", 0), forms.get("8-K/A", 0)
    if n8:
        lines.append(f"{n8} Form 8-K report{'s' if n8 != 1 else ''} filed since {start}"
                     + (f", plus {na} amendment{'s' if na != 1 else ''}." if na else "."))
    elif na:
        lines.append(f"{na} Form 8-K amendment{'s' if na != 1 else ''} filed since {start}.")
    if n6:
        lines.append(f"{n6} Form 6-K report{'s' if n6 != 1 else ''} filed since {start}. Foreign companies file these "
                     "instead of 8-Ks, and they carry no item codes.")
    top = [c for c in fl["counts"] if c["code"] != "2.02" and c["n"] >= 2][:3]      # results come every quarter: left out
    if top:
        lines.append("Item types that came up more than once: " + "; ".join(
            f"{c['code']} {FILING_ITEMS.get(c['code'], ('not described here',))[0].lower()} ({c['n']})" for c in top) + ".")
    first = [c for c in fl["counts"] if c["code"] in FILING_READ_FIRST]
    if first:
        lines.append("Item types on the app's read-first list that were filed in this period: " + "; ".join(
            f"{c['code']} {FILING_ITEMS[c['code']][0].lower()} (latest {c['latest']})" for c in first) + ".")
    if fl.get("catalyst"):
        n = fl.get("n_after") or 0
        lines.append(f"{n} filing{'s' if n != 1 else ''} listed since your date ({fl['catalyst']})." if n
                     else f"No filings are listed since your date ({fl['catalyst']}).")
    return lines


# ══════════════════════════════════════════════════════════════════════════════
# 4. SCORING MODEL (shared by both lenses)
# ══════════════════════════════════════════════════════════════════════════════
@dataclass
class Pillar:
    ref: str
    group: str
    name: str
    weight: float             # percent; only relative weights matter
    value: Optional[float]    # raw metric, None = unavailable
    display: str              # formatted metric, "n/a" when unavailable
    score: Optional[int]      # 1 (poor) .. 5 (excellent); None = left out of the score
    note: str = ""


def tier(value, cuts, higher=True):
    """Map a metric to 5..1 using four cut-offs ordered from best to worst. None stays None."""
    if value is None:
        return None
    for score, cut in zip((5, 4, 3, 2), cuts):
        if (value >= cut) if higher else (value <= cut):
            return score
    return 1


def summarize(pillars):
    """Weighted composite over pillars that have data -> (score, coverage, group_scores)."""
    total_w = sum(p.weight for p in pillars)
    have = [p for p in pillars if p.score is not None]
    w_have = sum(p.weight for p in have)
    coverage = w_have / total_w if total_w else 0.0
    score = sum(p.weight * p.score for p in have) / w_have if w_have else None
    groups = {}
    for g in dict.fromkeys(p.group for p in pillars):
        gp = [p for p in have if p.group == g]
        gw = sum(p.weight for p in gp)
        groups[g] = sum(p.weight * p.score for p in gp) / gw if gw else None
    return score, coverage, groups


def decide(score, coverage, min_cov, hard, soft):
    """Composite + coverage + safety gates -> (kind, label, reason)."""
    if score is None or coverage < min_cov:
        return (
            "insufficient",
            LABELS["insufficient"],
            f"Only {coverage:.0%} of the pillar weight has data (minimum {min_cov:.0%}), so no result is issued. "
            "Try another ticker or fill in the missing inputs.",
        )
    kind = "strong" if score >= STRONG_MIN else "mixed" if score >= MIXED_MIN else "weak"
    reason = f"Composite score {score:.2f} out of 5."
    if hard:
        reason += " Capped at Weak by a hard safety gate." if kind != "weak" else " A hard safety gate also triggered."
        kind = "weak"
    elif soft and kind == "strong":
        reason += " Capped at Mixed by a safety gate."
        kind = "mixed"
    return kind, LABELS[kind], reason


# ══════════════════════════════════════════════════════════════════════════════
# 5. PUBLIC EQUITY SCREEN
# ══════════════════════════════════════════════════════════════════════════════
def build_public_pillars(m):
    """15 pillars, each measuring a different thing. Weights add to 100."""
    out = []

    def add(ref, group, name, weight, value, fmt, cuts, higher, note):
        out.append(Pillar(ref, group, name, weight, value, fmt(value) if value is not None else "n/a",
                          tier(value, cuts, higher), note))

    g1, g2, g3, g4 = "Moat & growth", "Returns & balance sheet", "Valuation", "Governance & capital allocation"
    pct = lambda v: f"{v * 100:.1f}%"

    add("1.1", g1, "Gross margin level", 7, m["gross_margin"], pct, (0.50, 0.35, 0.20, 0.10), True,
        "Pricing power. Absolute thresholds, not sector-adjusted.")
    add("1.2", g1, "Gross margin trend", 5, m["gm_trend_pp"], lambda v: f"{v:+.1f} pp", (2, -1, -4, -8), True,
        "Change across the available annual filings. Erosion is an early moat warning.")
    add("1.3", g1, "Operating margin", 6, m["op_margin"], pct, (0.25, 0.15, 0.08, 0.03), True,
        "Cost discipline after overheads. Not sector-adjusted.")
    add("1.4", g1, "Revenue CAGR", 7, m["rev_cagr"], lambda v: f"{v * 100:.1f}% ({m['rev_years']}y)",
        (0.15, 0.08, 0.03, 0.0), True, "Compound growth from annual filings (needs 3+ years).")
    add("1.5", g1, "Net income CAGR", 6, m["ni_cagr"], lambda v: f"{v * 100:.1f}% ({m['ni_years']}y)",
        (0.15, 0.08, 0.03, 0.0), True, "Needs positive net income at both ends of the period.")

    add("2.1", g2, "Return on capital", 10, m["roc"], lambda v: f"{m['roc_label']}: {v * 100:.1f}%",
        (0.20, 0.15, 0.10, 0.05), True, "ROIC preferred. Falls back to average ROE, which leverage can inflate.")
    add("2.2", g2, "Debt / equity", 7, m["de"], lambda v: f"{v:.0f}%", (30, 75, 150, 250), False,
        "Yahoo reports a percentage and includes leases. n/a when book equity is negative.")
    add("2.3", g2, "Interest coverage", 8, m["int_cov"],
        lambda v: "No debt" if m["no_debt"] else (">50x" if v > 50 else f"{v:.1f}x"),
        (10, 6, 3, 1.5), True, "EBIT divided by interest expense (latest annual filing).")
    add("2.4", g2, "FCF conversion", 7, m["fcf_conv"], lambda v: f"{v * 100:.0f}% of net income",
        (1.0, 0.8, 0.6, 0.3), True, "Free cash flow / net income: are the earnings backed by cash?")
    yrs, neg = m["fcf_years"], m["fcf_neg_years"]
    add("2.5", g2, "FCF consistency", 7, (yrs - neg) / yrs if yrs >= 3 else None,
        lambda v: f"{yrs - neg} of {yrs} years positive", (1.0, 0.75, 0.5, 0.25), True,
        "Share of recent annual filings with positive free cash flow (needs 3+ years).")

    add("3.1", g3, "FCF yield", 8, m["fcf_yield"], pct, (0.06, 0.04, 0.025, 0.01), True,
        "Trailing FCF / market cap. Skipped if reporting and trading currencies differ.")
    add("3.2", g3, "PEG", 7, m["peg"], lambda v: f"{v:.2f}x ({m['peg_source']})", (1.0, 1.5, 2.0, 3.0), False,
        "P/E relative to growth. n/a when growth or P/E is not meaningful.")

    add("4.1", g4, "Insider ownership", 5, m["insider_pct"], lambda v: f"{v:.1f}%", (10, 3, 1, 0.25), True,
        "Skin in the game. Low is normal for professionally managed large caps; promoter pledging is not captured.")
    add("4.2", g4, "Share count trend", 7, m["share_cagr"], lambda v: f"{v * 100:+.1f}% a year",
        (-0.015, 0.005, 0.02, 0.04), False, m["share_note"] or "Negative = net buybacks, positive = dilution.")
    add("4.3", g4, "Analyst consensus", 3, m["analyst_mean"], lambda v: f"{v:.1f} (1 = strong buy, 5 = sell)",
        (1.8, 2.4, 3.0, 3.5), False, "Sentiment only, so low weight. Needs 3+ analysts.")
    return out


def public_gates(m):
    """Returns (hard_gates, soft_gates, red_flags), each a list of (title, detail)."""
    hard, soft, flags = [], [], []

    if m["ni_ttm"] is not None and m["ni_ttm"] <= 0:
        hard.append(("Loss-making", "Trailing net income is zero or negative, so this is not a profitable compounder."))
    ic = m["int_cov"]
    if ic is not None and ic < 1.5:
        hard.append(("Interest coverage below 1.5x", f"EBIT covers interest only {ic:.1f}x."))
    elif ic is not None and ic < 3:
        soft.append(("Interest coverage below 3x", f"EBIT covers interest only {ic:.1f}x."))
    if m["fcf_years"] >= 3 and m["fcf_neg_years"] >= 3:
        hard.append(("Persistent negative free cash flow",
                     f"FCF was negative in {m['fcf_neg_years']} of the last {m['fcf_years']} annual filings."))
    if m["de"] is not None and m["de"] > 150:
        soft.append(("Debt / equity above 150%", f"Debt is {m['de']:.0f}% of book equity."))
    if m["nd_ebitda"] is not None and m["nd_ebitda"] > 4:
        soft.append(("Net debt above 4x EBITDA", f"Net debt is {m['nd_ebitda']:.1f}x EBITDA."))
    if m["fcf_ttm"] is not None and m["fcf_ttm"] < 0:
        soft.append(("Negative trailing free cash flow", "The business is not currently self-funding."))
    if m["share_cagr"] is not None and m["share_cagr"] > 0.03:
        soft.append(("Heavy share dilution", f"Share count is growing {m['share_cagr'] * 100:.1f}% a year."))
    if m["rev_cagr"] is not None and m["rev_cagr"] < 0:
        soft.append(("Shrinking revenue", f"Revenue CAGR is {m['rev_cagr'] * 100:.1f}%."))

    if m["peg"] is not None and m["peg"] > 2.5:
        flags.append(("PEG above 2.5x", f"PEG is {m['peg']:.2f}x: the price already assumes strong growth."))
    if m["roc"] is not None and m["roc"] < 0.08:
        flags.append(("Low capital efficiency",
                      f"{m['roc_label']} is {m['roc'] * 100:.1f}%, below a typical 8-10% cost of capital."))
    if m["fcf_conv"] is not None and m["fcf_conv"] < 0.5:
        flags.append(("Weak cash conversion", f"FCF is only {m['fcf_conv'] * 100:.0f}% of net income."))
    if m["sbc_pct"] is not None and m["sbc_pct"] > 0.10:
        flags.append(("Heavy stock-based compensation",
                      f"SBC is {m['sbc_pct'] * 100:.0f}% of revenue, a real cost that FCF hides."))
    if m["op_margin"] is not None and m["op_margin"] < 0.05:
        flags.append(("Thin operating margin", f"Operating margin is {m['op_margin'] * 100:.1f}%."))
    if m["neg_equity"]:
        flags.append(("Negative book equity", "D/E and ROE are not meaningful. Check net debt / EBITDA instead."))
    return hard, soft, flags


def forward_model(m, cfg):
    """Illustrative 2-year EPS / price path -> (result dict or None, reason if None).

    Growth = conservative multi-year growth, capped. Exit P/E = lower of today's P/E and the
    PEG-implied P/E, so the multiple can stay flat or shrink but never expands. Fair value = year-2
    price discounted at the required return. The entry price adds a margin of safety. Analyst targets
    are never used. The required return is cfg["req_return"] and the exit-multiple floor is cfg["min_pe"]
    when present (else MIN_PE): that is how the optional rate links reach the model.
    """
    if m["currency_mismatch"]:
        return None, ("Prices are quoted in one currency and financials reported in another (typical for ADRs), "
                      "so per-share forecasts are skipped to avoid mixing currencies.")
    eps0, price = m["eps_ttm"], m["price"]
    if eps0 is None or eps0 <= 0 or price is None or price <= 0:
        return None, "Trailing EPS or price is unavailable (or EPS is not positive), so no forward valuation is produced."
    hist = [x for x in (m["ni_cagr"], m["rev_cagr"]) if x is not None]
    if hist:
        g_raw = GROWTH_BASES[cfg["growth_basis"]](hist)
    elif m["earn_growth"] is not None:
        g_raw = m["earn_growth"]
    else:
        return None, "No growth history is available, so no forward valuation is produced."
    g = min(max(g_raw, 0.0), cfg["max_growth"])
    floor = cfg.get("min_pe", MIN_PE)  # the fixed 15x unless the optional rate link has replaced it
    pe_peg = min(cfg["max_pe"], max(floor, cfg["target_peg"] * g * 100))
    mult = min(m["pe_ttm"], pe_peg) if m["pe_ttm"] else pe_peg
    eps1 = eps0 * (1 + g)
    eps2 = eps1 * (1 + g * EPS_GROWTH_FADE)
    p1, p2 = eps1 * mult, eps2 * mult
    fair = p2 / (1 + cfg["req_return"]) ** 2
    entry = fair * (1 - cfg["mos"])
    ni0 = m["ni_ttm"]
    return {
        "g_raw": g_raw, "g": g, "pe_peg": pe_peg, "mult": mult, "min_pe": floor, "req_return": cfg["req_return"],
        "eps": [eps0, eps1, eps2],
        "ni": [ni0, ni0 * eps1 / eps0 if ni0 is not None else None, ni0 * eps2 / eps0 if ni0 is not None else None],
        "prices": [price, p1, p2],
        "fair": fair, "entry": entry,
        "implied": (p2 / price) ** 0.5 - 1,
    }, ""


# ══════════════════════════════════════════════════════════════════════════════
# 5b. RATE LINKS AND STRESS TESTS  (version 2, optional; none of this touches a pillar score)
# ══════════════════════════════════════════════════════════════════════════════
def fmt_rate(v):
    """0.0985 -> '9.85%'. A whole rate such as 0.10 prints as '10%'."""
    text = f"{v * 100:.2f}".rstrip("0").rstrip(".")
    return text + "%"


def default_rates(cfg):
    """The fixed assumptions, untouched. Every stock gets exactly this unless a rate link is switched on."""
    return {"req_return": cfg["req_return"], "min_pe": MIN_PE, "r_linked": False, "floor_linked": False,
            "market": None, "y10": None, "r_implied": None, "g_lt": None, "lines": [], "notes": []}


def market_for(m):
    """Which rate curve applies to a stock, judged from its trading currency: 'US', 'IN' or None."""
    cur = (m.get("currency") or "").upper()
    if cur == "USD":
        return "US"
    if cur == "INR" or (not cur and str(m.get("ticker") or "").upper().endswith((".NS", ".BO"))):
        return "IN"
    return None


def linked_required_return(y10, erp):
    """10-year government yield plus the equity risk premium, held between REQ_RETURN_MIN and REQ_RETURN_MAX."""
    return min(max(y10 + erp, REQ_RETURN_MIN), REQ_RETURN_MAX)


def linked_floor(r, g_lt):
    """P/E that a business with no growth premium would justify: 1 / (required return - long-run growth),
    held between FLOOR_PE_MIN and FLOOR_PE_MAX."""
    spread = r - g_lt
    if spread <= 0:
        return FLOOR_PE_MAX
    return min(max(1.0 / spread, FLOOR_PE_MIN), FLOOR_PE_MAX)


def us_10y(mc, get_mkt=None, get_fred=None):
    """US 10-year yield as a fraction -> (value or None, source text). A typed override wins over live data."""
    if mc.get("us_y10"):
        return mc["us_y10"], "entered by you"
    errors = []
    found = yield_reading("^TNX", "DGS10", get_mkt or fetch_market_close, get_fred or fetch_fred, errors)
    if found is None:
        return None, "; ".join(errors) or "no data"
    v, as_of, source = found
    return v / 100, f"{source}, {as_of}"


def resolve_rates(m, cfg, get_mkt=None, get_fred=None):
    """Which required return and exit-multiple floor the forward model should use for this stock.

    With both links off (the default) this returns the sidebar's fixed values and fetches nothing. A link that
    cannot be applied (unsupported currency, no yield available) falls back to the fixed values and says why.
    """
    out = default_rates(cfg)
    want_r, want_f = bool(cfg.get("link_r")), bool(cfg.get("link_floor"))
    if not (want_r or want_f):
        return out
    mc = cfg.get("macro") or {}
    market = market_for(m)
    if market is None:
        out["notes"].append(
            f"The rate links cover US-dollar and Indian-rupee stocks. This one trades in {m.get('currency') or 'an unknown currency'}, "
            "so the fixed assumptions are used.")
        return out
    if market == "US":
        y10, source = us_10y(mc, get_mkt, get_fred)
    else:
        y10, source = mc.get("in_y10"), "entered by you"
    if y10 is None:
        if market == "US":
            out["notes"].append(f"No US 10-year yield could be loaded ({source}). Type one in under Macro overlay in the "
                                "sidebar; until then the fixed assumptions are used.")
        else:
            out["notes"].append("No India 10-year yield has been entered under Macro overlay in the sidebar, so the "
                                "fixed assumptions are used.")
        return out
    erp = mc.get("erp", DEFAULT_ERP)
    raw_r = y10 + erp
    r_imp = linked_required_return(y10, erp)
    name = "US" if market == "US" else "India"
    out.update(market=market, y10=y10, r_implied=r_imp)
    if want_r:
        out.update(req_return=r_imp, r_linked=True)
        line = f"Required return: {name} 10-year yield {y10 * 100:.2f}% ({source}) + {erp * 100:.1f}% equity risk premium = {fmt_rate(raw_r)}"
        if abs(raw_r - r_imp) > 1e-12:
            line += f", outside the {fmt_rate(REQ_RETURN_MIN)} to {fmt_rate(REQ_RETURN_MAX)} band, so {fmt_rate(r_imp)} is used"
        out["lines"].append(line + ".")
    if want_f:
        g_lt = mc.get("g_us" if market == "US" else "g_in", DEFAULT_G_US if market == "US" else DEFAULT_G_IN)
        floor = linked_floor(r_imp, g_lt)
        raw_f = 1.0 / (r_imp - g_lt) if r_imp > g_lt else None
        out.update(min_pe=floor, floor_linked=True, g_lt=g_lt)
        shown = "no positive spread" if raw_f is None else f"{raw_f:.1f}x"
        line = f"Exit-multiple floor: 1 / ({fmt_rate(r_imp)} - {g_lt * 100:.1f}% long-run growth) = {shown}"
        if raw_f is None or abs(raw_f - floor) > 1e-9:
            line += f", outside the {FLOOR_PE_MIN:.0f}x to {FLOOR_PE_MAX:.0f}x band, so {floor:.1f}x is used"
        out["lines"].append(line + f", replacing the fixed {MIN_PE:.0f}x.")
    return out


def rate_sensitivity(m, fcfg, rates, steps=(-0.02, -0.01, 0.0, 0.01, 0.02)):
    """Fair value and entry price if rates were `step` higher or lower. The step moves the required return one for
    one, and the exit-multiple floor too when that floor is rate-linked."""
    out = []
    for d in steps:
        r = fcfg["req_return"] + d
        if r < 0.02:
            continue
        floor = fcfg.get("min_pe", MIN_PE)
        if rates.get("floor_linked"):
            floor = linked_floor(rates["r_implied"] + d, rates["g_lt"])
        fwd, _ = forward_model(m, {**fcfg, "req_return": r, "min_pe": floor})
        if fwd:
            out.append({"d": d, "r": r, "floor": floor, "fair": fwd["fair"], "entry": fwd["entry"]})
    return out


def stress_inputs(snap, m):
    """Extra figures the stress tests need from the annual statements. Missing -> None, never a default."""
    inc, bal, cf = snap["income"], snap["balance"], snap["cashflow"]
    rev_pts = stmt_series(inc, "Total Revenue", "Operating Revenue")
    ebit_pts = stmt_series(inc, "EBIT", "Operating Income")
    int_pts = stmt_series(inc, "Interest Expense", "Interest Expense Non Operating")
    gm_pts = margin_series(stmt_series(inc, "Gross Profit"), rev_pts)
    fcf_pts = fcf_series(cf)
    return {
        "ebit": ebit_pts[-1][1] if ebit_pts else None,
        "interest": abs(int_pts[-1][1]) if int_pts else None,
        "debt": coalesce(latest(bal, "Total Debt"), m["total_debt"]),
        "debt_due": coalesce(latest(bal, "Current Debt And Capital Lease Obligation"), latest(bal, "Current Debt")),
        "cash": coalesce(latest(bal, "Cash Cash Equivalents And Short Term Investments", "Cash And Cash Equivalents"),
                         m["cash"]),
        "fcf": fcf_pts[-1][1] if fcf_pts else None,
        "ebit_series": ebit_pts[-4:],
        "margin_series": margin_series(ebit_pts, rev_pts)[-4:],
        "gm_n": len(gm_pts),
    }


def stress_row(name, status, reading, detail):
    return {"name": name, "status": status, "reading": reading, "detail": detail}


def cover_status(c):
    return "risk" if c < COVER_RISK else "watch" if c < COVER_WATCH else "ok"


def stress_tests(m, si, shock, reg_level="Not assessed", reg_note=""):
    """Information-only tests of how a business copes with higher rates, a debt wall, a downturn and inflation.
    They never touch the score, the label or the safety gates. -> list of {name, status, reading, detail};
    status is ok / watch / risk / na."""
    fs = m["fin_sym"]
    si = si or {}
    rows = []
    ebit, interest, debt, due = si.get("ebit"), si.get("interest"), si.get("debt"), si.get("debt_due")
    if due is not None and debt is not None:
        due = min(max(due, 0.0), debt)

    # 1. Interest cover if rates rise ------------------------------------------------------------------
    name = f"Interest cover if rates rise {shock * 100:.1f} pts"
    how = ("Extra interest = the rate rise x the debt that reprices. The 'refinanced' case covers only debt due within "
           "a year. The 'all debt' case is an upper bound, because fixed-rate bonds do not reprice and Yahoo does not "
           "split fixed from floating debt. Uses the latest annual EBIT and interest expense, like pillar 2.3. Cut-offs "
           f"match the coverage gates: under {COVER_WATCH:.0f}x is watch, under {COVER_RISK:.1f}x is risk.")
    if debt is not None and debt <= 0:
        rows.append(stress_row(name, "ok", "No debt", "No borrowings on the latest balance sheet, so higher rates do "
                                                      "not raise interest costs directly."))
    elif ebit is None or not interest or debt is None:
        rows.append(stress_row(name, "na", "n/a", "Needs EBIT, interest expense and total debt from the latest annual filing."))
    else:
        base = ebit / interest
        cover_all = ebit / (interest + shock * debt)
        if due is not None:
            cover_due = ebit / (interest + shock * due)
            status = cover_status(cover_due)
            if status == "ok" and cover_all < COVER_RISK:
                status = "watch"
            reading = (f"{base:.1f}x today. {cover_due:.1f}x if the debt due within a year is refinanced at the higher "
                       f"rate. {cover_all:.1f}x if all debt reprices.")
        else:
            status = cover_status(cover_all)
            status = "watch" if status == "risk" else status
            reading = f"{base:.1f}x today. {cover_all:.1f}x if all debt reprices (debt due within a year is not reported)."
        rows.append(stress_row(name, status, reading, how))

    # 2. Debt due within a year ------------------------------------------------------------------------
    name = "Debt due within a year"
    cash, fcf = si.get("cash"), si.get("fcf")
    if due is None:
        rows.append(stress_row(name, "na", "n/a", "The latest annual balance sheet does not report current debt."))
    elif due <= 0:
        rows.append(stress_row(name, "ok", "None due", "No debt falls due within a year on the latest annual balance sheet."))
    elif cash is None:
        rows.append(stress_row(name, "na", f"{fmt_big(due, fs)} due; cash not reported",
                               "Needs cash and short-term investments from the latest annual balance sheet."))
    else:
        share = f" ({due / debt:.0%} of total debt)" if debt else ""
        by_cash = cash / due
        by_flow = (cash + max(fcf or 0.0, 0.0)) / due
        status = "ok" if by_cash >= 1 else "watch" if by_flow >= 1 else "risk"
        reading = f"{fmt_big(due, fs)} due{share}. Cash and short-term investments cover it {by_cash:.1f}x"
        reading += f", or {by_flow:.1f}x with a year of free cash flow." if by_cash < 1 else "."
        rows.append(stress_row(name, status, reading,
                               "Green: cash alone covers it. Yellow: cash plus a year of free cash flow covers it. "
                               "Red: it would need refinancing or new funding. Uses the latest annual filing."))

    # 3. Earnings cyclicality --------------------------------------------------------------------------
    name = "Earnings cyclicality"
    es, ms = si.get("ebit_series") or [], si.get("margin_series") or []
    detail = (f"Worst year-over-year change in operating income (watch at {CYC_DROP_WATCH * 100:.0f}% or worse, risk at "
              f"{CYC_DROP_RISK * 100:.0f}% or worse) and the largest fall in operating margin from an earlier peak "
              f"(watch at {CYC_RANGE_WATCH * 100:.0f} pts, risk at {CYC_RANGE_RISK * 100:.0f} pts). Rising profits never "
              "count against a company. Annual filings only, so this is a short window and may miss a full cycle.")
    if len(es) < 3:
        rows.append(stress_row(name, "na", "n/a", "Needs three or more annual filings of operating income."))
    else:
        drops = [max(b / a - 1, -1.0) for (_, a), (_, b) in zip(es, es[1:]) if a > 0]
        worst = min(drops) if drops else None
        fall = None
        if len(ms) >= 3:
            peak, fall = ms[0][1], 0.0
            for _, v in ms:
                peak = max(peak, v)
                fall = max(fall, peak - v)
        if worst is None and fall is None:
            rows.append(stress_row(name, "na", "n/a", "Operating income was not positive in the earlier filings, so "
                                                      "year-over-year changes are not meaningful."))
        else:
            risk = (worst is not None and worst <= CYC_DROP_RISK) or (fall is not None and fall >= CYC_RANGE_RISK)
            watch = (worst is not None and worst <= CYC_DROP_WATCH) or (fall is not None and fall >= CYC_RANGE_WATCH)
            parts = []
            if worst is not None:
                parts.append(f"Worst year-over-year change in operating income {worst * 100:+.0f}%")
            if fall is not None:
                parts.append(f"Largest fall in operating margin from a peak {fall * 100:.1f} pts")
            rows.append(stress_row(name, "risk" if risk else "watch" if watch else "ok",
                                   ". ".join(parts) + f" ({len(es)} annual filings).", detail))

    # 4. Pricing power ---------------------------------------------------------------------------------
    name = "Pricing power (gross margin)"
    gm, trend = m.get("gross_margin"), m.get("gm_trend_pp")
    if gm is None:
        rows.append(stress_row(name, "na", "n/a", "Needs a gross-profit line, which banks and some service companies do not report."))
    elif trend is None:
        rows.append(stress_row(name, "na", f"Gross margin {gm * 100:.1f}%. Trend n/a.",
                               "Needs three or more annual filings that report gross profit."))
    else:
        status = "ok" if trend >= -1 else "watch" if trend >= -4 else "risk"
        span = si.get("gm_n") or "the available"
        rows.append(stress_row(name, status, f"Gross margin {gm * 100:.1f}%, {trend:+.1f} pts across {span} annual filings.",
                               "A company that can pass on higher costs keeps its gross margin when inflation rises. "
                               "Same cut-offs as pillar 1.2: a change of -1 pt or better is fine, worse than -4 pts is a weak spot."))

    # 5. Regulation and policy: entered by you, never scored ------------------------------------------------
    name = "Regulation and policy (your view)"
    level = reg_level if reg_level in ("Low", "Moderate", "High") else "Not assessed"
    note = (reg_note or "").strip()
    rows.append(stress_row(name, {"Low": "ok", "Moderate": "watch", "High": "risk"}.get(level, "na"),
                           level + (f": {note}" if note else "."),
                           "You set this in the sidebar. The app cannot read new laws or rulings, so it does not score "
                           "regulation. Check filings and news for the company's sector and countries."))
    return rows


# ══════════════════════════════════════════════════════════════════════════════
# 6. VENTURE LENS
# ══════════════════════════════════════════════════════════════════════════════
def venture_inputs_from_snapshot(snap, nrr=None, tam=None):
    """Public growth company -> venture inputs. Values are in millions. NRR and TAM are never guessed."""
    info, inc, cf = snap["info"], snap["income"], snap["cashflow"]
    t = snap["ticker"]
    sym = currency_symbol(info.get("financialCurrency") or info.get("currency"), t)
    rev_pts = stmt_series(inc, "Total Revenue", "Operating Revenue")
    rev = coalesce(first_num(info, "totalRevenue"), rev_pts[-1][1] if rev_pts else None)
    growth, growth_src = first_num(info, "revenueGrowth"), "Latest-quarter YoY from Yahoo (not ARR)"
    if growth is None and len(rev_pts) >= 2 and rev_pts[-2][1] > 0:
        growth, growth_src = rev_pts[-1][1] / rev_pts[-2][1] - 1, "Last two annual filings"
    gm_pts = margin_series(stmt_series(inc, "Gross Profit"), rev_pts)
    gm = coalesce(nz(first_num(info, "grossMargins")), gm_pts[-1][1] if gm_pts else None)
    fcf_pts = fcf_series(cf)
    fcf = coalesce(first_num(info, "freeCashflow"), fcf_pts[-1][1] if fcf_pts else None)
    cash, debt = first_num(info, "totalCash"), first_num(info, "totalDebt")
    mm = lambda v: v / 1e6 if v is not None else None
    return {
        "name": info.get("longName") or info.get("shortName") or t,
        "ticker": t, "sym": sym, "source": "ticker", "fetched_at": snap["fetched_at"],
        "revenue": mm(rev), "growth": growth, "growth_src": growth_src, "gross_margin": gm,
        "nrr": nrr, "tam": tam,
        "cash": mm(cash), "debt": mm(debt),
        "burn": mm(-fcf) if fcf is not None else None,  # positive = burning cash
    }


def venture_derive(vi):
    """Burn multiple, runway and Rule of 40 from raw inputs, so the inputs can never contradict each other."""
    rev, g, burn, cash = vi["revenue"], vi["growth"], vi["burn"], vi["cash"]
    net_new = rev * g / (1 + g) if (rev and g is not None and g > -1) else None
    if burn is None:
        bm = None
    elif burn <= 0:
        bm = 0.0                       # self-funding
    elif net_new is None:
        bm = None
    elif net_new <= 0:
        bm = math.inf                  # burning cash without adding revenue
    else:
        bm = burn / net_new
    if burn is not None and burn <= 0:
        runway = math.inf              # self-funding
    elif burn is None or cash is None:
        runway = None
    else:
        runway = cash / (burn / 12)
    rule40 = (g - burn / rev) * 100 if (rev and g is not None and burn is not None) else None
    return {
        "net_new": net_new, "burn_multiple": bm, "runway": runway, "rule40": rule40,
        "burning": burn is not None and burn > 0,
    }


def build_venture_pillars(vi, d):
    out = []

    def add(ref, group, name, weight, value, fmt, cuts, higher, note):
        out.append(Pillar(ref, group, name, weight, value, fmt(value) if value is not None else "n/a",
                          tier(value, cuts, higher), note))

    def fmt_bm(v):
        return "Self-funding" if v == 0 else ("No net new revenue" if math.isinf(v) else f"{v:.2f}x")

    def fmt_runway(v):
        return "Self-funding" if math.isinf(v) else f"{v:.0f} months"

    add("V1", "Unit economics", "Gross margin", 15, vi["gross_margin"], lambda v: f"{v * 100:.1f}%",
        (0.75, 0.60, 0.45, 0.30), True, "Room to fund R&D and sales as the company scales.")
    add("V2", "Growth", "Revenue / ARR growth (YoY)", 20, vi["growth"], lambda v: f"{v * 100:.0f}%",
        (1.0, 0.5, 0.25, 0.10), True, vi.get("growth_src") or "")
    add("V3", "Efficiency", "Burn multiple", 20, d["burn_multiple"], fmt_bm, (1.0, 1.5, 2.0, 3.0), False,
        "Net burn / net new revenue. At or under 1x is excellent, over 3x is poor.")
    add("V4", "Retention", "Net revenue retention", 15, vi["nrr"], lambda v: f"{v * 100:.0f}%",
        (1.20, 1.10, 1.00, 0.90), True, "Not available from Yahoo. Enter it yourself if you know it.")
    tam_score = TAM_SCORES.get(vi["tam"])
    out.append(Pillar("V5", "Market", "Addressable market (TAM)", 10,
                      float(tam_score) if tam_score else None, vi["tam"] or "n/a", tam_score,
                      "Your own judgement; leave it unknown rather than guess."))
    add("V6", "Risk", "Cash runway", 20, d["runway"], fmt_runway, (24, 18, 12, 6), True,
        "Cash / monthly net burn. Ignores debt maturities and any planned raise.")
    return out


def venture_gates(vi, d):
    hard, soft, flags = [], [], []
    rw, bm = d["runway"], d["burn_multiple"]
    if rw is not None and rw < 12:
        hard.append(("Runway under 12 months", f"About {rw:.0f} months of cash at the current burn."))
    elif rw is not None and rw < 18:
        soft.append(("Runway under 18 months", f"About {rw:.0f} months of cash at the current burn."))
    if bm is not None and bm > 3:
        hard.append(("Burn multiple above 3x", "Cash is being converted into new revenue very inefficiently."))
    if vi["nrr"] is not None and vi["nrr"] < 1.0:
        soft.append(("Net revenue retention below 100%", "The existing customer base is shrinking."))
    if vi.get("debt") and vi["cash"] is not None and d["burning"] and vi["debt"] > vi["cash"]:
        soft.append(("Debt exceeds cash while burning", "Refinancing risk: debt is larger than the cash buffer."))

    if vi["gross_margin"] is not None and vi["gross_margin"] < 0.40:
        flags.append(("Low gross margin", f"At {vi['gross_margin'] * 100:.0f}% there is little room to fund opex as it scales."))
    if vi["growth"] is not None and vi["growth"] < 0.25 and d["burning"]:
        flags.append(("Burning cash at low growth", f"Growth of {vi['growth'] * 100:.0f}% may not justify the burn."))
    if vi["growth"] is not None and vi["growth"] > PROJECTION_GROWTH_CAP:
        flags.append(("Growth capped in the projection",
                      f"Only {PROJECTION_GROWTH_CAP:.0%} is used as starting growth; extreme rates do not persist."))
    if vi["source"] == "ticker":
        flags.append(("Burn is a free-cash-flow proxy",
                      "It includes capex, which can overstate operating burn for capital-intensive companies, "
                      "and excludes stock-based compensation."))
    return hard, soft, flags


def project_venture(vi, fade, cost_ratio):
    """Simple operating model -> (DataFrame by year, summary). All amounts in millions.

    Revenue grows at start_growth x fade^t. Gross profit = revenue x gross margin. The cash cost base
    (everything below gross profit, derived from today's burn) grows at cost_ratio x revenue growth,
    which is the operating leverage assumption. Net burn = cost base - gross profit.
    """
    rev0, gm, burn0, cash0 = vi["revenue"], vi["gross_margin"], vi["burn"], vi["cash"]
    g0 = min(vi["growth"], PROJECTION_GROWTH_CAP)
    gp = rev0 * gm
    cost = max(gp + burn0, 0.0)
    cash = cash0 if cash0 is not None else float("nan")
    rows = [{"Year": 0, "Revenue": rev0, "Gross profit": gp, "Cash costs": cost, "Net burn": burn0, "Cash": cash}]
    rev = rev0
    for t in range(1, PROJECTION_YEARS + 1):
        g_t = g0 * fade ** t
        rev *= 1 + g_t
        gp = rev * gm
        cost *= 1 + g_t * cost_ratio
        burn = cost - gp
        cash -= burn
        rows.append({"Year": t, "Revenue": rev, "Gross profit": gp, "Cash costs": cost, "Net burn": burn, "Cash": cash})
    df = pd.DataFrame(rows)

    burns = df["Net burn"].tolist()
    be_months, be_idx = None, None
    if burns[0] <= 0:
        be_months, be_idx = 0.0, 0
    else:
        for i in range(1, len(burns)):
            if burns[i] <= 0:
                frac = burns[i - 1] / (burns[i - 1] - burns[i])
                be_months, be_idx = ((i - 1) + frac) * 12, i
                break
    upto = burns[1:(be_idx + 1)] if be_idx is not None else burns[1:]
    cum_burn = sum(b for b in upto if b > 0)
    min_cash = df["Cash"].min()
    gap = None if (cash0 is None or math.isnan(min_cash)) else max(0.0, -min_cash)
    return df, {"breakeven_months": be_months, "cum_burn": cum_burn, "funding_gap": gap}


def breakeven_message(summary):
    be = summary["breakeven_months"]
    if be is None:
        return "warning", (f"Not projected to reach cash breakeven within {PROJECTION_YEARS} years at these "
                           "assumptions. Growth would have to hold up, or costs grow more slowly than assumed.")
    if be == 0:
        return "success", "Already at or above cash breakeven (net burn is zero or negative)."
    years = be / 12
    if be <= 24:
        return "success", f"Near-term breakeven: about {be:.0f} months ({years:.1f} years) in this illustrative model."
    if be <= 48:
        return "info", f"Medium-term breakeven: about {years:.1f} years in this illustrative model. Watch the cash buffer."
    return "warning", f"Extended horizon: breakeven is about {years:.1f} years out. The funding line below shows whether cash lasts that long."


def funding_message(summary, cash, sym):
    gap, cum = summary["funding_gap"], summary["cum_burn"]
    if gap is None:
        return "info", (f"Cumulative burn before breakeven is about {fmt_mm(cum, sym)}. Cash on hand is unknown, "
                        "so the funding gap cannot be computed.")
    if gap > 0:
        return "warning", (f"Projected funding gap of about {fmt_mm(gap, sym)}: cash runs out before breakeven, "
                           "which implies new equity (dilution) or debt.")
    return "success", f"Cash on hand ({fmt_mm(cash, sym)}) covers the projected burn of about {fmt_mm(cum, sym)} through breakeven."


# ══════════════════════════════════════════════════════════════════════════════
# 7. UI HELPERS
# ══════════════════════════════════════════════════════════════════════════════
def pillar_dataframe(pillars):
    return pd.DataFrame([
        {
            "Ref": p.ref,
            "Group": p.group,
            "Pillar": p.name,
            "Weight": f"{p.weight:.0f}%",
            "Metric": p.display,
            "Score": str(p.score) if p.score is not None else "-",
            "Why it matters / caveat": p.note,
        }
        for p in pillars
    ])


def pillar_chart(pillars, title):
    scored = [p for p in pillars if p.score is not None]
    if not scored:
        return None
    df = pd.DataFrame({
        "Pillar": [f"{p.ref} {p.name}" for p in scored],
        "Score": [p.score for p in scored],
        "Metric": [p.display for p in scored],
    })
    fig = px.bar(df, x="Score", y="Pillar", orientation="h", color="Score", color_continuous_scale="Teal",
                 range_color=[1, 5], range_x=[0, 5], text="Metric", title=title)
    fig.update_traces(textposition="auto", cliponaxis=False)
    fig.update_yaxes(categoryorder="array", categoryarray=list(reversed(df["Pillar"].tolist())))
    fig.update_layout(height=max(320, 34 * len(df) + 120), coloraxis_showscale=False,
                      margin=dict(l=10, r=10, t=50, b=10))
    return fig


def show_verdict(kind, label, reason):
    say({"strong": "success", "mixed": "warning", "weak": "error", "insufficient": "info"}[kind],
        f"**Screen result: {label}.** {reason}")


def show_findings(hard, soft, flags):
    c1, c2 = st.columns(2)
    with c1:
        st.markdown("#### 🚧 Safety gates")
        if not (hard or soft):
            say("success", "No safety gate triggered by the available data.")
        for title, detail in hard:
            say("error", f"**{title}.** {detail} Hard gate: caps the result at Weak.")
        for title, detail in soft:
            say("warning", f"**{title}.** {detail} Soft gate: caps the result at Mixed.")
    with c2:
        st.markdown("#### 🚩 Red flags")
        if not flags:
            say("success", "No red flag triggered by the available data.")
        for title, detail in flags:
            say("warning", f"**{title}.** {detail}")


def show_scorecard(pillars, filename, title):
    fig = pillar_chart(pillars, title)
    if fig is not None:
        st.plotly_chart(fig)
    missing = [f"{p.ref} {p.name}" for p in pillars if p.score is None]
    if missing:
        st.caption("Left out of the score because no usable data was found: " + ", ".join(missing) + ".")
    df = pillar_dataframe(pillars)
    st.dataframe(df, hide_index=True)
    st.download_button("Download scorecard (CSV)", df.to_csv(index=False).encode("utf-8"),
                       file_name=filename, mime="text/csv")


def raw_inputs_table(m):
    s, fs = m["sym"], m["fin_sym"]
    items = [
        ("Price", fmt_price(m["price"], s)),
        ("Market cap", fmt_big(m["market_cap"], s)),
        ("Revenue (TTM)", fmt_big(m["rev_ttm"], fs)),
        ("Net income (TTM)", fmt_big(m["ni_ttm"], fs)),
        ("Free cash flow (TTM)", fmt_big(m["fcf_ttm"], fs)),
        ("Total debt", fmt_big(m["total_debt"], fs)),
        ("Cash and short-term investments", fmt_big(m["cash"], fs)),
        ("Book equity (latest annual)", fmt_big(m["equity"], fs)),
        ("Trailing EPS", fmt_price(m["eps_ttm"], s)),
        ("Trailing P/E", fmt_x(m["pe_ttm"])),
        (f"PEG ({m['peg_source']})", fmt_x(m["peg"], 2)),
        ("Revenue CAGR", "n/a" if m["rev_cagr"] is None else f"{fmt_pct(m['rev_cagr'])} over {m['rev_years']} years"),
        ("Net income CAGR", "n/a" if m["ni_cagr"] is None else f"{fmt_pct(m['ni_cagr'])} over {m['ni_years']} years"),
        ("Latest-quarter revenue growth (Yahoo)", fmt_pct(m["rev_growth_yoy"])),
        ("Net debt / EBITDA", fmt_x(m["nd_ebitda"])),
        ("Stock-based compensation / revenue", fmt_pct(m["sbc_pct"])),
        ("Annual filings with free cash flow", f"{m['fcf_years']} (negative in {m['fcf_neg_years']})"),
        ("Analyst consensus target (reference only)", fmt_price(m["analyst_target"], s)),
    ]
    return pd.DataFrame(items, columns=["Input", "Value"])


def show_forward(m, fwd, msg, cfg, rates=None, fixed=None):
    if fwd is None:
        say("info", msg)
        return
    s, fs = m["sym"], m["fin_sym"]
    floor = cfg.get("min_pe", MIN_PE)
    floor_txt = f"{floor:.0f}" if floor == MIN_PE else f"{floor:.1f}"
    st.caption("Illustrative model, not a forecast. Every assumption is listed below and can be changed in the sidebar.")
    if rates is not None:  # a rate link that fell back to the fixed values is never silent
        for note in rates["notes"]:
            say("warning", note)
        for line in rates["lines"]:
            st.caption(esc(line))
    if fixed is not None:
        st.caption(esc(
            f"For comparison, the fixed assumptions ({fmt_rate(fixed['req_return'])} required return, {fixed['min_pe']:.0f}x floor) "
            f"would give a fair value of {fmt_price(fixed['fair'], s)} and a max entry price of {fmt_price(fixed['entry'], s)}."
        ))
    df = pd.DataFrame({
        "Period": ["Today (TTM)", "Year 1", "Year 2"],
        "EPS": [fmt_price(x, s) for x in fwd["eps"]],
        "Net profit": [fmt_big(x, fs) for x in fwd["ni"]],
        "P/E applied": [fmt_x(m["pe_ttm"]), fmt_x(fwd["mult"]), fmt_x(fwd["mult"])],
        "Price (today) / target": [fmt_price(x, s) for x in fwd["prices"]],
    })
    st.dataframe(df, hide_index=True)
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Fair value today (model)", fmt_price(fwd["fair"], s))
    c2.metric("Max entry price", fmt_price(fwd["entry"], s), help="Fair value less the margin of safety.")
    c3.metric("Implied annual return at today's price", f"{fwd['implied'] * 100:+.1f}%",
              help="Price return only (dividends excluded), if the year-2 target is reached.")
    c4.metric("Analyst consensus target", fmt_price(m["analyst_target"], s), help="Shown for reference only; not used.")
    st.caption(esc(
        f"Growth used: {fwd['g'] * 100:.1f}% (basis: {cfg['growth_basis'].split(':')[0].lower()}; raw {fwd['g_raw'] * 100:.1f}%, "
        f"floored at 0 and capped at {cfg['max_growth'] * 100:.0f}%). Year-2 growth fades to {EPS_GROWTH_FADE:.0%} of that. "
        f"Exit P/E = lower of today's P/E and the PEG-implied P/E ({cfg['target_peg']:.1f} x growth, between {floor_txt} "
        f"and {cfg['max_pe']:.0f}), so the multiple can stay flat or shrink but never expands. Fair value discounts "
        f"the year-2 price at {fmt_rate(cfg['req_return'])} a year; the margin of safety is {cfg['mos'] * 100:.0f}%. "
        "Because growth is capped and the multiple cannot expand, high-multiple growth stocks will usually sit above "
        "the entry price. Read it as what you would have to believe, not as a price target."
    ))
    bars = pd.DataFrame({
        "Item": ["Price today", "Year-1 target", "Year-2 target", "Fair value today", "Max entry price"],
        "Value": [fwd["prices"][0], fwd["prices"][1], fwd["prices"][2], fwd["fair"], fwd["entry"]],
    })
    fig = px.bar(bars, x="Item", y="Value", text=bars["Value"].map(lambda v: f"{v:,.2f}"), title="Price vs model values")
    fig.update_layout(height=360, margin=dict(l=10, r=10, t=50, b=10))
    st.plotly_chart(fig)
    if rates is not None:
        show_rate_sensitivity(m, cfg, rates)


def show_rate_sensitivity(m, fcfg, rates):
    rows = rate_sensitivity(m, fcfg, rates)
    base = next((r for r in rows if r["d"] == 0), None)
    if base is None or len(rows) < 3:
        return
    s = m["sym"]
    with st.expander("Sensitivity to interest rates"):
        st.caption(esc(
            "What the model's fair value would be if rates were higher or lower than assumed. Each step moves the "
            "required return one for one" + (", and the exit-multiple floor with it." if rates["floor_linked"]
                                              else " (the exit-multiple floor stays fixed because it is not rate-linked).")
        ))
        df = pd.DataFrame({
            "Rates vs the model": ["As modelled" if r["d"] == 0 else f"{r['d'] * 100:+.0f} pt" for r in rows],
            "Required return": [fmt_rate(r["r"]) for r in rows],
            "Exit-multiple floor": [f"{r['floor']:.1f}x" for r in rows],
            "Fair value today": [fmt_price(r["fair"], s) for r in rows],
            "Max entry price": [fmt_price(r["entry"], s) for r in rows],
            "Fair value vs modelled": [f"{(r['fair'] / base['fair'] - 1) * 100:+.1f}%" for r in rows],
        })
        st.dataframe(df, hide_index=True)


STATUS_ICON = {"ok": "🟢", "watch": "🟡", "risk": "🔴", "na": "⚪"}


def show_stress(rows):
    st.caption("Information only. These tests do not change the score, the label or the safety gates. "
               "Green is comfortable, yellow is worth a look, red is a weak spot, white means no data. "
               "The cut-offs are rules of thumb, not calibrated.")
    for r in rows:
        st.markdown(esc(f"{STATUS_ICON[r['status']]} **{r['name']}.** {r['reading']}"))
        st.caption(esc(r["detail"]))


def macro_dataframe(rows):
    return pd.DataFrame([{
        "Indicator": r["label"],
        "Reading": r["disp"],
        "As of": r["as_of"] or "-",
        "Source": r["source"] or "-",
        "Caution when": r["rule"] or "-",
        "Caution?": "-" if r["signal"] is None else ("yes" if r["signal"] else "no"),
    } for r in rows])


def show_macro_market(title, rows, y10, mc, market):
    active = sum(1 for r in rows if r["signal"] is True)
    known = sum(1 for r in rows if r["signal"] is not None)
    st.subheader(title)
    st.markdown(f"**{active} of {known} caution signals active.**" if known else "**No caution signal could be read.**")
    st.dataframe(macro_dataframe(rows), hide_index=True)
    if y10 is not None:
        r = linked_required_return(y10, mc["erp"])
        g = mc["g_us"] if market == "US" else mc["g_in"]
        st.caption(esc(
            f"If the rate links are ticked in the screen, a stock priced in this market would use a required return of "
            f"{fmt_rate(r)} and an exit-multiple floor of {linked_floor(r, g):.1f}x, instead of the fixed sidebar return "
            f"and the fixed {MIN_PE:.0f}x floor."
        ))


def show_macro_panel(data, mc):
    st.subheader("Macro backdrop")
    st.caption("Descriptive readings of the market today. They are not forecasts, they do not change any score, and "
               "the caution rules are rules of thumb, not calibrated.")
    show_macro_market("United States", data["us"], data["y10"]["US"], mc, "US")
    show_macro_market("India", data["in"], data["y10"]["IN"], mc, "IN")
    if data["errors"]:
        with st.expander("Data that could not be loaded"):
            for err in data["errors"]:
                st.caption(esc(err))
    st.caption(f"Fetched {data['fetched_at']}. Yahoo Finance and FRED (St. Louis Fed) are free sources and can be delayed "
               "or briefly unavailable. India's policy rate, bond yield and inflation are typed in by you.")


def fmt_ret(v):
    """A price return as '+4.1%' (never '-0.0%')."""
    return "n/a" if v is None else f"{round(v * 100, 1) + 0.0:+.1f}%"


def fmt_gap(v):
    """A gap between two returns as '+4.1 pts'."""
    return "n/a" if v is None else f"{round(v * 100, 1) + 0.0:+.1f} pts"


def ctx_returns_frame(ctx):
    labels = [lab for lab, _ in CTX_WINDOWS]
    rows = [{"Series": d["label"], **{lab: fmt_ret(d["ret"][lab]) for lab in labels}, "As of": d["as_of"]}
            for d in (ctx["stock"], ctx["sector"], ctx["bench"]) if d]
    for name, key in (("Sector minus market", "sector_vs_market"), ("Stock minus sector", "stock_vs_sector")):
        gaps = ctx["gaps"].get(key)
        if gaps:
            rows.append({"Series": name, **{lab: fmt_gap(gaps.get(lab)) for lab in labels}, "As of": ""})
    return pd.DataFrame(rows)


def ctx_trend_frame(ctx):
    rows = []
    for d in (ctx["stock"], ctx["sector"], ctx["bench"]):
        t = d["trend"] if d else None
        if t:
            rows.append({
                "Series": d["label"], "Vs 50-day average": fmt_ret(t["vs_ma50"]), "Vs 200-day average": fmt_ret(t["vs_ma200"]),
                "From 52-week high": "n/a" if t["from_high"] is None else _gap(t["from_high"] * 100),
                "Position in 52-week range": "n/a" if t["range_pos"] is None else f"{t['range_pos'] * 100:.0f}%",
            })
    return pd.DataFrame(rows)


def ctx_episode_frame(rows):
    return pd.DataFrame([{
        "Episode": f"{r['name']} ({r['start']} to {r['end']})", "Market": fmt_ret(r["market"]),
        "Sector": fmt_ret(r["sector"]), "Stock": fmt_ret(r["stock"]), "Sector minus market": fmt_gap(r["sector_vs_market"]),
    } for r in rows])


def ctx_board_frame(board):
    return pd.DataFrame([{
        "Sector": r["label"], "Symbol": r["symbol"], **{lab: fmt_ret(r["ret"][lab]) for lab, _ in CTX_WINDOWS},
        "3M vs market": fmt_gap(r["rel"]["3M"]), "12M vs market": fmt_gap(r["rel"]["12M"]),
        "This stock's sector": "◀" if r["is_this"] else "",
    } for r in board])


def ctx_tape_frame(tape):
    rows = []
    for key, name in (("defensive", "Defensive average"), ("cyclical", "Cyclical average")):
        g = tape[key]
        rows.append({"Group": f"{name} ({g['used']} of {g['of']} series)",
                     **{lab: fmt_ret(g["avg"][lab]) for lab, _ in CTX_WINDOWS}})
    rows.append({"Group": "Defensive minus cyclical", **{lab: fmt_gap(tape["diff"][lab]) for lab, _ in CTX_WINDOWS}})
    return pd.DataFrame(rows)


def ctx_since_frame(ctx):
    rows = []
    for key, name in (("stock", "stock"), ("sector", "sector"), ("bench", "bench")):
        d, info = ctx["since"].get(key), ctx.get(name)
        if d and info:
            rows.append({"Series": info["label"], "First close on or after the date": d["from"],
                         "Return since": fmt_ret(d["ret"]),
                         "Highest close since": f"{d['high_date']} ({fmt_ret(d['high_ret'])})",
                         "Latest vs that high": fmt_ret(d["off_high"])})
    return pd.DataFrame(rows)


def ctx_ownership_frame(info, price, sym):
    pct = lambda v: "n/a" if v is None else f"{v * 100:.1f}%"
    mean, n, target = info.get("analyst_mean"), info.get("analyst_n"), info.get("target")
    rows = [
        ("Held by insiders", pct(info.get("insiders"))),
        ("Held by institutions", pct(info.get("institutions"))),
        ("Short interest, share of float", pct(info.get("short_float"))),
        ("Short interest, days to cover", "n/a" if info.get("short_days") is None else f"{info['short_days']:.1f}"),
        ("Analyst consensus (1 = strong buy, 5 = sell)",
         f"{mean:.1f} from {n:.0f} analysts" if mean is not None and n is not None and n >= 3 else "n/a"),
        ("Mean analyst price target (reference only)",
         "n/a" if target is None else fmt_price(target, sym) + (f" ({(target / price - 1) * 100:+.0f}% vs price)" if price else "")),
    ]
    return pd.DataFrame(rows, columns=["Figure", "Yahoo reading"])


def headline_line(item):
    """One markdown bullet for a headline. Brackets in the title are swapped for parentheses so they cannot break the
    link, and the URL was made safe in parse_news."""
    title = item["title"].replace("[", "(").replace("]", ")")
    bits = [item["date"] or "undated", f"[{title}]({item['url']})" if item["url"] else title]
    if item["publisher"]:
        bits.append(item["publisher"])
    if item["tags"]:
        bits.append("_" + ", ".join(item["tags"]) + "_")
    return "- " + " · ".join(bits)


def show_context(ctx, m, filings=None):
    s = m["sym"]
    st.caption(esc(CTX_NOTE))
    for note in ctx["notes"]:
        say("info", note)
    if ctx["proxy"] and ctx["sector"] is None:
        say("info", f"The sector series {ctx['proxy']} could not be loaded, so the sector rows are missing.")

    lines = ctx_glance(ctx)
    if lines:
        st.markdown("**At a glance**")
        for line in lines:
            st.markdown(esc(f"- {line}"))

    st.subheader("Price moves")
    st.caption("Price only (dividends are not added back, so high-dividend sectors look weaker than their total return). "
               "1M, 3M, 6M and 12M are 21, 63, 126 and 252 trading days.")
    returns = ctx_returns_frame(ctx)
    if len(returns):
        st.dataframe(returns, hide_index=True)
    else:
        say("info", "No price history could be loaded for this stock.")

    trend = ctx_trend_frame(ctx)
    if len(trend):
        st.subheader("Trend health")
        st.dataframe(trend, hide_index=True)
        st.caption("Position in the 52-week range: 0% is the lowest close of the year, 100% the highest. "
                   "A series with under a year of history shows its range since the history begins."
                   if any(d and not d["trend"]["full_year"] for d in (ctx["stock"], ctx["sector"], ctx["bench"]))
                   else "Position in the 52-week range: 0% is the lowest close of the year, 100% the highest.")

    if ctx["since"]:
        st.subheader(f"Since {ctx['since']['date']}")
        st.caption("How far the price has moved since the date you entered in the sidebar, and how much of that is still held.")
        st.dataframe(ctx_since_frame(ctx), hide_index=True)
        d_stock, d_sector = ctx["since"]["stock"], ctx["since"]["sector"]
        if d_stock and d_sector:
            st.caption(f"Stock minus sector over the same period: {fmt_gap(d_stock['ret'] - d_sector['ret'])}.")

    if ctx["episodes"]:
        st.subheader("How the sector held up in past sell-offs")
        st.caption("From the market's closing peak to its closing low in each episode; the dates are found from the market "
                   "series itself. A sector return less negative than the market's means it fell less. Each sell-off has "
                   "its own cause, so what happened in one is only a loose guide to the next. n/a means the fund or "
                   "stock did not exist yet, or Yahoo has no data for it.")
        st.dataframe(ctx_episode_frame(ctx["episodes"]), hide_index=True)

    if ctx["board"]:
        st.subheader("Sector leaderboard")
        st.caption("Every sector, ranked by its 3-month return relative to the market. Price only.")
        st.dataframe(ctx_board_frame(ctx["board"]), hide_index=True)
        names = {sym: label for label, sym in (CTX_US_BOARD if ctx["market"] == "US" else CTX_IN_BOARD)}
        groups = CTX_TAPE[ctx["market"]]
        st.markdown("**Defensive versus cyclical**")
        st.dataframe(ctx_tape_frame(ctx["tape"]), hide_index=True)
        st.caption(esc(
            f"Defensive: {', '.join(names[x] for x in groups['defensive'])}. Cyclical: {', '.join(names[x] for x in groups['cyclical'])}. "
            "Equal-weighted averages of the series that loaded. This shows whether money has recently favoured the safer "
            "sectors or the growth-sensitive ones. It describes the past; it does not predict a recession or a boom."))
        st.caption("A fund or index covers a whole sector. A narrower theme (off-price retail, say) can move differently, so "
                   "type a narrower symbol in the sidebar if you want to compare against one.")

    if ctx["info"]:
        st.subheader("Ownership and positioning")
        st.dataframe(ctx_ownership_frame(ctx["info"], m["price"], s), hide_index=True)
        st.caption("Current snapshot from Yahoo Finance. Yahoo does not show how these figures have changed, and some "
                   "(especially short interest for Indian stocks) are often missing.")

    if m.get("ctx_alloc") is not None:
        show_alloc(m["ctx_alloc"])
    if filings is not None:
        show_filings(filings)

    st.subheader("Recent headlines")
    if ctx["news"] is None:
        say("info", "Headlines could not be loaded from Yahoo Finance just now.")
    elif not ctx["news"]:
        st.caption("Yahoo returned no recent headlines for this ticker.")
    else:
        for item in ctx["news"]:
            st.markdown(esc(headline_line(item)))
        st.caption("The topic words in italics are keyword matches on the headline text, shown only to help you scan. They "
                   "are not an assessment of the news. Read the story and the company's own announcement before drawing a "
                   "conclusion.")

    with st.expander("Checklist for your own research on a catalyst"):
        st.caption("News about a government stake, a big customer or a takeover can matter. A screen like this one cannot "
                   "see it coming, so these are the questions to answer yourself.")
        for line in CTX_CHECKLIST:
            st.markdown(esc(f"- {line}"))

    if ctx["errors"]:
        with st.expander("Data that could not be loaded"):
            for err in ctx["errors"]:
                st.caption(esc(err))
    st.caption(f"Fetched {ctx['fetched_at']}. Prices and headlines come from Yahoo Finance, a free and unofficial source "
               "that can be delayed, incomplete or briefly unavailable. If a fund or index returns nothing, it is listed "
               "under 'Data that could not be loaded'.")


def alloc_frame(a):
    shown = {"chg": fmt_ret, "pct": lambda v: fmt_pct(v, 1), "x": lambda v: fmt_x(v, 1)}
    return pd.DataFrame([{"Measure": label, **{d: shown[kind](a["values"][key].get(d)) for d in a["dates"]}}
                         for key, label, kind in ALLOC_ROWS])


def show_alloc(a):
    st.subheader("Capital allocation")
    st.caption("How the company has been investing and paying for it, worked out from the annual statements Yahoo "
               "provides (newest year first). Information only: it is not part of the score.")
    if not a.get("dates"):
        for note in a.get("notes") or []:
            say("info", note)
        return
    if a["glance"]:
        st.markdown("**In brief**")
        for line in a["glance"]:
            st.markdown(esc(f"- {line}"))
    st.dataframe(alloc_frame(a), hide_index=True)
    for note in a["notes"]:
        st.caption(esc(note))
    with st.expander("How these are worked out, and what the research says"):
        for line in ALLOC_HELP:
            st.markdown(esc(f"- {line}"))
        st.caption(esc(ALLOC_RESEARCH))


FILINGS_MESSAGES = {
    "not_us": "SEC filings cover US-registered companies. This app does not fetch exchange announcements for Indian or "
              "other non-US stocks, so for those read the company's own announcements on its investor-relations page "
              "and in the exchange's announcements section.",
    "needs_contact": "To list this company's filings, type a contact email in the sidebar (under Sector & market "
                     "context) and click Run audit again. The SEC asks every automated request to carry one. It is sent "
                     "to the SEC only, and kept only for this session.",
    "bad_contact": "The contact email in the sidebar does not look like an email address, so nothing was sent to the SEC.",
    "error": "The SEC filings could not be loaded just now. The rest of this tab is unaffected. A refusal (HTTP 403) "
             "usually means the SEC did not accept the contact email or is limiting requests, so check the address "
             "and try again in a minute.",
}
FILINGS_INTRO = (
    "Form 8-K is how US companies report significant events, generally within four business days: agreements, "
    "completed acquisitions, restructuring, equity sales, changes of auditor or officers and so on. This lists what "
    "was filed, newest first. It does not say whether an event is good or bad news, and an expansion announcement "
    "often sits under the catch-all items (7.01 and 8.01) or in a press release attached to the filing, so open the "
    "filing before drawing a conclusion. Information only. Source: SEC EDGAR."
)


def filings_counts_frame(fl):
    rows = []
    for c in fl["counts"]:
        name, group = FILING_ITEMS.get(c["code"], (f"Item {c['code']} (not described in this app)", "Other"))
        rows.append({"Item": c["code"], "What it covers": name, "Group": group, "Filings": c["n"], "Latest": c["latest"],
                     "Read first": "Yes" if c["code"] in FILING_READ_FIRST else ""})
    return pd.DataFrame(rows)


def filing_line(r):
    """One markdown bullet for a filing. Every piece is checked or comes from the app's own tables."""
    codes = [c for c in (r["items"] or []) if c != "9.01"]
    if r["form"] == "6-K":
        what = "foreign-company report (no item codes; open it to see what it covers)"
    elif r["items"] is None:
        what = "item codes not available"
    elif not codes:
        what = "exhibits only"
    else:
        what = "; ".join(f"{c} {FILING_ITEMS[c][0] if c in FILING_ITEMS else '(not described in this app)'}"
                         for c in codes)
    bits = [r["date"], r["form"], what]
    if r["items_from"] == "text":
        bits.append("_read from the filing text_")
    if r.get("after"):
        bits.append("_after your date_")
    if r["url"]:
        bits.append(f"[open]({r['url']})")
    return "- " + " · ".join(bits)


def show_filings(fl):
    st.subheader("Company filings (SEC EDGAR)")
    status = fl.get("status")
    if status in FILINGS_MESSAGES and status != "error":
        say("info", FILINGS_MESSAGES[status])
        return
    if status == "not_found":
        say("info", f"The SEC's company list has no entry for {fl.get('ticker') or 'this ticker'}. It may not be "
                    "registered with the SEC, or Yahoo may use a different symbol.")
        return
    if status != "ok":
        say("info", FILINGS_MESSAGES["error"])
        for err in fl.get("errors") or []:
            st.caption(esc(err))
        return

    st.caption(esc(FILINGS_INTRO))
    who = plain(fl.get("name"))
    if who:
        st.caption(esc(f"SEC record: {who}."))
    lines = filings_glance(fl)
    if lines:
        st.markdown("**In brief**")
        for line in lines:
            st.markdown(esc(f"- {line}"))
    if fl["short_coverage"]:
        st.caption(esc(f"The list the SEC provides starts on {fl['coverage_start']}, so nothing earlier is shown here "
                       "(for a recently listed company that is expected)."))
    if not fl["rows"]:
        st.caption(esc(f"No Form 8-K or 6-K filings are listed since {fl['window_start']}."))
    else:
        if fl["counts"]:
            st.dataframe(filings_counts_frame(fl), hide_index=True)
            st.caption(f"Counts cover 8-K reports filed since {fl['window_start']}. Amendments (8-K/A) are listed but not "
                       "counted, and Item 9.01 (exhibits) is left out. \"Read first\" is the app's own shortlist of item "
                       "types that deserve a careful look, not a verdict.")
        rows = fl["rows"]
        st.markdown(f"**Filings since {fl['window_start']}**" + (f" ({fl['n_window']} in all, newest {len(rows)} listed)"
                                                                if fl["n_window"] > len(rows) else ""))
        for r in rows[:FILINGS_SHOWN_FIRST]:
            st.markdown(esc(filing_line(r)))
        if len(rows) > FILINGS_SHOWN_FIRST:
            with st.expander(f"Older filings in this period ({len(rows) - FILINGS_SHOWN_FIRST})"):
                for r in rows[FILINGS_SHOWN_FIRST:]:
                    st.markdown(esc(filing_line(r)))
    if fl["text_read"] or fl["text_unread"]:
        total = fl["text_read"] + fl["text_unread"]
        st.caption(esc(
            f"The SEC's list gave no item codes for {total} filing{'s' if total != 1 else ''}. "
            + (f"For {fl['text_read']} of them the codes were read from the filing text, which is a best-effort reading"
               if fl["text_read"] else "None of them could be read from the filing text")
            + (f"; for the other {fl['text_unread']} no codes could be read." if fl["text_read"] and fl["text_unread"]
               else "." if fl["text_read"] else ".")))
    for err in fl["errors"]:
        st.caption(esc(err))
    if fl.get("browse_url"):
        st.markdown(f"[All of this company's filings on EDGAR]({fl['browse_url']})")
    st.caption(esc(f"Fetched {fl['fetched_at']} from the SEC's public EDGAR service."))


# ══════════════════════════════════════════════════════════════════════════════
# 8. RENDERERS
# ══════════════════════════════════════════════════════════════════════════════
def render_excluded(m, why):
    s = m["sym"]
    st.subheader(f"{m['name']} ({m['ticker']})")
    say("warning", f"**The screen is not applicable to the {m['sector']} sector.** {why}")
    c1, c2, c3, c4 = st.columns(4)
    c1.metric("Price", fmt_price(m["price"], s))
    c2.metric("Market cap", fmt_big(m["market_cap"], s))
    c3.metric("Trailing P/E", fmt_x(m["pe_ttm"]))
    c4.metric("Price / book", fmt_x(m["pb"], 2))
    say("info", "To run the screen anyway (results will be unreliable), tick the box in the sidebar and click Run audit again.")


def render_public(m, cfg):
    s = m["sym"]
    pillars = build_public_pillars(m)
    score, coverage, groups = summarize(pillars)
    hard, soft, flags = public_gates(m)
    kind, label, reason = decide(score, coverage, MIN_COVERAGE_PUBLIC, hard, soft)
    try:
        rates = resolve_rates(m, cfg)
    except Exception as exc:  # noqa: BLE001 - an optional feature must never stop the screen
        rates = default_rates(cfg)
        rates["notes"].append(f"The rate links could not be applied ({type(exc).__name__}), so the fixed assumptions are used.")
    fcfg = {**cfg, "req_return": rates["req_return"], "min_pe": rates["min_pe"]}
    fwd, fwd_msg = forward_model(m, fcfg)
    fixed = forward_model(m, cfg)[0] if (rates["r_linked"] or rates["floor_linked"]) else None
    try:
        stress = None if m.get("stress") is None else stress_tests(
            m, m["stress"], (cfg.get("macro") or {}).get("shock", DEFAULT_SHOCK),
            cfg.get("reg_level", REG_LEVELS[0]), cfg.get("reg_note", ""))
    except Exception:  # noqa: BLE001 - same rule: the stress tests are an extra, not part of the screen
        stress = None

    st.subheader(f"{m['name']} ({m['ticker']})")
    st.caption(esc(
        f"{m['sector']}, {m['industry']}. Price {fmt_price(m['price'], s)}, market cap {fmt_big(m['market_cap'], s)}. "
        f"Yahoo Finance data fetched {m['fetched_at']}."
    ))
    rule = sector_rule(m["sector"], m["industry"])
    if rule:
        extra = " You chose to run it anyway, so treat the result as unreliable." if rule[0] == "exclude" else ""
        say("warning", f"**{m['sector']} sector.** {rule[1]}{extra}")
    if m["currency_mismatch"]:
        say("warning", f"The price is in {m['currency']} but financials are reported in {m['fin_currency']}. "
                       "FCF yield and the forward valuation are skipped to avoid mixing currencies.")

    c1, c2, c3, c4 = st.columns(4)
    have = sum(1 for p in pillars if p.score is not None)
    c1.metric("Screen result", label)
    c2.metric("Composite score", "n/a" if score is None else f"{score:.2f} / 5")
    c3.metric("Data coverage", f"{coverage:.0%}",
              help=f"{have} of {len(pillars)} pillars had data. Missing pillars are left out and the remaining weights are rescaled.")
    if fwd:
        c4.metric("Model entry price", fmt_price(fwd["entry"], s),
                  delta=f"{(m['price'] / fwd['entry'] - 1) * 100:+.1f}% price vs entry", delta_color="inverse",
                  help="From the illustrative forward model in the second tab. Not an analyst target.")
    else:
        c4.metric("Model entry price", "n/a", help=fwd_msg)
    show_verdict(kind, label, reason)

    for col, (g, v) in zip(st.columns(len(groups)), groups.items()):
        col.metric(g, "n/a" if v is None else f"{v:.2f} / 5")
    show_findings(hard, soft, flags)

    flagged = bool(stress) and any(r["status"] == "risk" for r in stress)
    show_ctx = bool(cfg.get("show_context"))
    tab_names = ["Scorecard", "Forward valuation (illustrative)", "Stress tests (info only)" + (" ⚠" if flagged else "")]
    if show_ctx:
        tab_names.append("Sector & market context (info only)")
    tabs = st.tabs(tab_names + ["Inputs used"])
    t1, t2, t3, t4 = tabs[0], tabs[1], tabs[2], tabs[-1]
    with t1:
        show_scorecard(pillars, f"{m['ticker']}_scorecard.csv", "Pillar scores (1 = poor, 5 = excellent)")
    with t2:
        show_forward(m, fwd, fwd_msg, fcfg, rates, fixed)
    with t3:
        if stress is None:
            say("info", "The stress tests could not be computed from the data Yahoo returned.")
        else:
            show_stress(stress)
    if show_ctx:
        with tabs[3]:
            try:
                with st.spinner("Fetching sector and market prices (the first load can be slow; later loads use a cache)..."):
                    ctx = collect_context(m, cfg)
                    filings = None
                    if cfg.get("ctx_filings", True):
                        try:
                            filings = collect_filings(m, cfg)
                        except Exception as exc:  # noqa: BLE001 - the filings panel is an extra inside an extra
                            filings = {"status": "error", "errors": [type(exc).__name__]}
                show_context(ctx, m, filings)
            except Exception as exc:  # noqa: BLE001 - an optional extra must never stop the screen
                say("info", f"The context tab could not be built ({type(exc).__name__}). The screen above is unaffected.")
    with t4:
        st.caption("Check these against the Yahoo Finance page or the company filings before relying on the result.")
        st.dataframe(raw_inputs_table(m), hide_index=True)


def render_venture(vi, fade, cost_ratio):
    s = vi["sym"]
    d = venture_derive(vi)
    pillars = build_venture_pillars(vi, d)
    score, coverage, _ = summarize(pillars)
    hard, soft, flags = venture_gates(vi, d)
    kind, label, reason = decide(score, coverage, MIN_COVERAGE_VENTURE, hard, soft)
    can_project = (vi["revenue"] and vi["growth"] is not None and vi["gross_margin"] is not None
                   and vi["burn"] is not None)
    df_proj, summary = project_venture(vi, fade, cost_ratio) if can_project else (None, None)

    st.subheader(f"Venture growth dashboard: {vi['name']}")
    src = "Manual inputs." if vi["source"] == "manual" else f"Yahoo Finance data fetched {vi['fetched_at']}."
    st.caption(esc(f"{src} Amounts in millions of {s.strip()}."))

    rw, bm = d["runway"], d["burn_multiple"]
    c1, c2, c3, c4, c5 = st.columns(5)
    c1.metric("Screen result", label)
    c2.metric("Composite score", "n/a" if score is None else f"{score:.2f} / 5")
    c3.metric("Cash runway", "n/a" if rw is None else "Self-funding" if math.isinf(rw) else f"{rw:.0f} months")
    c4.metric("Burn multiple", "n/a" if bm is None else "Self-funding" if bm == 0 else "No net new revenue"
              if math.isinf(bm) else f"{bm:.2f}x")
    c5.metric("Data coverage", f"{coverage:.0%}",
              help="Share of pillar weight that has data. Missing pillars are left out and the rest rescaled.")
    show_verdict(kind, label, reason)
    show_findings(hard, soft, flags)

    t1, t2, t3 = st.tabs(["Scorecard", "Projection and breakeven", "Inputs and derived metrics"])
    with t1:
        show_scorecard(pillars, f"{vi['name'].replace(' ', '_')}_venture_scorecard.csv", "Venture pillar scores (1 = poor, 5 = excellent)")
    with t2:
        if df_proj is None:
            say("info", "A projection needs revenue, growth, gross margin and net burn. Fill in the missing inputs.")
        else:
            st.caption("Illustrative operating model, not a forecast. Growth fades each year and the cost base grows "
                       "more slowly than revenue (operating leverage). Change both in the sidebar.")
            level, text = breakeven_message(summary)
            say(level, f"**Breakeven.** {text}")
            level, text = funding_message(summary, vi["cash"], s)
            say(level, f"**Funding.** {text}")
            long = df_proj.melt(id_vars="Year", value_vars=["Revenue", "Gross profit", "Cash costs"],
                                var_name="Series", value_name="Amount")
            fig = px.line(long, x="Year", y="Amount", color="Series", markers=True,
                          title="Revenue, gross profit and cash costs (millions)")
            fig.update_layout(height=400, margin=dict(l=10, r=10, t=50, b=10))
            st.plotly_chart(fig)
            if not df_proj["Cash"].isna().all():
                cash_df = df_proj[["Year", "Cash"]].copy()
                cash_df["Status"] = ["Funded" if v >= 0 else "Shortfall" for v in cash_df["Cash"]]
                fig2 = px.bar(cash_df, x="Year", y="Cash", color="Status",
                              color_discrete_map={"Funded": "#0EA5E9", "Shortfall": "#DC2626"},
                              title="Projected cash balance (millions); below zero means new funding is needed")
                fig2.update_layout(height=320, margin=dict(l=10, r=10, t=50, b=10))
                st.plotly_chart(fig2)
            show = df_proj.copy()
            show["Year"] = ["Today"] + [f"Year {i}" for i in range(1, PROJECTION_YEARS + 1)]
            for col in ("Revenue", "Gross profit", "Cash costs", "Net burn", "Cash"):
                show[col] = show[col].map(lambda v: fmt_mm(None if math.isnan(v) else v, s))
            st.dataframe(show, hide_index=True)
    with t3:
        items = [
            ("Revenue / ARR", fmt_mm(vi["revenue"], s)),
            ("Growth (YoY)", f"{fmt_pct(vi['growth'], 0)}  [{vi.get('growth_src') or 'user input'}]"),
            ("Gross margin", fmt_pct(vi["gross_margin"])),
            ("Net revenue retention", fmt_pct(vi["nrr"], 0)),
            ("TAM", vi["tam"] or "n/a"),
            ("Cash on hand", fmt_mm(vi["cash"], s)),
            ("Debt", fmt_mm(vi.get("debt"), s)),
            ("Annual net burn (negative = cash-generative)", fmt_mm(vi["burn"], s)),
            ("Net new revenue, last 12 months (derived)", fmt_mm(d["net_new"], s)),
            ("Rule of 40: growth + free-cash-flow margin (derived)", "n/a" if d["rule40"] is None else f"{d['rule40']:.0f}"),
        ]
        st.dataframe(pd.DataFrame(items, columns=["Input", "Value"]), hide_index=True)
        if vi["source"] == "ticker":
            st.caption("Growth is the latest-quarter year-on-year rate and burn is free cash flow, both from Yahoo. "
                       "Neither is ARR or operating burn, so treat the burn multiple as an approximation.")


# ══════════════════════════════════════════════════════════════════════════════
# 9. APP FLOW
# ══════════════════════════════════════════════════════════════════════════════
def explain_error(exc):
    text = f"{type(exc).__name__}: {exc}"
    if any(k in text for k in ("RateLimit", "Too Many Requests", "429")):
        return ("Yahoo Finance is rate-limiting this server, which is common on shared cloud hosts. "
                "Wait a minute and click Run audit again. Data that was fetched successfully is cached for an hour.")
    return f"The analysis could not be completed. {text}"


def macro_inputs():
    """Sidebar inputs shared by the rate links, the stress tests and the macro panel. The boxes show percent; the
    returned dict holds fractions (None = left blank)."""
    frac = lambda v: None if v is None else v / 100
    mc = {
        "erp": st.slider("Equity risk premium (%)", 3.0, 8.0, round(DEFAULT_ERP * 100, 2), 0.25, key="m_erp",
                         help="Added to the 10-year yield to get the required return. Published estimates run about 4% to 6%.") / 100,
        "g_us": st.slider("Long-run growth for the floor, US-dollar stocks (%)", 1.0, 5.0, round(DEFAULT_G_US * 100, 2), 0.25,
                          key="m_gus", help="Used only when the exit-multiple floor is rate-linked. Roughly long-run nominal growth.") / 100,
        "g_in": st.slider("Long-run growth for the floor, Indian stocks (%)", 2.0, 8.0, round(DEFAULT_G_IN * 100, 2), 0.25,
                          key="m_gin", help="Higher than the US figure because Indian inflation and nominal growth are higher.") / 100,
        "shock": st.slider("Rate rise for the stress test (percentage points)", 0.5, 4.0, round(DEFAULT_SHOCK * 100, 2), 0.5,
                           key="m_shock", help="Used by the interest-cover stress test.") / 100,
    }
    st.markdown("**Typed-in figures** (leave blank where not needed)")
    mc["us_y10"] = frac(st.number_input(
        "US 10-year yield override (%)", min_value=0.1, max_value=25.0, value=None, step=0.05, format="%.2f", key="m_us10",
        placeholder="blank = use live data", help="Overrides the live yield, for example if the live fetch fails."))
    mc["in_y10"] = frac(st.number_input(
        "India 10-year government bond yield (%)", min_value=0.1, max_value=25.0, value=None, step=0.05, format="%.2f",
        key="m_in10", placeholder="not set", help="Needed for the rate links on Indian stocks. Check the latest figure."))
    mc["in_repo"] = frac(st.number_input(
        "India repo rate (%)", min_value=0.0, max_value=25.0, value=None, step=0.05, format="%.2f", key="m_repo",
        placeholder="not set", help="Shown in the macro backdrop only."))
    mc["in_cpi"] = frac(st.number_input(
        "India CPI inflation, latest year on year (%)", min_value=-5.0, max_value=30.0, value=None, step=0.1, format="%.1f",
        key="m_incpi", placeholder="not set", help="Shown in the macro backdrop only."))
    return mc


def sidebar():
    sb = st.sidebar
    sb.header("Configuration")
    mode = sb.radio("Evaluation mode", [MODE_PUBLIC, MODE_VENTURE, MODE_MACRO])
    cfg = {"mode": mode}
    if mode == MODE_PUBLIC:
        cfg["ticker"] = sb.text_input(
            "Ticker", value="NVDA", help="US: AAPL. India NSE: RELIANCE.NS. India BSE: 500325.BO."
        ).strip().upper()
        cfg["loss_handling"] = sb.selectbox(
            "If trailing net income is zero or negative", LOSS_OPTIONS,
            help=f"Auto sends loss-makers with revenue growth of {ROUTE_GROWTH_MIN:.0%} or more to the venture lens. "
                 "Other loss-makers stay in the screen, where a hard gate caps them at Weak.")
        cfg["allow_excluded"] = sb.checkbox(
            "Run anyway for banks, insurers and REITs", value=False,
            help="The rubric does not fit these sectors. Results will be unreliable.")
        with sb.expander("Valuation assumptions"):
            cfg["mos"] = st.slider("Margin of safety", 0.05, 0.50, 0.20, 0.05)
            cfg["req_return"] = st.slider("Required annual return", 0.08, 0.20, 0.10, 0.01)
            cfg["growth_basis"] = st.selectbox("Growth basis", list(GROWTH_BASES))
            cfg["max_growth"] = st.slider("Maximum growth assumed", 0.05, 0.40, 0.20, 0.01)
            cfg["target_peg"] = st.slider("Target PEG for the exit multiple", 0.8, 2.5, 1.5, 0.1)
            cfg["max_pe"] = st.slider("Maximum exit P/E", 12.0, 45.0, 30.0, 1.0)
        with sb.expander("Macro overlay (optional)"):
            st.caption("Everything here is off by default. With both boxes unticked, scores and the forward valuation "
                       "are exactly as before.")
            cfg["link_r"] = st.checkbox(
                "Tie the required return to the 10-year yield", value=False, key="link_r",
                help="Required return = 10-year government yield + equity risk premium. US-dollar stocks use the US yield "
                     "(live, or typed in below); Indian stocks use the India yield typed in below. The fixed slider "
                     "above is the fallback when no yield is available.")
            cfg["link_floor"] = st.checkbox(
                "Tie the exit-multiple floor to rates", value=False, key="link_floor",
                help=f"Replaces the fixed {MIN_PE:.0f}x floor with 1 / (required return - long-run growth), kept between "
                     f"{FLOOR_PE_MIN:.0f}x and {FLOOR_PE_MAX:.0f}x.")
            cfg["macro"] = macro_inputs()
            cfg["reg_level"] = st.selectbox(
                "Regulatory or policy exposure (your view)", REG_LEVELS, key=f"reg_level_{cfg['ticker']}",
                help="Shown in the stress tests for this ticker. Never scored.")
            cfg["reg_note"] = st.text_input("Regulation note (optional)", value="", max_chars=140,
                                            key=f"reg_note_{cfg['ticker']}")
        with sb.expander("Sector & market context (optional)"):
            st.caption("Off by default. Adds a tab with the stock's sector against the market, trend health, how the sector "
                       "held up in past sell-offs, an all-sector leaderboard, headlines and a research checklist. "
                       "Information only: the rating never changes.")
            cfg["show_context"] = st.checkbox(
                "Show the sector & market context tab", value=False, key="show_ctx",
                help="Fetches price history for the stock, its sector and the market from Yahoo Finance when you click Run audit.")
            cfg["ctx_board"] = st.checkbox(
                "Include the all-sector leaderboard", value=True, key="ctx_board",
                help="Ranks every sector by recent performance. Fetches about ten more price series on the first run "
                     "(then cached for three hours); untick it if Yahoo is rate-limiting you.")
            cfg["ctx_proxy"] = st.text_input(
                "Compare with this fund or index (optional)", value="", max_chars=20, key=f"ctx_proxy_{cfg['ticker']}",
                help="Blank = chosen from Yahoo's sector (US: the Select Sector SPDR funds; India: NSE sector indexes). "
                     "For a narrower theme type a Yahoo symbol, for example XRT (US retail) or SMH (semiconductors).",
            ).strip().upper()
            cfg["ctx_date"] = st.text_input(
                "Catalyst date (optional, YYYY-MM-DD)", value="", max_chars=10, key=f"ctx_date_{cfg['ticker']}",
                help="If the stock moved on news, enter the date to see how far the stock, its sector and the market have "
                     "moved since then, and how much of the move is still held. It also starts the filings list from "
                     "that date.").strip()
            cfg["ctx_alloc"] = st.checkbox(
                "Include capital-allocation numbers", value=True, key="ctx_alloc",
                help="Asset growth, capital spending against depreciation, cash paid for acquisitions, goodwill, debt "
                     "and share-count changes, worked out from the annual statements the app has already loaded. "
                     "No extra fetching.")
            cfg["ctx_filings"] = st.checkbox(
                "Include recent SEC filings (US companies)", value=True, key="ctx_filings",
                help="Lists the company's recent 8-K reports (agreements, completed acquisitions, equity sales, officer "
                     "changes and so on) from SEC EDGAR. Nothing is fetched until you give a contact email below.")
            cfg["sec_contact"] = st.text_input(
                "Contact email for the SEC (needed for filings)", value="", max_chars=100, key="sec_contact",
                help="The SEC asks every automated request to carry a contact email. It is sent to the SEC with each "
                     "request and nowhere else, and is kept only for your current session. You can also set SEC_CONTACT "
                     "in the app's secrets.").strip()
    elif mode == MODE_MACRO:
        sb.caption("Shows US and India readings side by side. US data loads automatically. For India, type the bond "
                   "yield, policy rate and inflation in below.")
        with sb.expander("Assumptions and typed-in figures", expanded=True):
            cfg["macro"] = macro_inputs()
    else:
        cfg["source"] = sb.radio("Data source", [SRC_MANUAL, SRC_TICKER])
        if cfg["source"] == SRC_TICKER:
            cfg["ticker"] = sb.text_input("Ticker of a loss-making or growth company", value="CRWV").strip().upper()
            cfg["nrr"] = sb.number_input("Net revenue retention % (0 = unknown)", 0, 200, 0, 5)
            cfg["tam"] = sb.selectbox("TAM (your judgement, annual USD-equivalent)", TAM_CHOICES,
                                      index=len(TAM_CHOICES) - 1)
        else:
            cfg["name"] = sb.text_input("Company name", value="My SaaS Venture").strip()
            cfg["sym"] = sb.selectbox("Currency symbol", ["$", "₹", "€", "£"])
            cfg["arr"] = sb.number_input("Current ARR / revenue (millions)", min_value=0.1, value=10.0, step=1.0)
            cfg["growth"] = sb.slider("YoY growth (%)", -20, 400, 85, 5)
            cfg["gm"] = sb.slider("Gross margin (%)", 10, 95, 75, 5)
            cfg["nrr"] = sb.slider("Net revenue retention (%)", 70, 160, 115, 5)
            cfg["tam"] = sb.selectbox("TAM (annual USD-equivalent)", TAM_CHOICES, index=0)
            cfg["cash"] = sb.number_input("Cash on hand (millions)", min_value=0.0, value=12.0, step=1.0)
            cfg["burn"] = sb.number_input("Annual net burn (millions; negative = cash-generative)", value=6.0, step=1.0)
        with sb.expander("Projection assumptions"):
            cfg["fade"] = st.slider("Growth fade per year", 0.5, 1.0, DEFAULT_FADE, 0.05,
                                    help="Growth in year t = starting growth x fade^t.")
            cfg["cost_ratio"] = st.slider("Cost growth as a share of revenue growth", 0.2, 1.0, DEFAULT_COST_RATIO, 0.05,
                                          help="Lower means more operating leverage.")
    clicked = sb.button("Load backdrop 🌍" if mode == MODE_MACRO else "Run audit 🚀", type="primary")
    sb.caption("Screening tool for research and education. Not investment advice.")
    return cfg, clicked


def load(ticker):
    if not ticker:
        raise DataError("Enter a ticker symbol in the sidebar, then click Run audit.")
    with st.spinner(f"Fetching Yahoo Finance data for {ticker}..."):
        return fetch_snapshot(ticker)


def run_public(cfg):
    snap = load(cfg["ticker"])
    m = extract_public_metrics(snap)
    try:
        m["stress"] = stress_inputs(snap, m)
    except Exception:  # noqa: BLE001 - the stress tests are an optional extra: never let them stop the screen
        m["stress"] = None
    if cfg.get("show_context"):
        try:
            m["ctx_info"] = ctx_info(snap)
        except Exception:  # noqa: BLE001 - same rule for the context tab
            m["ctx_info"] = None
        if cfg.get("ctx_alloc", True):
            try:
                m["ctx_alloc"] = capital_allocation(snap)
            except Exception:  # noqa: BLE001 - same rule again
                m["ctx_alloc"] = {"dates": [], "values": {}, "acq3": None, "glance": [],
                                  "notes": ["The capital-allocation figures could not be worked out from the data Yahoo "
                                            "returned."]}
    rule = sector_rule(m["sector"], m["industry"])
    if rule and rule[0] == "exclude" and not cfg["allow_excluded"]:
        render_excluded(m, rule[1])
        return
    if m["ni_ttm"] is not None and m["ni_ttm"] <= 0:
        growth = coalesce(m["rev_growth_yoy"], m["rev_cagr"])
        choice = cfg["loss_handling"]
        if choice == LOSS_VENTURE:
            why = "the sidebar is set to always use the venture lens"
            to_venture = True
        elif choice == LOSS_AUTO and growth is not None and growth >= ROUTE_GROWTH_MIN:
            why = f"revenue is growing {growth * 100:.0f}%"
            to_venture = True
        else:
            to_venture = False
        if to_venture:
            say("warning", f"**Routed to the venture lens.** {m['name']} has negative trailing net income and {why}, "
                           "so profit-based metrics do not apply. Switch to venture mode in the sidebar to add NRR, "
                           "TAM or change the projection assumptions.")
            render_venture(venture_inputs_from_snapshot(snap), DEFAULT_FADE, DEFAULT_COST_RATIO)
            return
        if choice == LOSS_SCREEN:
            say("warning", "**Trailing net income is negative.** The sidebar is set to always run the quality screen, "
                           "so the loss-making gate caps the result at Weak.")
        else:
            say("warning", "**Trailing net income is negative and growth is below the venture-routing threshold "
                           f"({ROUTE_GROWTH_MIN:.0%}).** The quality screen runs anyway, and the loss-making gate "
                           "caps the result at Weak.")
    render_public(m, cfg)


def run_venture(cfg):
    if cfg["source"] == SRC_TICKER:
        snap = load(cfg["ticker"])
        vi = venture_inputs_from_snapshot(
            snap,
            nrr=cfg["nrr"] / 100 if cfg["nrr"] else None,
            tam=None if cfg["tam"] == TAM_UNKNOWN else cfg["tam"],
        )
    else:
        vi = {
            "name": cfg["name"] or "Startup", "ticker": None, "sym": cfg["sym"], "source": "manual",
            "fetched_at": None, "revenue": cfg["arr"], "growth": cfg["growth"] / 100,
            "growth_src": "User input", "gross_margin": cfg["gm"] / 100, "nrr": cfg["nrr"] / 100,
            "tam": None if cfg["tam"] == TAM_UNKNOWN else cfg["tam"],
            "cash": cfg["cash"], "debt": None, "burn": cfg["burn"],
        }
    render_venture(vi, cfg["fade"], cfg["cost_ratio"])


def run_macro(cfg):
    mc = cfg["macro"]
    with st.spinner("Fetching US and India market data (the first load can take about ten seconds)..."):
        data = collect_macro(mc)
    show_macro_panel(data, mc)


def main():
    st.title("🛡️ Anti-Fragile Stock & Startup Screener")
    st.markdown(
        "A **15-pillar screen** for profitable listed companies and a **venture lens** for pre-profit and growth "
        "companies. Missing data is shown as *n/a* and left out of the score. It is never invented. An optional "
        "**macro overlay** (rate links, stress tests and a US and India backdrop) and an optional **sector & market "
        "context** tab (with capital-allocation numbers and recent SEC filings) are off by default."
    )
    cfg, clicked = sidebar()
    if clicked:
        st.session_state["active_cfg"] = cfg
    active = st.session_state.get("active_cfg")

    if not active:
        say("info", "👈 Choose a mode and a target in the sidebar, then click the button at the bottom of the sidebar.")
    else:
        if active != cfg:
            st.caption("Sidebar settings changed since the last run. Click the button again to refresh the results.")
        try:
            if active["mode"] == MODE_PUBLIC:
                run_public(active)
            elif active["mode"] == MODE_MACRO:
                run_macro(active)
            else:
                run_venture(active)
        except DataError as exc:
            say("error", str(exc))
        except Exception as exc:  # noqa: BLE001 - show any data or network problem instead of a blank page
            say("error", explain_error(exc))
            with st.expander("Technical details"):
                st.exception(exc)

    st.divider()
    with st.expander("Methodology and limits"):
        st.markdown(
            "- **Scoring:** each pillar scores 1 to 5 against fixed thresholds. The composite is the weighted average "
            "of pillars that have data; missing pillars are left out and the remaining weights are rescaled.\n"
            f"- **Coverage rule:** a result needs at least {MIN_COVERAGE_PUBLIC:.0%} of pillar weight to have data "
            f"({MIN_COVERAGE_VENTURE:.0%} in the venture lens).\n"
            f"- **Result bands:** Strong at {STRONG_MIN} or more, Mixed from {MIXED_MIN}, Weak below. "
            "A hard safety gate forces Weak and a soft gate caps at Mixed. These cut-offs are uncalibrated: "
            "run a set of known compounders, value traps and blow-ups through the screen before trusting them.\n"
            "- **Not sector-adjusted:** margin thresholds are absolute. Banks, insurers and REITs are blocked by "
            "default; utilities and cyclicals carry a caution.\n"
            "- **Forward valuation:** a transparent illustration built from conservative, capped growth, an exit "
            "multiple that can shrink but never expands, and a margin of safety. It is deliberately harsh on "
            "high-multiple growth stocks. Analyst targets are shown for reference and never used.\n"
            "- **Macro overlay (optional, off by default):** the rate links change only the required return and the "
            "exit-multiple floor inside the illustrative forward valuation, never a pillar score. The stress tests and "
            "the macro backdrop are information only, and regulation is a flag you set yourself. The caution rules and "
            "cut-offs are rules of thumb that have not been tested across market regimes.\n"
            "- **Sector & market context (optional, off by default):** a separate tab with the sector against the "
            "market, trend health, how the sector held up in past sell-offs, an all-sector leaderboard, headlines, "
            "ownership figures and a research checklist. It is information only and never changes a score, a label or "
            "a gate. In a three-year back-test on about 50 large US companies, sector trend and defensive-versus-"
            "cyclical leadership showed no reliable edge (the sample was small), so treat the tab as background for "
            "your own research.\n"
            "- **Capital allocation and company filings (inside that tab):** asset growth, capital spending against "
            "depreciation, cash paid for acquisitions, goodwill, debt and share-count changes from the annual "
            "statements, and a US company's recent SEC 8-K filings with their item codes (it needs a contact email, "
            "which the SEC asks every automated request to carry). Information only: neither changes a score, a label "
            "or a gate. Research on US companies has linked heavy investment, fast asset growth and share-financed "
            "acquisitions to weaker average returns, but those findings come from older samples, are disputed in "
            "places and have tended to weaken once published, so the figures are shown for your own due diligence "
            "and not scored.\n"
            "- **Venture projection:** revenue growth fades each year while the cost base grows more slowly, "
            "which gives a breakeven year and a funding gap. It is a what-if tool, not a forecast.\n"
            "- **Data:** Yahoo Finance via yfinance is unofficial and can be incomplete or delayed. "
            "Compare the *Inputs used* tab with the company's filings."
        )
    st.caption(DISCLAIMER)
    st.caption(f"App version {APP_VERSION}.")


if __name__ == "__main__":
    main()
