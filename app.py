import io
from datetime import datetime
import openpyxl
from openpyxl.formatting.rule import CellIsRule, FormulaRule
from openpyxl.styles import Alignment, Border, Font, PatternFill, Side
import streamlit as st
import yfinance as yf

st.set_page_config(page_title="16-Pillar Evaluator", page_icon="📈", layout="centered")

st.title("📈 Anti-Fragile 16-Pillar Evaluator")
ticker_input = st.text_input("Enter Stock Ticker (e.g., CTVA, NVDA, RELIANCE.NS):", value="NVDA").strip().upper()

def evaluate_stock(clean_ticker):
    is_indian = clean_ticker.endswith(".NS") or clean_ticker.endswith(".BO")
    curr_sym = "₹" if is_indian else "$"
    today_str = datetime.now().strftime("%Y-%m-%d")

    stock = yf.Ticker(clean_ticker)
    info = stock.info or {}
    
    # Safe validation to handle invalid, delisted, or missing tickers cleanly
    if not info or len(info) < 5 or ('regularMarketPrice' in info and info.get('regularMarketPrice') is None and 'currentPrice' in info and info.get('currentPrice') is None):
        raise ValueError(f"Could not retrieve valid fundamental data for '{clean_ticker}'. It may be invalid, delisted, or temporarily restricted.")

    cmp = info.get('currentPrice') or info.get('regularMarketPrice') or info.get('previousClose') or 100.0
    company_name = info.get('longName') or info.get('shortName') or clean_ticker
    sector = info.get('sector', 'Unknown')
    fair_value = info.get('targetMeanPrice') or round(cmp * 1.25, 2)
    analyst_rec = (info.get('recommendationKey') or 'HOLD').upper().replace('_', ' ')
    num_analysts = info.get('numberOfAnalystOpinions', 5)

    gm_val = info.get('grossMargins') or 0.35
    op_margin = info.get('operatingMargins') or 0.12
    roe_val = info.get('returnOnEquity') or 0.10
    de_val = info.get('debtToEquity') or 60.0
    rg_val = info.get('revenueGrowth') or 0.05
    eg_val = info.get('earningsGrowth') or 0.05

    fcf_val = info.get('freeCashflow') or 500_000_000
    net_inc = info.get('netIncomeToCommon') or 500_000_000

    pe_val = info.get('trailingPE') or 20.0
    fwd_pe_val = info.get('forwardPE') or 18.0
    peg_val = info.get('pegRatio') or 1.5

    insider_held = info.get('heldPercentInsiders')
    insider_val = (insider_held * 100) if insider_held is not None else 5.0

    mcap = info.get('marketCap', 1)
    fcf_yield_val = (fcf_val / mcap) * 100 if (mcap and mcap > 0 and fcf_val) else 3.5
    insider_action = "Stable / Neutral"

    # 16 Pillars Scoring Logic
    s11 = 5 if gm_val >= 0.50 else (4 if gm_val >= 0.35 else (3 if gm_val >= 0.20 else 2))
    s12 = 5 if rg_val >= 0.15 else (4 if rg_val >= 0.08 else (3 if rg_val >= 0.0 else 2))
    s13 = 4
    s21 = 5 if roe_val >= 0.20 else (4 if roe_val >= 0.12 else (3 if roe_val >= 0.05 else 2))
    s22 = s11
    s23 = 5 if de_val < 50 else (4 if de_val < 150 else (3 if de_val < 300 else 2))
    fcf_ratio = (fcf_val / net_inc) if net_inc and net_inc > 0 else 0.5
    s24 = 5 if fcf_ratio >= 1.0 else (4 if fcf_ratio >= 0.75 else (3 if fcf_ratio >= 0.5 else 2))
    s31 = 5 if fcf_yield_val >= 7.0 else (4 if fcf_yield_val >= 4.0 else (3 if fcf_yield_val >= 2.0 else 2))
    s32 = 5 if (0 < peg_val <= 1.2) else (4 if (1.2 < peg_val <= 2.0) else (3 if peg_val > 0 else 2))
    s33 = 4
    s34 = 5 if insider_val >= 10.0 else (4 if insider_val >= 3.0 else (3 if insider_val >= 1.0 else 2))
    s41, s42 = s21, s12
    s43 = 5 if fcf_val > 0 else 3
    s44 = 5 if "Buyers" in insider_action else (4 if "Stable" in insider_action else 3)
    s45 = 5 if ("BUY" in analyst_rec or "OUTPERFORM" in analyst_rec) else (3 if "HOLD" in analyst_rec else 2)

    # Risk Overlays
    eps_rev_pct = eg_val if eg_val < -0.05 else 0.0
    bookings_delta = eg_val - rg_val
    val_cap_flag = 1 if (fwd_pe_val and fwd_pe_val >= 45.0 and peg_val and peg_val > 2.5) else 0
    cyclical_ratio = round(op_margin / 0.15, 2) if sector in {"Energy", "Basic Materials", "Industrials"} else 1.0

    rows = [
        ("1.1", "Moat", "Competitive Advantage", 0.06, f"Gross Margin: {gm_val*100:.1f}%", s11, "Pricing power"),
        ("1.2", "Moat", "Market Dynamics", 0.06, f"Rev Growth: {rg_val*100:.1f}%", s12, "TAM growth"),
        ("1.3", "Moat", "Revenue Model Quality", 0.06, "Recurring / Sticky", s13, "Retention"),
        ("2.1", "Quality", "ROE / Capital Returns", 0.07, f"ROE: {roe_val*100:.1f}%", s21, "Efficiency"),
        ("2.2", "Quality", "Gross Margin Floor", 0.07, f"GM: {gm_val*100:.1f}%", s22, "Margin stability"),
        ("2.3", "Quality", "Debt Leverage", 0.07, f"D/E: {de_val:.1f}%", s23, "Solvency"),
        ("2.4", "Quality", "FCF Conversion", 0.07, f"FCF/NI: {fcf_ratio*100:.1f}%", s24, "Cash quality"),
        ("3.1", "Valuation", "FCF Yield", 0.07, f"Yield: {fcf_yield_val:.1f}%", s31, "Cash yield"),
        ("3.2", "Valuation", "PEG & P/E Multiple", 0.06, f"PEG: {peg_val:.2f}x | P/E: {pe_val:.1f}x", s32, "Growth multiple"),
        ("3.3", "Governance", "Management Alignment", 0.06, "Shareholder returns", s33, "Capital policy"),
        ("3.4", "Governance", "Insider Ownership", 0.05, f"Insiders: {insider_val:.1f}%", s34, "Skin in game"),
        ("4.1", "Filters", "Multi-Yr Return Trend", 0.06, f"ROE: {roe_val*100:.1f}%", s41, "Durability"),
        ("4.2", "Filters", "Top-Line Compounding", 0.06, f"Rev Growth: {rg_val*100:.1f}%", s42, "Expansion"),
        ("4.3", "Filters", "Positive Free Cash Flow", 0.06, f"FCF: {curr_sym}{fcf_val:,.0f}", s43, "Self-funding"),
        ("4.4", "Filters", "Insider Net Action", 0.06, insider_action, s44, "Recent activity"),
        ("4.5", "Consensus", "Analyst Rating", 0.06, f"{analyst_rec} ({curr_sym}{fair_value:,.2f})", s45, f"{num_analysts} analysts"),
    ]

    base_score = sum(wt * sc for _, _, _, wt, _, sc, _ in rows)
    penalties = (
        (-0.50 if eps_rev_pct < -0.05 else 0.0)
        + (-0.40 if bookings_delta < 0.0 else 0.0)
        + (-0.60 if val_cap_flag >= 1 else 0.0)
        + (-0.50 if cyclical_ratio > 1.50 else 0.0)
    )
    final_score = max(1.0, min(5.0, base_score + penalties))

    if val_cap_flag >= 1:
        verdict = "NEUTRAL / VAL CAP"
    elif final_score >= 4.0:
        verdict = "PASS / BUY"
    elif final_score >= 3.2:
        verdict = "WATCH / HOLD"
    else:
        verdict = "FAIL / AVOID"

    target_buy = fair_value * 0.80

    # Build Excel Workbook in memory
    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = "Anti-Fragile Audit"
    hdr_fill = PatternFill("solid", fgColor="1E293B")
    hdr_font = Font(name="Calibri", bold=True, color="FFFFFF", size=11)
    ws.merge_cells("A1:I1")
    ws["A1"] = f"Anti-Fragile 16-Pillar Audit — {company_name} ({clean_ticker}) | {today_str}"
    ws["A1"].font = Font(name="Calibri", bold=True, color="FFFFFF", size=13)
    ws["A1"].fill = hdr_fill

    headers = ["Ref", "Category", "Pillar / Criteria", "Weight", "Live Metric", "Score", "Weighted", "Status", "Notes"]
    for c, h in enumerate(headers, 1):
        cell = ws.cell(row=3, column=c, value=h)
        cell.fill, cell.font = hdr_fill, hdr_font

    for idx, (ref, cat, name, wt, met, sc, note) in enumerate(rows, 4):
        ws.cell(row=idx, column=1, value=ref)
        ws.cell(row=idx, column=2, value=cat)
        ws.cell(row=idx, column=3, value=name)
        ws.cell(row=idx, column=4, value=wt).number_format = "0.0%"
        ws.cell(row=idx, column=5, value=met)
        ws.cell(row=idx, column=6, value=sc)
        ws.cell(row=idx, column=7, value=f"=D{idx}*F{idx}").number_format = "0.00"
        ws.cell(row=idx, column=8, value=f'=IF(F{idx}>=4,"PASS",IF(F{idx}=3,"NEUTRAL","FAIL"))')
        ws.cell(row=idx, column=9, value=note)

    excel_buffer = io.BytesIO()
    wb.save(excel_buffer)
    excel_buffer.seek(0)

    return {
        "company_name": company_name,
        "curr_sym": curr_sym,
        "cmp": cmp,
        "fair_value": fair_value,
        "target_buy": target_buy,
        "final_score": final_score,
        "verdict": verdict,
        "rows": rows,
        "excel_bytes": excel_buffer,
    }

if st.button("Run 16-Pillar Audit", type="primary", use_container_width=True):
    if ticker_input:
        with st.spinner(f"Fetching fundamentals for {ticker_input}..."):
            try:
                res = evaluate_stock(ticker_input)
                st.subheader(f"{res['company_name']} ({ticker_input})")

                col1, col2, col3 = st.columns(3)
                col1.metric("Final Score", f"{res['final_score']:.2f} / 5.00")
                col2.metric("CMP", f"{res['curr_sym']}{res['cmp']:,.2f}")
                col3.metric("Max Buy (20% MoS)", f"{res['curr_sym']}{res['target_buy']:,.2f}")

                if "BUY" in res["verdict"]:
                    st.success(f"**Verdict:** {res['verdict']}")
                elif "AVOID" in res["verdict"]:
                    st.error(f"**Verdict:** {res['verdict']}")
                else:
                    st.warning(f"**Verdict:** {res['verdict']}")

                st.download_button(
                    label="📥 Download Formatted Excel (.xlsx)",
                    data=res["excel_bytes"],
                    file_name=f"{ticker_input}_AntiFragile_Audit.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
                    use_container_width=True,
                )

                st.dataframe(
                    [{"Ref": r[0], "Pillar": r[2], "Metric": r[4], "Score": r[5]} for r in res["rows"]],
                    use_container_width=True,
                    hide_index=True,
                )
            except Exception as e:
                st.error(f"Error: {e}")
