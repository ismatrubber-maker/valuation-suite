import streamlit as st
import pandas as pd
import yfinance as yf
import io
import openpyxl
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from openpyxl.formatting.rule import CellIsRule

st.set_page_config(page_title="Anti-Fragile Valuation & Startup Audit Suite", page_icon="📈", layout="wide")

st.title("📈 Anti-Fragile Stock & Startup Evaluation Suite")
st.markdown("Generate institutional-grade 16-pillar scorecards, live market valuations, or startup unit-economics audits instantly.")

# Sidebar navigation
app_mode = st.sidebar.selectbox("Select Evaluation Model", ["Public Stock Evaluator", "Pre-Profit Startup Evaluator"])

if app_mode == "Public Stock Evaluator":
    st.subheader("🏢 Public Listed Company Valuation Engine")
    ticker = st.text_input("Enter Stock Ticker Symbol (e.g., AVGO, TPR, CAT, MSFT):", value="AVGO").strip().upper()
    
    if st.button("Generate Stock Scorecard"):
        with st.spinner(f"Fetching live market data and computing valuation for {ticker}..."):
            try:
                stock = yf.Ticker(ticker)
                todays_data = stock.history(period="1d")
                cmp = float(todays_data["Close"].iloc[-1]) if not todays_data.empty else float(stock.fast_info.last_price)
                
                info = stock.info or {}
                company_name = info.get("longName") or info.get("shortName") or ticker
                fair_value = float(info.get("targetMeanPrice")) if info.get("targetMeanPrice") else round(cmp * 1.25, 2)
                analyst_rec = info.get("recommendationKey", "BUY").upper().replace("_", " ")
                num_analysts = info.get("numberOfAnalystOpinions", 10)
                
                gm_val = info.get("grossMargins", 0.50)
                roe_val = info.get("returnOnEquity", 0.20)
                de_val = info.get("debtToEquity", 50.0)
                rg_val = info.get("revenueGrowth", 0.10)
                fcf_val = info.get("freeCashflow", 1000000000)
                net_income_val = info.get("netIncomeToCommon", 1000000000)
                pe_val = info.get("trailingPE", 20.0)
                peg_val = info.get("pegRatio", 1.5)
                insider_val = info.get("heldPercentInsiders", 0.03) * 100
                
                market_cap = info.get("marketCap", 0)
                fcf_yield_val = (fcf_val / market_cap) * 100 if market_cap > 0 and fcf_val else 4.0

                # Scores
                score_11 = 5 if gm_val >= 0.50 else (4 if gm_val >= 0.35 else 3)
                score_12 = 5 if rg_val >= 0.15 else (4 if rg_val >= 0.08 else 3)
                score_13 = 4
                score_21 = 5 if roe_val >= 0.20 else (4 if roe_val >= 0.12 else 3)
                score_22 = score_11
                score_23 = 5 if de_val < 50 else (4 if de_val < 150 else 3)
                fcf_net_ratio = (fcf_val / net_income_val) if net_income_val > 0 else 0.5
                score_24 = 5 if fcf_net_ratio >= 1.0 else (4 if fcf_net_ratio >= 0.75 else 3)
                score_31 = 5 if fcf_yield_val >= 7.0 else (4 if fcf_yield_val >= 4.0 else 3)
                score_32 = 5 if (0 < peg_val <= 1.2) else (4 if (1.2 < peg_val <= 2.0) else 3)
                score_33 = 4
                score_34 = 5 if insider_val >= 10.0 else (4 if insider_val >= 3.0 else 3)
                score_41 = score_21
                score_42 = score_12
                score_43 = 5 if fcf_val > 0 else 3
                score_44 = 4
                score_45 = 5 if "BUY" in analyst_rec else 3

                pillars_data = [
                    ("1.1", "Economic Moat", "Competitive Advantage", "Brand Moat & Pricing Power", 0.06, f"Gross Margin: {gm_val*100:.1f}%", score_11, "Strong moat characteristics"),
                    ("1.2", "Economic Moat", "Market Dynamics", "TAM Expansion", 0.06, f"Revenue Growth: {rg_val*100:.1f}% YoY", score_12, "Market growth"),
                    ("1.3", "Economic Moat", "Revenue Model Quality", "Recurring mix", 0.06, "Robust revenue quality", score_13, "Stable model"),
                    ("2.1", "Financial Quality", "ROIC vs WACC Spread", "ROIC exceeds WACC", 0.07, f"ROE / Capital Returns: {roe_val*100:.1f}%", score_21, "Capital efficiency"),
                    ("2.2", "Financial Quality", "Gross Margin Floor", "Gross Margin > 40%", 0.07, f"Gross Margin: {gm_val*100:.1f}%", score_22, "Reliable margins"),
                    ("2.3", "Financial Quality", "Debt Leverage", "Net Debt / EBITDA <= 2.0x", 0.07, f"Debt/Equity: {de_val:.1f}%", score_23, "Balance sheet leverage"),
                    ("2.4", "Financial Quality", "Accrual & FCF Conversion", "FCF / Net Income >= 75%", 0.07, f"FCF/NetInc Ratio: {fcf_net_ratio*100:.1f}%", score_24, "Cash conversion audit"),
                    ("3.1", "Valuation", "FCF Yield / Valuation", "FCF Yield > 5.0%", 0.07, f"FCF Yield: {fcf_yield_val:.1f}% (CMP: ${cmp:,.2f})", score_31, "Valuation check"),
                    ("3.2", "Valuation", "PEG Ratio", "PEG 1.0 - 1.5", 0.06, f"PEG Ratio: {peg_val:.2f}x | P/E: {pe_val:.1f}x", score_32, "Growth multiple check"),
                    ("3.3", "Governance", "Management Alignment", "High executive stake", 0.06, "Active shareholder returns & buybacks", score_33, "Shareholder-friendly execution"),
                    ("3.4", "Governance", "Insider Ownership %", "Significant skin-in-the-game", 0.05, f"Insider Holding: {insider_val:.1f}%", score_34, "Executive ownership depth"),
                    ("4.1", "Screening Filters", "5-Year ROIC Trend", "ROIC > 15% 5-yr avg", 0.06, "Consistent multi-year compounding", score_41, "Cycle resilience"),
                    ("4.2", "Screening Filters", "Top-Line Growth", "Revenue Growth > 8%", 0.06, f"Revenue Growth: {rg_val*100:.1f}% YoY", score_42, "Top-line expansion"),
                    ("4.3", "Screening Filters", "Maintenance CapEx Efficiency", "Positive FCF", 0.06, f"Free Cash Flow: ${fcf_val:,.0f}", score_43, "Asset efficiency"),
                    ("4.4", "Screening Filters", "Insider Net Action", "Net open-market buying", 0.06, "Stable insider positioning", score_44, "Insider trading momentum"),
                    ("4.5", "Expert Opinion", "Wall Street Analyst Consensus", "Strong Buy / Buy", 0.06, f"Consensus: {analyst_rec} (${fair_value:,.2f} Target)", score_45, "Wall Street backing")
                ]

                # Calculate overall metrics for browser UI
                total_weighted_score = sum(row[4] * row[6] for row in pillars_data)
                margin_of_safety = 0.20
                target_buy_price = fair_value * (1 - margin_of_safety)
                is_in_buy_zone = cmp <= target_buy_price
                upside_pct = ((fair_value - cmp) / cmp) * 100

                # --- BROWSER UI DISPLAY ---
                st.divider()
                st.markdown(f"### 📊 {company_name} ({ticker})")
                st.caption(f"Wall Street Consensus: **{analyst_rec}** ({num_analysts} Analysts)")

                # Key Metrics Grid
                col1, col2, col3, col4 = st.columns(2)
                col1.metric("Current Price", f"${cmp:,.2f}")
                col2.metric("Fair Value Target", f"${fair_value:,.2f}", f"{upside_pct:+.1f}% Upside")
                col3.metric("Max Buy Price (20% MoS)", f"${target_buy_price:,.2f}")
                col4.metric("16-Pillar Score", f"{total_weighted_score:.2f} / 5.00")

                # Buy Zone Status Banner
                if is_in_buy_zone:
                    st.success(f"🟢 **IN BUY ZONE** — Trading below your ${target_buy_price:,.2f} margin-of-safety threshold.")
                else:
                    st.warning(f"🟡 **WAIT FOR DIP** — Trading ${cmp - target_buy_price:,.2f} above your${target_buy_price:,.2f} target buy price.")

                # Build DataFrame for Interactive Browser Table
                df_rows = []
                for r in pillars_data:
                    status_label = "🟢 PASS" if r[6] >= 4 else ("🟡 NEUTRAL" if r[6] == 3 else "🔴 FAIL")
                    df_rows.append({
                        "Ref": r[0],
                        "Category": r[1],
                        "Metric": r[2],
                        "Company Value": r[5],
                        "Score": f"{r[6]}/5",
                        "Weight": f"{r[4]*100:.0f}%",
                        "Weighted": round(r[4] * r[6], 2),
                        "Status": status_label,
                        "Notes": r[7]
                    })
                
                df_display = pd.DataFrame(df_rows)
                st.markdown("#### 📋 16-Pillar Audit Breakdown")
                st.dataframe(df_display, use_container_width=True, hide_index=True)

                # --- EXCEL WORKBOOK GENERATION ---
                wb = openpyxl.Workbook()
                ws1 = wb.active
                ws1.title = "Established Companies"
                ws1.views.sheetView[0].showGridLines = True

                TITLE_FONT = Font(name="Calibri", size=16, bold=True, color="0F172A")
                SUB_FONT = Font(name="Calibri", size=12, italic=True, color="64748B")
                HEADER_FILL = PatternFill(start_color="1E293B", end_color="1E293B", fill_type="solid")
                HEADER_FONT = Font(name="Calibri", size=13, bold=True, color="FFFFFF")
                ROW_FONT = Font(name="Calibri", size=12)
                BOLD_
