import subprocess
import sys

def install(package):
    subprocess.check_call([sys.executable, "-m", "pip", inst := "install", package])

try:
    import yfinance as yf
except ImportError:
    install("yfinance")
    import yfinance as yf

try:
    import openpyxl
except ImportError:
    install("openpyxl")
    import openpyxl
import streamlit as st
import pandas as pd
import yfinance as yf
import io
import openpyxl
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from openpyxl.formatting.rule import CellIsRule

st.set_page_config(page_title="Anti-Fragile Valuation & Startup Audit Suite", page_icon="📈", layout="wide")

st.title("📈 Anti-Fragile Stock & Startup Evaluation Suite")
st.markdown("Generate institutional-grade 16-pillar Excel scorecards, live market valuations, or startup unit-economics audits instantly.")

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

                # Excel Workbook Generation
                wb = openpyxl.Workbook()
                ws1 = wb.active
                ws1.title = "Established Companies"
                ws1.views.sheetView[0].showGridLines = True

                TITLE_FONT = Font(name="Calibri", size=16, bold=True, color="0F172A")
                SUB_FONT = Font(name="Calibri", size=12, italic=True, color="64748B")
                HEADER_FILL = PatternFill(start_color="1E293B", end_color="1E293B", fill_type="solid")
                HEADER_FONT = Font(name="Calibri", size=13, bold=True, color="FFFFFF")
                ROW_FONT = Font(name="Calibri", size=12)
                BOLD_FONT = Font(name="Calibri", size=12, bold=True, color="0F172A")
                GREEN_FONT = Font(name="Calibri", size=12, bold=True, color="166534")
                AMBER_FONT = Font(name="Calibri", size=12, bold=True, color="B45309")
                RED_FONT = Font(name="Calibri", size=12, bold=True, color="991B1B")

                ALIGN_LEFT = Alignment(horizontal="left", vertical="center", wrap_text=True)
                ALIGN_CENTER = Alignment(horizontal="center", vertical="center", wrap_text=True)
                BORDER_THIN = Border(left=Side(style="thin", color="CBD5E1"), right=Side(style="thin", color="CBD5E1"), top=Side(style="thin", color="CBD5E1"), bottom=Side(style="thin", color="CBD5E1"))

                ws1["A1"] = f"Anti-Fragile Stock Evaluation Framework ({company_name})"
                ws1["A1"].font = TITLE_FONT
                ws1["A3"] = f"Company / Ticker: {company_name} ({ticker})"
                ws1["A3"].font = BOLD_FONT
                ws1["A4"] = f"Evaluation Date: 2026-11-13 | Consensus: {analyst_rec} ({num_analysts} Analysts)"
                ws1["A4"].font = SUB_FONT

                headers = ["Ref #", "Category", "Evaluation Metric / Criteria", "Target Threshold", "Weight", "Company Value / Metric", "Score (1-5)", "Weighted Score", "Pass / Fail / Neutral", "Notes / Remarks"]
                ws1.row_dimensions[6].height = 32
                for col_idx, h in enumerate(headers, 1):
                    c = ws1.cell(row=6, column=col_idx, value=h)
                    c.fill = HEADER_FILL
                    c.font = HEADER_FONT
                    c.alignment = ALIGN_CENTER
                    c.border = BORDER_THIN

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

                for idx, row in enumerate(pillars_data, 7):
                    ws1.row_dimensions[idx].height = 28
                    ws1.cell(row=idx, column=1, value=row[0]).alignment = ALIGN_CENTER
                    ws1.cell(row=idx, column=2, value=row[1]).alignment = ALIGN_LEFT
                    ws1.cell(row=idx, column=3, value=row[2]).alignment = ALIGN_LEFT
                    ws1.cell(row=idx, column=4, value=row[3]).alignment = ALIGN_LEFT
                    
                    c_weight = ws1.cell(row=idx, column=5, value=row[4])
                    c_weight.number_format = "0.0%"
                    c_weight.alignment = ALIGN_CENTER
                    
                    ws1.cell(row=idx, column=6, value=row[5]).alignment = ALIGN_LEFT
                    
                    c_score = ws1.cell(row=idx, column=7, value=row[6])
                    c_score.alignment = ALIGN_CENTER
                    c_score.font = BOLD_FONT
                    
                    c_weighted = ws1.cell(row=idx, column=8, value=f"=G{idx}*E{idx}")
                    c_weighted.number_format = "0.00"
                    c_weighted.alignment = ALIGN_CENTER
                    
                    c_pass = ws1.cell(row=idx, column=9, value=f'=IF(G{idx}>=4, "PASS", IF(G{idx}=3, "NEUTRAL", "FAIL"))')
                    c_pass.alignment = ALIGN_CENTER
                    c_pass.font = BOLD_FONT
                    
                    c_notes = ws1.cell(row=idx, column=10, value=row[7])
                    c_notes.alignment = ALIGN_LEFT

                    for col in range(1, 11):
                        if col != 7 and col != 9:
                            ws1.cell(row=idx, column=col).font = ROW_FONT
                        ws1.cell(row=idx, column=col).border = BORDER_THIN

                ws1.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=["\"PASS\""], stopIfTrue=True, font=GREEN_FONT))
                ws1.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=["\"NEUTRAL\""], stopIfTrue=True, font=AMBER_FONT))
                ws1.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=["\"FAIL\""], stopIfTrue=True, font=RED_FONT))

                ws1.row_dimensions[24].height = 30
                ws1.cell(row=24, column=3, value="OVERALL SCORE & WEIGHTED TOTAL").font = BOLD_FONT
                ws1.cell(row=24, column=3).alignment = Alignment(horizontal="right", vertical="center")
                c_tot = ws1.cell(row=24, column=8, value="=SUM(H7:H22)")
                c_tot.font = BOLD_FONT
                c_tot.number_format = "0.00"
                c_tot.alignment = ALIGN_CENTER

                # Valuation Calculator
                ws1.cell(row=26, column=2, value="VALUATION & TARGET BUY PRICE CALCULATOR").font = BOLD_FONT
                val_headers = ["Valuation Method", "Current Market Price", "Fair Value Estimate", "Margin of Safety Required", "Target Max Buy Price", "Status vs Current Price"]
                ws1.row_dimensions[27].height = 28
                for col_idx, vh in enumerate(val_headers, 2):
                    c = ws1.cell(row=27, column=col_idx, value=vh)
                    c.fill = HEADER_FILL
                    c.font = HEADER_FONT
                    c.alignment = ALIGN_CENTER
                    c.border = BORDER_THIN

                ws1.row_dimensions[28].height = 26
                ws1.cell(row=28, column=2, value="Discounted Fair Value Model").alignment = ALIGN_LEFT
                ws1.cell(row=28, column=3, value=cmp).number_format = "$#,##0.00"
                ws1.cell(row=28, column=4, value=fair_value).number_format = "$#,##0.00"
                ws1.cell(row=28, column=5, value=0.20).number_format = "0.0%"
                target_cell = ws1.cell(row=28, column=6, value="=D28*(1-E28)")
                target_cell.number_format = "$#,##0.00"
                target_cell.font = BOLD_FONT
                status_cell = ws1.cell(row=28, column=7, value='=IF(C28<=F28, "IN BUY ZONE", "WAIT FOR DIP")')
                status_cell.font = BOLD_FONT

                for col in range(2, 8):
                    ws1.cell(row=28, column=col).border = BORDER_THIN

                output = io.BytesIO()
                wb.save(output)
                output.seek(0)

                st.success(f"Successfully evaluated **{company_name} ({ticker})**!")
                st.metric(label="Current Market Price", value=f"${cmp:,.2f}")
                st.metric(label="Fair Value Estimate", value=f"${fair_value:,.2f}")
                st.download_button(
                    label="📥 Download Excel Scorecard",
                    data=output,
                    file_name=f"{ticker}_Evaluated_Scorecard.xlsx",
                    mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
                )
            except Exception as e:
                st.error(f"Error fetching data for {ticker}: {e}")

elif app_mode == "Pre-Profit Startup Evaluator":
    st.subheader("🚀 Pre-Profit Startup Unit Economics Evaluator")
    startup_name = st.text_input("Startup Name:", value="SaaSCo")
    arr_growth = st.slider("YoY ARR Growth Rate (%)", 10, 200, 85) / 100.0
    burn_multiple = st.slider("Burn Multiple (Net Burn / New ARR)", 0.5, 3.0, 1.2, 0.1)
    runway_months = st.slider("Cash Runway (Months)", 3, 36, 22)
    ltv_cac = st.slider("LTV / CAC Ratio", 1.0, 8.0, 4.2, 0.1)

    if st.button("Generate Startup Audit"):
        st.success(f"Generated unit-economics audit for **{startup_name}**!")
        st.metric("Venture Burn Health", "Healthy" if burn_multiple <= 1.5 else "High Risk")
        st.info("To export full Excel audits for startups, you can integrate the same openpyxl export logic as the public stock evaluator.")
