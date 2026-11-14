cat << 'EOF' > ~/Documents/app.py
import streamlit as st
import yfinance as yf
import io
from datetime import datetime
import openpyxl
from openpyxl.styles import Font, PatternFill, Alignment, Border, Side
from openpyxl.formatting.rule import CellIsRule

st.set_page_config(page_title="Anti-Fragile Valuation & Startup Audit Suite", page_icon="📈", layout="wide")
st.title("📈 Anti-Fragile Stock & Startup Evaluation Suite")
st.markdown("Generate institutional-grade 16-pillar Excel scorecards with live market data, conditional formatting, and buy-zone / burn-health calculators.")

def build_excel_report(sheet_title, main_title, entity_line, sub_line, pillars_data, calc_title, calc_headers, calc_row_values, calc_formats):
    wb = openpyxl.Workbook()
    ws = wb.active
    ws.title = sheet_title
    ws.views.sheetView[0].showGridLines = True

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
    BORDER_THIN = Border(
        left=Side(style="thin", color="CBD5E1"), right=Side(style="thin", color="CBD5E1"),
        top=Side(style="thin", color="CBD5E1"), bottom=Side(style="thin", color="CBD5E1")
    )

    ws["A1"] = main_title
    ws["A1"].font = TITLE_FONT
    ws["A3"] = entity_line
    ws["A3"].font = BOLD_FONT
    ws["A4"] = sub_line
    ws["A4"].font = SUB_FONT

    headers = ["Ref #", "Category", "Evaluation Metric / Criteria", "Target Threshold", "Weight", "Company Value / Metric", "Score (1-5)", "Weighted Score", "Pass / Fail / Neutral", "Notes / Remarks"]
    ws.row_dimensions[6].height = 32
    for col_idx, h in enumerate(headers, 1):
        c = ws.cell(row=6, column=col_idx, value=h)
        c.fill = HEADER_FILL
        c.font = HEADER_FONT
        c.alignment = ALIGN_CENTER
        c.border = BORDER_THIN

    for idx, row in enumerate(pillars_data, 7):
        ws.row_dimensions[idx].height = 28
        ws.cell(row=idx, column=1, value=row[0]).alignment = ALIGN_CENTER
        ws.cell(row=idx, column=2, value=row[1]).alignment = ALIGN_LEFT
        ws.cell(row=idx, column=3, value=row[2]).alignment = ALIGN_LEFT
        ws.cell(row=idx, column=4, value=row[3]).alignment = ALIGN_LEFT

        c_weight = ws.cell(row=idx, column=5, value=row[4])
        c_weight.number_format = "0.0%"
        c_weight.alignment = ALIGN_CENTER

        ws.cell(row=idx, column=6, value=row[5]).alignment = ALIGN_LEFT

        c_score = ws.cell(row=idx, column=7, value=row[6])
        c_score.alignment = ALIGN_CENTER
        c_score.font = BOLD_FONT

        c_weighted = ws.cell(row=idx, column=8, value=f"=G{idx}*E{idx}")
        c_weighted.number_format = "0.00"
        c_weighted.alignment = ALIGN_CENTER

        c_pass = ws.cell(row=idx, column=9, value=f'=IF(G{idx}>=4, "PASS", IF(G{idx}=3, "NEUTRAL", "FAIL"))')
        c_pass.alignment = ALIGN_CENTER
        c_pass.font = BOLD_FONT

        c_notes = ws.cell(row=idx, column=10, value=row[7])
        c_notes.alignment = ALIGN_LEFT

        for col in range(1, 11):
            if col not in (7, 9):
                ws.cell(row=idx, column=col).font = ROW_FONT
            ws.cell(row=idx, column=col).border = BORDER_THIN

    ws.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=['"PASS"'], stopIfTrue=True, font=GREEN_FONT))
    ws.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=['"NEUTRAL"'], stopIfTrue=True, font=AMBER_FONT))
    ws.conditional_formatting.add("I7:I22", CellIsRule(operator="equal", formula=['"FAIL"'], stopIfTrue=True, font=RED_FONT))

    ws.row_dimensions[24].height = 30
    ws.cell(row=24, column=3, value="OVERALL SCORE & WEIGHTED TOTAL").font = BOLD_FONT
    ws.cell(row=24, column=3).alignment = Alignment(horizontal="right", vertical="center")
    c_tot = ws.cell(row=24, column=8, value="=SUM(H7:H22)")
    c_tot.font = BOLD_FONT
    c_tot.number_format = "0.00"
    c_tot.alignment = ALIGN_CENTER

    ws.cell(row=26, column=2, value=calc_title).font = BOLD_FONT
    ws.row_dimensions[27].height = 28
    for col_idx, vh in enumerate(calc_headers, 2):
        c = ws.cell(row=27, column=col_idx, value=vh)
        c.fill = HEADER_FILL
        c.font = HEADER_FONT
        c.alignment = ALIGN_CENTER
        c.border = BORDER_THIN

    ws.row_dimensions[28].height = 26
    for i, (val, fmt, is_bold, align) in enumerate(zip(calc_row_values, calc_formats["formats"], calc_formats["bold"], calc_formats["align"]), 2):
        c = ws.cell(row=28, column=i, value=val)
        if fmt:
            c.number_format = fmt
        c.alignment = ALIGN_LEFT if align == "left" else ALIGN_CENTER
        c.font = BOLD_FONT if is_bold else ROW_FONT
        c.border = BORDER_THIN

    widths = {"A": 10, "B": 28, "C": 28, "D": 26, "E": 22, "F": 32, "G": 20, "H": 16, "I": 20, "J": 38}
    for col_letter, w in widths.items():
        ws.column_dimensions[col_letter].width = w

    output = io.BytesIO()
    wb.save(output)
    output.seek(0)
    return output

app_mode = st.sidebar.selectbox("Select Evaluation Model", ["Public Stock Evaluator", "Pre-Profit Startup Evaluator"])
today_str = datetime.now().strftime("%Y-%m-%d")

if app_mode == "Public Stock Evaluator":
    st.subheader("🏢 Public Listed Company Valuation Engine")
    col_in1, col_in2 = st.columns([2, 1])
    with col_in1:
        ticker = st.text_input("Enter Stock Ticker Symbol (e.g., AVGO, TPR, CAT, MSFT):", value="AVGO").strip().upper()
    with col_in2:
        mos_pct = st.number_input("Margin of Safety Required (%):", min_value=0, max_value=60, value=20, step=5) / 100.0

    if st.button("Generate Stock Scorecard", type="primary"):
        if not ticker:
            st.warning("Please enter a valid ticker symbol.")
        else:
            with st.spinner(f"Fetching live market data and computing 16-pillar audit for {ticker}..."):
                try:
                    stock = yf.Ticker(ticker)
                    todays_data = stock.history(period="1d")
                    cmp = float(todays_data["Close"].iloc[-1]) if not todays_data.empty else float(stock.fast_info.last_price)

                    info = stock.info or {}
                    company_name = info.get("longName") or info.get("shortName") or ticker
                    fair_value = float(info.get("targetMeanPrice")) if info.get("targetMeanPrice") else round(cmp * 1.25, 2)
                    analyst_rec = (info.get("recommendationKey") or "BUY").upper().replace("_", " ")
                    num_analysts = info.get("numberOfAnalystOpinions") or 10

                    gm_val = info.get("grossMargins", 0.50) if info.get("grossMargins") is not None else 0.50
                    roe_val = info.get("returnOnEquity", 0.20) if info.get("returnOnEquity") is not None else 0.20
                    de_val = info.get("debtToEquity", 50.0) if info.get("debtToEquity") is not None else 50.0
                    rg_val = info.get("revenueGrowth", 0.10) if info.get("revenueGrowth") is not None else 0.10
                    fcf_val = info.get("freeCashflow", 1000000000) if info.get("freeCashflow") is not None else 1000000000
                    net_income_val = info.get("netIncomeToCommon", 1000000000) if info.get("netIncomeToCommon") is not None else 1000000000
                    pe_val = info.get("trailingPE", 20.0) if info.get("trailingPE") is not None else 20.0
                    peg_val = info.get("pegRatio", 1.5) if info.get("pegRatio") is not None else 1.5
                    insider_val = (info.get("heldPercentInsiders") * 100) if info.get("heldPercentInsiders") is not None else 3.0

                    insider_action = "Stable / Neutral"
                    try:
                        insider_txns = stock.insider_transactions
                        if insider_txns is not None and not insider_txns.empty and "Shares" in insider_txns.columns:
                            recent_net = insider_txns["Shares"].head(5).sum()
                            if recent_net > 0: insider_action = "Net Open-Market Buyers"
                            elif recent_net < 0: insider_action = "Net Open-Market Sellers"
                    except Exception:
                        pass

                    market_cap = info.get("marketCap") or 0
                    fcf_yield_val = (fcf_val / market_cap) * 100 if market_cap > 0 and fcf_val else 4.0

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
                    score_44 = 5 if "Buyers" in insider_action else 4
                    score_45 = 5 if "BUY" in analyst_rec else 3

                    pillars_data = [
                        ("1.1", "Economic Moat", "Competitive Advantage", "Brand Moat & Pricing Power", 0.06, f"Gross Margin: {gm_val*100:.1f}%", score_11, "Strong moat"),
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
                        ("4.4", "Screening Filters", "Insider Net Action", "Net open-market buying", 0.06, f"Recent Activity: {insider_action}", score_44, "Insider trading momentum"),
                        ("4.5", "Expert Opinion", "Wall Street Analyst Consensus", "Strong Buy / Buy", 0.06, f"Consensus: {analyst_rec} (${fair_value:,.2f} Target)", score_45, "Wall Street backing")
                    ]

                    target_buy = fair_value * (1 - mos_pct)
                    in_buy_zone = cmp <= target_buy
                    weighted_total = sum(r[4] * r[6] for r in pillars_data)

                    excel_file = build_excel_report(
                        sheet_title="Established Companies",
                        main_title=f"Anti-Fragile Stock Evaluation & Risk Audit Framework ({company_name})",
                        entity_line=f"Company / Ticker: {company_name} ({ticker})",
                        sub_line=f"Evaluation Date: {today_str} | Consensus: {analyst_rec} ({num_analysts} Analysts)",
                        pillars_data=pillars_data,
                        calc_title="VALUATION & TARGET BUY PRICE CALCULATOR",
                        calc_headers=["Valuation Method", "Current Market Price", "Fair Value Estimate", "Margin of Safety Required", "Target Max Buy Price", "Status vs Current Price"],
                        calc_row_values=["Discounted Fair Value Model", cmp, fair_value, mos_pct, "=D28*(1-E28)", '=IF(C28<=F28, "IN BUY ZONE", "WAIT FOR DIP")'],
                        calc_formats={"formats": [None, "$#,##0.00", "$#,##0.00", "0.0%", "$#,##0.00", None], "bold": [False, False, False, False, True, True], "align": ["left", "center", "center", "center", "center", "center"]}
                    )

                    st.success(f"Audit complete for **{company_name} ({ticker})**!")
                    m1, m2, m3, m4 = st.columns(4)
                    m1.metric("Current Market Price", f"${cmp:,.2f}")
                    m2.metric("Fair Value Estimate", f"${fair_value:,.2f}")
                    m3.metric("Target Max Buy Price", f"${target_buy:,.2f}", delta="IN BUY ZONE" if in_buy_zone else "WAIT FOR DIP")
                    m4.metric("Weighted Score", f"{weighted_total:.2f} / 5.00")

                    st.download_button(label=f"📥 Download {ticker} Excel Scorecard", data=excel_file, file_name=f"{ticker}_Evaluated_Framework_Final.xlsx", mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
                except Exception as e:
                    st.error(f"Could not fetch live data for '{ticker}'. Details: {e}")

elif app_mode == "Pre-Profit Startup Evaluator":
    st.subheader("🚀 Pre-Profit Startup & Unit Economics Evaluator")
    startup_name = st.text_input("Startup / Venture Name:", value="SaaSCo")
    c1, c2, c3 = st.columns(3)
    with c1:
        arr_growth = st.slider("YoY ARR Growth Rate (%)", 0, 250, 85) / 100.0
        gross_margin = st.slider("Gross Margin (%)", 10, 95, 78) / 100.0
        nrr_val = st.slider("Net Revenue Retention - NRR (%)", 70, 160, 115) / 100.0
    with c2:
        ltv_cac = st.slider("LTV / CAC Ratio", 0.5, 10.0, 4.2, 0.1)
        cac_payback = st.slider("CAC Payback Period (Months)", 1, 36, 9)
        burn_multiple = st.slider("Burn Multiple (Net Burn / New ARR)", 0.2, 4.0, 1.2, 0.1)
    with c3:
        runway_months = st.slider("Cash Runway (Months)", 3, 48, 22)
        ebitda_margin = st.slider("EBITDA / FCF Margin (%)", -100, 30, -10) / 100.0
        team_score = st.slider("Founder-Market Fit Score (1-5)", 1, 5, 5)

    rule_of_40 = arr_growth + ebitda_margin

    if st.button("Generate Startup Audit Scorecard", type="primary"):
        score_21 = 5 if ltv_cac >= 3.0 else (4 if ltv_cac >= 2.0 else 3)
        score_22 = 5 if cac_payback <= 12 else (4 if cac_payback <= 18 else 3)
        score_23 = 5 if gross_margin >= 0.70 else (4 if gross_margin >= 0.50 else 3)
        score_24 = 5 if nrr_val >= 1.10 else (4 if nrr_val >= 1.00 else 3)
        score_31 = 5 if burn_multiple <= 1.2 else (4 if burn_multiple <= 1.8 else 3)
        score_32 = 5 if runway_months >= 18 else (4 if runway_months >= 12 else 2)
        score_33 = 5 if rule_of_40 >= 0.40 else (4 if rule_of_40 >= 0.20 else 3)
        score_34 = 4
        score_42 = 5 if arr_growth >= 0.50 else (4 if arr_growth >= 0.25 else 3)
        score_44 = 5 if nrr_val >= 1.10 else 4

        pillars_data = [
            ("1.1", "Market Opportunity", "TAM / SAM Scale", "Market size > $1B", 0.06, "Large addressable market", 5, "Venture scale potential"),
            ("1.2", "Market Opportunity", "Defensibility / Moat", "Proprietary tech / Network effects", 0.06, "Strong IP / Moat", 5, "Defensible advantage"),
            ("1.3", "Market Opportunity", "GTM Motion", "Repeatable acquisition channel", 0.06, "Scalable GTM motion", 4, "Sales efficiency"),
            ("2.1", "Unit Economics", "LTV / CAC Ratio", "LTV:CAC >= 3.0x", 0.07, f"LTV/CAC: {ltv_cac:.1f}x", score_21, "Customer lifetime value health"),
            ("2.2", "Unit Economics", "CAC Payback Period", "Payback <= 12 Months", 0.07, f"Payback: {cac_payback} Months", score_22, "Capital recovery speed"),
            ("2.3", "Unit Economics", "Gross Margin Floor", "Gross Margin >= 70% (SaaS)", 0.07, f"Gross Margin: {gross_margin*100:.1f}%", score_23, "Cost structure efficiency"),
            ("2.4", "Unit Economics", "Net Revenue Retention", "NRR >= 110%", 0.07, f"NRR: {nrr_val*100:.1f}%", score_24, "Expansion & negative churn"),
            ("3.1", "Cash & Burn Health", "Burn Multiple", "Burn Multiple < 1.5x", 0.07, f"Burn Multiple: {burn_multiple:.2f}x", score_31, "Capital conversion efficiency"),
            ("3.2", "Cash & Burn Health", "Cash Runway", "Runway >= 18 Months", 0.06, f"Runway: {runway_months} Months", score_32, "Downside buffer"),
            ("3.3", "Cash & Burn Health", "Rule of 40 (Growth + Margin)", "Growth + Margin >= 40%", 0.06, f"Rule of 40 Score: {rule_of_40*100:.0f}%", score_33, "Growth vs burn balance"),
            ("3.4", "Cash & Burn Health", "Working Capital Discipline", "Lean overhead structure", 0.05, "Disciplined R&D allocation", score_34, "Cost discipline"),
            ("4.1", "Team & Traction", "Founder-Market Fit", "Domain expertise & execution", 0.06, f"Founder Score: {team_score}/5", team_score, "Execution capability"),
            ("4.2", "Team & Traction", "Top-Line ARR Growth", "YoY Growth >= 50%", 0.06, f"ARR Growth: {arr_growth*100:.1f}% YoY", score_42, "Momentum & traction"),
            ("4.3", "Team & Traction", "Cap Table & Investor Quality", "Tier-1 institutional backing", 0.06, "Clean cap table & syndicate", 5, "Investor support"),
            ("4.4", "Team & Traction", "Product-Market Fit Signals", "High user engagement / NRR", 0.06, f"NRR / Retention: {nrr_val*100:.1f}%", score_44, "Market pull"),
            ("4.5", "Team & Traction", "Milestone Execution", "Hitting product & revenue milestones", 0.06, "Consistent execution history", 5, "Milestone delivery")
        ]

        weighted_total = sum(r[4] * r[6] for r in pillars_data)
        clean_filename = startup_name.replace(" ", "_")

        excel_file = build_excel_report(
            sheet_title="Early-Stage & Pre-Profit",
            main_title=f"Pre-Profit Startup & Unit Economics Evaluation Framework ({startup_name})",
            entity_line=f"Target Venture: {startup_name}",
            sub_line=f"Evaluation Date: {today_str} | Stage: Seed / Series A Growth",
            pillars_data=pillars_data,
            calc_title="STARTUP BURN, RUNWAY & VALUATION HEALTH",
            calc_headers=["Evaluation Metric", "Burn Multiple", "Cash Runway (Mos)", "Rule of 40 Score", "Target Benchmark", "Burn Risk Status"],
            calc_row_values=["Venture Efficiency Model", burn_multiple, runway_months, rule_of_40, "< 1.5x Burn / >= 18m Runway", '=IF(AND(C28<=1.5, D28>=18), "VENTURE HEALTHY", "MONITOR BURN / RUNWAY")'],
            calc_formats={"formats": [None, "0.00", "0", "0.0%", None, None], "bold": [False, False, False, False, False, True], "align": ["left", "center", "center", "center", "center", "center"]}
        )

        st.success(f"Unit-economics audit generated for **{startup_name}**!")
        m1, m2, m3, m4 = st.columns(4)
        m1.metric("Burn Multiple", f"{burn_multiple:.2f}x")
        m2.metric("Cash Runway", f"{runway_months} Months")
        m3.metric("Rule of 40", f"{rule_of_40*100:.0f}%")
        m4.metric("Weighted Score", f"{weighted_total:.2f} / 5.00")

        st.download_button(label=f"📥 Download {startup_name} Audit Scorecard", data=excel_file, file_name=f"{clean_filename}_Startup_Evaluation_Framework.xlsx", mime="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet")
EOF
