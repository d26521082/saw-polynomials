# mathproject — OEIS 猜想證明計畫

業餘數學研究專案:證明 OEIS 上長期掛著「conjectured / empirical」標記的公式,
目標是更新 OEIS 條目、並累積成一篇可投稿的論文(如 Journal of Integer
Sequences),配合 Lean 4 形式化驗證。

## 目前目標:自避走多項式家族(20 個 OEIS 條目)

| 家族 | 條目 | 內容 |
|---|---|---|
| 2D | A188148–A188155 | n×n 方格上 k-step 自避走總數(k=3..10),猜想為 n 的二次式 |
| 3D | A187164–A187170 | n×n×n(k=3..9),猜想為三次式 |
| 4D | A188785–A188789 | n×n×n×n(k=2..6),猜想為四次式 |

核心定理(見 `docs/proof.md`):固定步數的自避走,起點的走法數只依賴
「到各面邊界的截斷距離」(Lemma 1),按此分類求和即得:當 n ≥ 2(k−1)+1 時
a(n) 是 n 的 d 次多項式,係數由有限次窗口枚舉決定。門檻以下的缺口用精確
計算逐一驗證(有限檢查)。

注意 Hardin 的 OEIS 慣例:「k-step walk」= k 個相異相鄰格子(k−1 條邊),
方向相反的走法分開計數(已用 A188148 的 example 區塊確認)。

## 目錄

- `verify/saw.py` — 計數引擎:暴力枚舉 + 窗口法(截斷剖面分類)+ 精確有理內插
- `verify/run_checks.py` — 驗證套件:`python3 run_checks.py [small|2d|3d|4d|all]`
- `verify/oeis_data.json` — OEIS 官方數據(2026-08-18 由 JSON API 原樣抓取)
- `docs/proof.md` — 定理與證明草稿(論文骨架)

## 復現 Lean 驗證

任何人(包括未來的你)在乾淨的 Linux/macOS 機器上重現全部機器驗證:

```bash
# 1. 裝 elan(Lean 版本管理器,約 1 分鐘)
curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y --default-toolchain none

# 2. 進入 Lean 專案(toolchain 與 mathlib 版本由 lean-toolchain / lake-manifest.json 釘死)
cd lean

# 3. 下載 mathlib 預編譯快取(約 5.6GB,免去數小時的 mathlib 自行編譯)
lake exe cache get

# 4. 重新驗證一切(我們的檔案從零重新檢查;含大型枚舉,約 30–60 分鐘)
lake build
```

`Build completed successfully` = 全部 20 條定理通過檢查。

之後可以稽核公理依賴(確認沒有偷用 sorry 或非標準公理):

```bash
echo 'import SawProofs
#print axioms SawProofs.D2.A_eq_poly
#print axioms SawProofs.D2.A188148
#print axioms SawProofs.D3.A187170
#print axioms SawProofs.D4.A188789' > /tmp/audit.lean
lake env lean /tmp/audit.lean
```

預期輸出:主定理(`*_eq_poly`)只列 `[propext, Classical.choice, Quot.sound]`
(Lean 標準三公理);條目定理多一個 `Lean.ofReduceBool`(`native_decide`
的標準編譯器信任)。任何 `sorry` 都會在 build 時以 warning 顯示 — 沒有就是沒有。

Python 驗證套件的復現:`cd verify && python3 run_checks.py all`(約 3 分鐘,
無第三方依賴)。

## 進度

- [x] 2026-08-18 選題調查:66 個帶猜想的條目,篩出四組候選
- [x] 窗口法引擎 + 暴力枚舉交叉驗證(28 個測試)
- [x] 2D 全家族(8 條)完整驗證:OEIS 全部數據吻合、精確多項式 = 猜想、門檻缺口關閉
- [x] 4D 全家族(5 條)同上
- [x] 3D 全家族(7 條)同上 — 至此 20 條猜想全部驗證完成
- [x] Lean 4 + mathlib 環境、2D 主定理完整形式化(局部性、平移、census、多項式定理)
- [x] A188148–A188155 八條 2D 猜想在 Lean 中端到端機器驗證(公理:標準三條 + ofReduceBool)
- [x] 3D(A187164–A187170)與 4D(A188785–A188789)形式化完成 — 20 條猜想全部機器驗證
- [x] 論文初稿(LaTeX,paper/main.tex,6 頁,編譯乾淨)
- [ ] Lean 形式化元定理(mathlib)、OEIS 條目更新、社群回饋
