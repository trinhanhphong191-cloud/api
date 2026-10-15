// tonghop.js - FILE DUY NHẤT: Express + CORS | 13 game của 6 nhà (Sunwin, HitClub, B52, 789Club, LC79, BetVip) | /lichsu
// Cài:  npm i express cors
// Chạy: node tonghop.js     ->  http://localhost:3000/lichsu
// Route mỗi game: /<game>  /api/<game>  /lichsu/<game>   (xem danh sách ở /health hoặc console khi khởi động)
// Khoá nguồn kwinstore: biến môi trường KWIN_KEY (hoặc SOURCE_<TÊN_GAME_VIẾT_HOA> là URL đầy đủ)

const express = require("express");
const cors = require("cors");
const path = require("path");
const fs = require("fs");

// ================= ENGINE: soi cầu + ensemble thích nghi =================
const T = "TAI", X = "XIU";
const opp = (r) => (r === T ? X : T);
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));
const WARM = 20;   // tối thiểu 20 phiên hợp lệ trước khi đánh giá dự đoán
const WINDOW = 40; // cửa sổ đánh giá độ tin cậy từng thuật toán

function toRuns(seq) {
  const runs = [];
  for (const r of seq) {
    const last = runs[runs.length - 1];
    if (last && last.val === r) last.len++;
    else runs.push({ val: r, len: 1 });
  }
  return runs;
}

function makeCtx(hist) {
  const seq = hist.map((h) => h.result);
  return { hist, seq, pts: hist.map((h) => h.point), runs: toRuns(seq) };
}

// ----- 1. Cầu theo chu kỳ độ dài chuỗi (1-1, 2-2, 3-3, 2-1-2, 3-2, 4-1 ...) -----
function cyclePattern(ctx, cycle) {
  const runs = ctx.runs;
  const cur = runs[runs.length - 1];
  const done = runs.slice(0, -1);
  const k = cycle.length;
  const need = Math.max(3, 2 * k);
  if (done.length < need) return null;
  for (let p = 0; p < k; p++) {
    if (cur.len > cycle[p]) continue;
    let ok = true;
    for (let j = 0; j < need; j++) {
      const idx = (((p - 1 - j) % k) + k) % k;
      if (done[done.length - 1 - j].len !== cycle[idx]) { ok = false; break; }
    }
    if (ok) return { pick: cur.len < cycle[p] ? cur.val : opp(cur.val), weight: 1 + need * 0.25 };
  }
  return null;
}
const CYCLES = {
  "cau-1-1": [1], "cau-2-2": [2], "cau-3-3": [3], "cau-4-4": [4],
  "cau-2-1-2": [2, 1], "cau-3-2": [3, 2], "cau-4-1": [4, 1], "cau-3-1": [3, 1], "cau-4-2": [4, 2],
  "cau-1-1-2": [1, 1, 2], "cau-1-2": [1, 2], "cau-2-3": [2, 3], "cau-1-3": [1, 3], "cau-1-2-2": [1, 2, 2], "cau-3-3-1": [3, 3, 1], "cau-2-2-1": [2, 2, 1], "cau-1-2-3": [1, 2, 3], "cau-3-2-1": [3, 2, 1],
};

// ----- 2. Cầu bệt / bẻ cầu -----
const catBet = (c) => {
  const cur = c.runs[c.runs.length - 1];
  return cur.len >= 3 ? { pick: cur.val, weight: 1 + cur.len * 0.5 } : null;
};
const beCau = (c) => {
  const cur = c.runs[c.runs.length - 1];
  return cur.len >= 9 ? { pick: opp(cur.val), weight: 1 + cur.len * 0.7 } : null;
};

// ----- 3. Xác suất ngắt chuỗi (hazard): chuỗi đang dài L thì lịch sử hay tiếp hay ngắt? (Beta smoothing) -----
function runMarkov(c) {
  const runs = c.runs, cur = runs[runs.length - 1], L = cur.len;
  let cont = 0, end = 0;
  for (let i = 0; i < runs.length - 1; i++) {
    if (runs[i].len > L) cont++;
    else if (runs[i].len === L) end++;
  }
  if (cont + end < 8) return null;
  const p = (cont + 1) / (cont + end + 2);
  if (Math.abs(p - 0.5) < 0.1) return null;
  return { pick: p > 0.5 ? cur.val : opp(cur.val), weight: 1 + 6 * Math.abs(p - 0.5) };
}

// ----- 4. Markov bậc k (xác suất hậu nghiệm Beta) -----
function markovK(c, k) {
  const s = c.seq;
  if (s.length <= k + 3) return null;
  const ctx = s.slice(-k).join(",");
  let a = 0, b = 0;
  for (let i = k; i < s.length; i++) {
    if (s.slice(i - k, i).join(",") === ctx) (s[i] === T ? a++ : b++);
  }
  const t = a + b;
  if (t < Math.max(8, 2 * k)) return null; // bậc cao cần nhiều lần xuất hiện hơn
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.12) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 5. Lặp chuỗi: đoạn cuối (5-7 phiên) từng xuất hiện >= 2 lần, sau đó thường ra gì (Beta) -----
function lapChuoi(c) {
  const s = c.seq;
  for (let L = Math.min(7, s.length - 2); L >= 5; L--) {
    const suf = s.slice(-L).join(",");
    let a = 0, b = 0;
    for (let i = s.length - L - 1; i >= 0; i--) {
      if (s.slice(i, i + L).join(",") === suf) (s[i + L] === T ? a++ : b++);
    }
    const t = a + b;
    if (t >= 3) { // cần ít nhất 3 lần lặp trước khi xem tín hiệu là có ích
      const p = (a + 1) / (t + 2);
      if (Math.abs(p - 0.5) >= 0.15) return { pick: p > 0.5 ? T : X, weight: 0.6 + 3 * Math.abs(p - 0.5) };
    }
  }
  return null;
}

// ----- 6. Chu kỳ lặp p phiên (vd T T X T T X) -----
function chuKy(c, p) {
  const s = c.seq, n = s.length;
  if (n < p * 3) return null; // xác nhận chu kỳ qua 3 lần, không chỉ 2 lần tình cờ
  for (let j = 0; j < p; j++) {
    if (s[n - 1 - j] !== s[n - 1 - j - p] || s[n - 1 - j - p] !== s[n - 1 - j - 2 * p]) return null;
  }
  const unit = s.slice(n - p);
  if (unit.every((v) => v === unit[0])) return null;
  return { pick: s[n - p], weight: 1 + 0.3 * p };
}

// ----- 7. Bayes tỉ lệ Tài/Xỉu toàn lịch sử -----
function bayesTyLe(c) {
  const n = c.seq.length, tai = c.seq.filter((r) => r === T).length;
  if (n < 50) return null; // tránh đoán theo lệch tỉ lệ của mẫu nhỏ
  const p = (tai + 1) / (n + 2);
  if (Math.abs(p - 0.5) < 0.08) return null;
  return { pick: p > 0.5 ? T : X, weight: 0.8 };
}

// ----- 8. Markov theo vùng điểm của phiên trước -----
const bucket = (p) => (p <= 7 ? 0 : p <= 10 ? 1 : p <= 13 ? 2 : 3);
function markovTong(c) {
  const n = c.seq.length;
  if (n < 20) return null;
  const b = bucket(c.pts[n - 1]);
  let a = 0, x = 0;
  for (let i = 1; i < n; i++) if (bucket(c.pts[i - 1]) === b) (c.seq[i] === T ? a++ : x++);
  const t = a + x;
  if (t < 10) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.1) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 9. Cân bằng: N phiên gần nhất lệch quá một bên thì đoán về bên còn lại -----
function canBang(c, n) {
  const s = c.seq;
  if (s.length < n) return null;
  const tai = s.slice(-n).filter((v) => v === T).length;
  const d = tai / n - 0.5;
  if (Math.abs(d) < 0.17) return null;
  return { pick: d > 0 ? X : T, weight: 0.8 + 3 * (Math.abs(d) - 0.17) };
}

// ----- 10. Nhịp chuỗi kép: độ dài chuỗi trước + chuỗi hiện tại -> tiếp hay ngắt -----
function runMarkov2(c) {
  const runs = c.runs;
  if (runs.length < 8) return null;
  const cur = runs[runs.length - 1], L = cur.len, prev = Math.min(runs[runs.length - 2].len, 4);
  let cont = 0, end = 0;
  for (let i = 1; i < runs.length - 1; i++) {
    if (Math.min(runs[i - 1].len, 4) !== prev) continue;
    if (runs[i].len > L) cont++;
    else if (runs[i].len === L) end++;
  }
  if (cont + end < 6) return null;
  const p = (cont + 1) / (cont + end + 2);
  if (Math.abs(p - 0.5) < 0.15) return null;
  return { pick: p > 0.5 ? cur.val : opp(cur.val), weight: 1 + 5 * Math.abs(p - 0.5) };
}

// ----- 11. Markov theo điểm chính xác (3-18) của phiên trước -----
function markovDiemChinh(c) {
  const n = c.seq.length;
  if (n < 30) return null;
  const v = c.pts[n - 1];
  let a = 0, b = 0;
  for (let i = 1; i < n; i++) if (c.pts[i - 1] === v) (c.seq[i] === T ? a++ : b++);
  const t = a + b;
  if (t < 8) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.12) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 12. Markov theo 2 vùng điểm liên tiếp -----
function markovTong2(c) {
  const n = c.seq.length;
  if (n < 30) return null;
  const key = bucket(c.pts[n - 2]) * 4 + bucket(c.pts[n - 1]);
  let a = 0, b = 0;
  for (let i = 2; i < n; i++) if (bucket(c.pts[i - 2]) * 4 + bucket(c.pts[i - 1]) === key) (c.seq[i] === T ? a++ : b++);
  const t = a + b;
  if (t < 10) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.12) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 13. Markov theo số xúc xắc "lớn" (>=4) của phiên trước -----
const bigCount = (d) => d.filter((x) => x >= 4).length;
function markovXucXac(c) {
  const n = c.seq.length, h = c.hist;
  if (n < 30 || !Array.isArray(h[n - 1].dices)) return null;
  const key = bigCount(h[n - 1].dices);
  let a = 0, b = 0;
  for (let i = 1; i < n; i++) if (Array.isArray(h[i - 1].dices) && bigCount(h[i - 1].dices) === key) (c.seq[i] === T ? a++ : b++);
  const t = a + b;
  if (t < 8) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.12) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 14. Xu hướng EWMA (đi theo bên đang chiếm ưu thế gần đây) -----
function xuHuong(c) {
  const s = c.seq;
  if (s.length < 20) return null;
  const al = 0.15;
  let e = 0.5;
  for (const r of s) e = e * (1 - al) + (r === T ? 1 : 0) * al;
  const d = e - 0.5;
  if (Math.abs(d) < 0.12) return null;
  return { pick: d > 0 ? T : X, weight: 0.8 + 3 * (Math.abs(d) - 0.12) };
}

// ----- 15. Cầu gương: đoạn cuối đối xứng quanh một tâm (vd T X X T T X X T) -> đoán tiếp theo phản chiếu -----
function cauGuong(c) {
  const s = c.seq, n = s.length;
  for (let m = 5; m >= 3; m--) {
    if (n < 2 * m) continue;
    const start = n - 2 * m;
    let ok = true;
    // Kiểm tra đúng đoạn đối xứng chẵn: nửa trái phải bằng nửa phải theo chiều ngược.
    for (let j = 0; j < m; j++) {
      if (s[start + j] !== s[n - 1 - j]) { ok = false; break; }
    }
    if (!ok) continue;
    const seg = s.slice(start);
    if (seg.every((v) => v === seg[0])) continue;
    return { pick: s[start], weight: 0.8 + 0.12 * m };
  }
  return null;
}

// ----- 16. Tương quan lag-p: 24 phiên gần nhất hay giống / hay ngược phiên cách p bước -----
function tuongQuanLag(c, p) {
  const s = c.seq, n = s.length, W = 40;
  if (n < W + p) return null;
  let agree = 0;
  for (let i = n - W; i < n; i++) if (s[i] === s[i - p]) agree++;
  const r = agree / W, d = Math.abs(r - 0.5);
  if (d < 0.2) return null;
  return { pick: r > 0.5 ? s[n - p] : opp(s[n - p]), weight: 0.8 + 3 * (d - 0.2) };
}

// ----- 17. Markov theo chẵn/lẻ của điểm phiên trước -----
function markovChanLe(c) {
  const n = c.seq.length;
  if (n < 30) return null;
  const par = c.pts[n - 1] % 2;
  let a = 0, b = 0;
  for (let i = 1; i < n; i++) if (c.pts[i - 1] % 2 === par) (c.seq[i] === T ? a++ : b++);
  const t = a + b;
  if (t < 20) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.1) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 18. Hồi quy về trung bình điểm: 8 phiên gần nhất lệch xa 10.5 thì đoán ngược lại -----
function hoiQuyDiem(c) {
  const n = c.pts.length;
  if (n < 10) return null;
  const m = c.pts.slice(-8).reduce((a, v) => a + v, 0) / 8, d = m - 10.5;
  if (Math.abs(d) < 1.3) return null;
  return { pick: d > 0 ? X : T, weight: 0.8 + 0.5 * (Math.abs(d) - 1.3) };
}

// ----- 19. Markov theo số xúc xắc "lớn" của 2 phiên liên tiếp -----
function markovXucXac2(c) {
  const n = c.seq.length, h = c.hist;
  if (n < 40 || !Array.isArray(h[n - 1].dices) || !Array.isArray(h[n - 2].dices)) return null;
  const key = bigCount(h[n - 1].dices) * 4 + bigCount(h[n - 2].dices);
  let a = 0, b = 0;
  for (let i = 2; i < n; i++) {
    if (!Array.isArray(h[i - 1].dices) || !Array.isArray(h[i - 2].dices)) continue;
    if (bigCount(h[i - 1].dices) * 4 + bigCount(h[i - 2].dices) === key) (c.seq[i] === T ? a++ : b++);
  }
  const t = a + b;
  if (t < 8) return null;
  const p = (a + 1) / (t + 2);
  if (Math.abs(p - 0.5) < 0.12) return null;
  return { pick: p > 0.5 ? T : X, weight: 1 + 4 * Math.abs(p - 0.5) };
}

// ----- 20. Hồi quy logistic online: học từ 8 kết quả gần nhất (huấn luyện lại trên dữ liệu TRƯỚC phiên đoán) -----
function logistic(c) {
  const s = c.seq, n = s.length, K = 8;
  if (n < K + 80) return null; // dữ liệu học logistic phải đủ rộng so với 9 tham số
  const feat = (i) => { const f = [1]; for (let j = 1; j <= K; j++) f.push(s[i - j] === T ? 1 : -1); return f; };
  const w = new Array(K + 1).fill(0);
  const sig = (z) => 1 / (1 + Math.exp(-z));
  for (let ep = 0; ep < 3; ep++) {
    for (let i = K; i < n; i++) {
      const f = feat(i);
      const g = (s[i] === T ? 1 : 0) - sig(f.reduce((a, v, k) => a + v * w[k], 0));
      for (let k = 0; k <= K; k++) w[k] += 0.03 * (g * f[k] - 0.01 * w[k]);
    }
  }
  const f = feat(n);
  const p = sig(f.reduce((a, v, k) => a + v * w[k], 0));
  if (Math.abs(p - 0.5) < 0.06) return null;
  return { pick: p > 0.5 ? T : X, weight: 0.6 + 3 * (Math.abs(p - 0.5) - 0.06) };
}

const STRATEGIES = {};
for (const [name, cycle] of Object.entries(CYCLES)) STRATEGIES[name] = (c) => cyclePattern(c, cycle);
Object.assign(STRATEGIES, {
  "cau-bet": catBet,
  "be-cau": beCau,
  "run-markov": runMarkov,
  "markov-2": (c) => markovK(c, 2),
  "markov-3": (c) => markovK(c, 3),
  "markov-4": (c) => markovK(c, 4),
  "markov-5": (c) => markovK(c, 5),
  "markov-6": (c) => markovK(c, 6),
  "cau-guong": cauGuong,
  "lag-2": (c) => tuongQuanLag(c, 2),
  "lag-3": (c) => tuongQuanLag(c, 3),
  "lag-4": (c) => tuongQuanLag(c, 4),
  "chan-le": markovChanLe,
  "hoi-quy-diem": hoiQuyDiem,
  "markov-xuc-xac-2": markovXucXac2,
  "logistic": logistic,
  "markov-diem-chinh": markovDiemChinh,
  "markov-tong-2": markovTong2,
  "markov-xuc-xac": markovXucXac,
  "xu-huong": xuHuong,
  "lap-chuoi": lapChuoi,
  "chu-ky-3": (c) => chuKy(c, 3),
  "chu-ky-4": (c) => chuKy(c, 4),
  "chu-ky-5": (c) => chuKy(c, 5),
  "chu-ky-6": (c) => chuKy(c, 6),
  "bayes-ty-le": bayesTyLe,
  "markov-tong": markovTong,
  "run-markov-2": runMarkov2,
  "can-bang-12": (c) => canBang(c, 12),
  "can-bang-24": (c) => canBang(c, 24),
});
const ALL_NAMES = Object.keys(STRATEGIES);
let MULT = null; // hệ số ưu tiên theo hồ sơ của game đang tính (null = đều nhau)
let NAMES = ALL_NAMES; // chiến lược đang dùng: mỗi game có 1 hồ sơ riêng (xem PROFILES)

// ----- Walk-forward: dự đoán của từng thuật toán + ensemble tại mọi vị trí (chỉ dùng dữ liệu TRƯỚC vị trí đó) -----
const WINDOW_LONG = 150; // cửa sổ dài để trọng số không chạy theo vài phiên may rủi
// Thành tích walk-forward: tại vị trí i chỉ dùng kết quả đã biết trước i.
// Beta(1,1) shrinkage kéo các mẫu ít dữ liệu về 50%, tránh tăng trọng số vì vài lần đoán trúng.
function skillRecord(preds, name, hist, from, to) {
  let wins = 0, fired = 0;
  for (let j = Math.max(WARM, from); j < to; j++) {
    const q = preds[name] && preds[name][j];
    if (!q) continue;
    fired++;
    if (q.pick === hist[j].result) wins++;
  }
  return { fired, wins, rate: (wins + 1) / (fired + 2) };
}
function skillFactor(preds, name, hist, i) {
  const recent = skillRecord(preds, name, hist, i - WINDOW, i);
  const longer = skillRecord(preds, name, hist, i - WINDOW_LONG, i);
  let edge = 0, weight = 0;
  // Không học trọng số từ các mẫu quá nhỏ; giới hạn tác động để giảm overfit/multiple testing.
  if (recent.fired >= 20) { edge += 0.7 * (recent.rate - 0.5); weight += 0.7; }
  if (longer.fired >= 50) { edge += 0.3 * (longer.rate - 0.5); weight += 0.3; }
  if (!weight) return 1;
  edge /= weight;
  return clamp(1 + 0.8 * edge, 0.8, 1.2);
}
const BAL = 12; // lịch sử dự đoán gần đây chỉ dùng khi phiếu hoà để phá hoà; không ép cân bằng đầu ra
// Cache tăng dần: khi có phiên mới chỉ tính thêm vị trí mới, không tính lại toàn bộ lịch sử.
// Hợp lệ vì dự đoán tại vị trí i chỉ phụ thuộc dữ liệu TRƯỚC i.
const caches = new Map(); // mỗi game 1 cache riêng
let CUR_KEY = "_";
function analyze(hist) {
  const n = hist.length;
  let c = caches.get(CUR_KEY);
  if (c && !(c.ids.length <= n && c.ids.every((id, i) => hist[i].id === id && hist[i].result === c.res[i]))) c = null;
  if (!c) {
    c = { ids: [], res: [], preds: {}, ens: [] };
    for (const name of NAMES) c.preds[name] = [];
    caches.set(CUR_KEY, c);
  }
  c.startId = hist[0].id;
  const { preds, ens } = c;
  for (let i = Math.max(WARM, c.ids.length + 1); i <= n; i++) {
    const ctx = makeCtx(hist.slice(0, i));
    for (const name of NAMES) { try { preds[name][i] = STRATEGIES[name](ctx); } catch (_) { preds[name][i] = null; } }
  }
  for (let i = Math.max(WARM, c.ids.length + 1); i <= n; i++) {
    const recent = [];
    for (let j = Math.max(WARM, i - BAL); j < i; j++) recent.push(ens[j].pick);
    ens[i] = ensembleAt(preds, hist, i, recent);
  }
  c.ids = hist.map((h) => h.id);
  c.res = hist.map((h) => h.result);
  return { preds, ens };
}

// ----- Ensemble thích nghi, không ép tỉ lệ Tài/Xỉu bằng cách lật phiếu -----
// Trọng số chỉ học từ dự đoán walk-forward đã có kết quả, dùng shrinkage và giới hạn biên độ.
// pT/pX là tỷ trọng phiếu đã co về 50%, KHÔNG phải xác suất thắng thực tế đã hiệu chuẩn.
function ensembleAt(preds, hist, i, recent) {
  const list = [];
  let sT = 0, sX = 0;
  for (const name of NAMES) {
    const r = preds[name] && preds[name][i];
    if (!r || (r.pick !== T && r.pick !== X)) continue;
    const rel = skillFactor(preds, name, hist, i);
    const profileFactor = MULT ? MULT(name) : 1;
    const w = Math.min(r.weight * rel * profileFactor, 2.4);
    if (!Number.isFinite(w) || w <= 0) continue;
    list.push({ name, pick: r.pick, w });
    if (r.pick === T) sT += w; else sX += w;
  }
  const raw = sT + sX;
  // Chỉnh hướng tối đa 15% khi các dự đoán đã phát ra gần đây lệch mạnh.
  // Đây chỉ là ràng buộc phân bổ đầu ra theo yêu cầu cân bằng, KHÔNG phải bằng chứng tăng độ chính xác.
  const recentTai = recent.filter((p) => p === T).length;
  const recentShare = recent.length >= 8 ? recentTai / recent.length : 0.5;
  const deviation = recentShare - 0.5;
  const factorT = clamp(1 - 0.5 * deviation, 0.85, 1.15);
  const factorX = clamp(1 + 0.5 * deviation, 0.85, 1.15);
  const aT = sT * factorT, aX = sX * factorX;
  const adjustedRaw = aT + aX;
  const margin = adjustedRaw > 0 ? Math.abs(aT - aX) / adjustedRaw : 0;
  const hasSide = Math.abs(aT - aX) > 1e-9;
  const enough = (list.length >= 3 && adjustedRaw >= 2.5 && margin >= 0.08) ||
                 (list.length >= 2 && adjustedRaw >= 3.2 && margin >= 0.12);
  let pick, fallback = false;
  if (hasSide) {
    pick = aT > aX ? T : X;
    fallback = !enough;
  } else {
    fallback = true;
    // Hoà phiếu: dùng kết quả gần nhất, nhưng luôn đánh dấu tín hiệu yếu.
    pick = (hist[i - 1] && hist[i - 1].result) ||
           (recent.length ? opp(recent[recent.length - 1]) : T);
  }

  // Giới hạn lệch phân bổ dự đoán: nếu >=7/12 dự đoán gần nhất cùng một phía,
  // chỉ đảo dự đoán kế tiếp khi mô hình tiếp tục chọn phía đang quá nhiều.
  // Đây là quy tắc cân bằng đầu ra theo yêu cầu giao diện, không được xem là tăng xác suất thắng.
  let balanceOverride = false;
  if (recent.length >= BAL) {
    const recentT = recent.filter((p) => p === T).length;
    if (recentT >= 7 && pick === T) { pick = X; fallback = true; balanceOverride = true; }
    else if (recent.length - recentT >= 7 && pick === X) { pick = T; fallback = true; balanceOverride = true; }
  }

  const aligned = list.filter((x) => x.pick === pick).sort((a, b) => b.w - a.w);
  const voteShareT = adjustedRaw > 0 ? aT / adjustedRaw : 0.5;
  let pT;
  if (fallback) {
    const smallEdge = Math.min(0.07, margin * 0.07);
    pT = 0.5 + (pick === T ? smallEdge : -smallEdge);
  } else {
    pT = clamp((aT + 1.5) / (adjustedRaw + 3), 0.3, 0.7);
  }
  const firing = {};
  for (const x of list) firing[x.name] = x.pick;
  return {
    pick, pT: +pT.toFixed(2), pX: +(1 - pT).toFixed(2),
    voteShareT: +voteShareT.toFixed(3), voteMargin: +margin.toFixed(3),
    signal: balanceOverride ? "BALANCE_OVERRIDE" : fallback ? "WEAK" : "CONSENSUS",
    balanceOverride,
    top: aligned[0] || null, aligned, fallback,
    strategiesFiring: list.length, firing,
  };
}

// issued: các dự đoán đã THỰC SỰ phát ra gần đây (để giữ cân bằng theo đúng cái người dùng đã thấy)
// Chi phí tính lần đầu tăng theo BÌNH PHƯƠNG số phiên (4000 phiên ~16 giây trên máy nhanh, vài phút trên Render free)
// và nguồn trả về cửa sổ trượt nên cache cũ bị mất mỗi phiên. Giải pháp: chỉ phân tích tối đa MAXWIN phiên gần nhất,
// neo cố định ở một id để cache tăng dần được tái sử dụng; chỉ neo lại khi cửa sổ phình quá REBASE.
const MAXWIN = 250, REBASE = 500;
function windowed(hist) {
  const n = hist.length;
  if (n <= MAXWIN) return hist;
  const c = caches.get(CUR_KEY);
  let start = c && c.startId != null ? hist.findIndex((h) => h.id === c.startId) : -1;
  if (start < 0 || n - start > REBASE) start = n - MAXWIN;
  return start > 0 ? hist.slice(start) : hist;
}
function withGame(g, fn) {
  const pn = NAMES, pk = CUR_KEY, pm = MULT;
  NAMES = g.names; CUR_KEY = g.key; MULT = g.mult;
  try { return fn(); } finally { NAMES = pn; CUR_KEY = pk; MULT = pm; }
}

function predict(hist, issued) {
  hist = windowed(hist);
  const { preds, ens } = analyze(hist), n = hist.length;
  if (issued && issued.length >= 4) return ensembleAt(preds, hist, n, issued.slice(-BAL));
  return ens[n];
}

function backtest(hist) {
  hist = windowed(hist);
  const { preds, ens } = analyze(hist), n = hist.length;
  const st = {};
  for (const k of [...NAMES, "TONG-HOP"]) st[k] = { fired: 0, right: 0 };
  for (let i = WARM; i < n; i++) {
    const actual = hist[i].result;
    for (const name of NAMES) {
      const r = preds[name][i];
      if (r) { st[name].fired++; if (r.pick === actual) st[name].right++; }
    }
    st["TONG-HOP"].fired++;
    if (ens[i].pick === actual) st["TONG-HOP"].right++;
  }
  const out = {};
  for (const [k, v] of Object.entries(st)) {
    out[k] = { fired: v.fired, accuracy: v.fired ? +((v.right / v.fired) * 100).toFixed(1) + "%" : "n/a" };
  }
  return out;
}

// tỉ lệ Tài trong các dự đoán walk-forward (để kiểm tra độ cân bằng)
function pickShare(hist) {
  hist = windowed(hist);
  const { ens } = analyze(hist);
  const picks = ens.slice(WARM, hist.length).map((e) => e.pick);
  const tai = picks.filter((p) => p === T).length;
  return { tai, xiu: picks.length - tai, taiPercent: picks.length ? +((tai / picks.length) * 100).toFixed(1) : null };
}

function stats(hist) {
  const seq = hist.map((h) => h.result);
  const runs = toRuns(seq);
  const tai = seq.filter((r) => r === T).length;
  return {
    sessions: seq.length, tai, xiu: seq.length - tai,
    taiPercent: +((tai / seq.length) * 100).toFixed(1),
    longestStreak: Math.max(...runs.map((r) => r.len)),
    currentStreak: { result: runs[runs.length - 1].val, length: runs[runs.length - 1].len },
    runLengths: runs.slice(-15).map((r) => r.len).join("-"),
  };
}
const engine = { STRATEGIES, predict, backtest, stats, toRuns, pickShare };

// ================= SUNWIN: đọc dữ liệu + 3 vị =================
const noDau = (v) => String(v ?? "").normalize("NFD").replace(/[\u0300-\u036f]/g, "").replace(/đ/g, "d").replace(/Đ/g, "D").toUpperCase();

// Nhận cả 2 dạng: Sicbo {data:[{phien:"#2755612", ket_qua, tong, xuc_xac_1..3}]} và TX [{phiên, d1,d2,d3, tổng, "kết quả"}]
function parseSunwin(json) {
  const arr = Array.isArray(json) ? json : json && (json.data || json.list || json.history || json.items);
  if (!Array.isArray(arr)) throw new Error("Dữ liệu nguồn không hợp lệ (khoá: " + Object.keys(json || {}).join(",") + ")");
  const parsed = arr.map((s) => {
    const id = parseInt(String(s["phiên"] ?? s.phien ?? s.id ?? "").replace(/\D/g, ""), 10);
    const dices = [s.d1 ?? s.xuc_xac_1, s.d2 ?? s.xuc_xac_2, s.d3 ?? s.xuc_xac_3].map(Number);
    const okD = dices.every((d) => Number.isInteger(d) && d >= 1 && d <= 6);
    const rawPoint = s["tổng"] ?? s.tong ?? s.point;
    const point = rawPoint == null && okD ? dices[0] + dices[1] + dices[2] : Number(rawPoint);
    const kq = noDau(s["kết quả"] ?? s.ket_qua ?? s.result);
    const isTriple = okD && dices[0] === dices[1] && dices[1] === dices[2];
    const result = kq === "TAI" ? T : kq === "XIU" ? X : null;
    if (!Number.isSafeInteger(id) || id <= 0 || !Number.isFinite(point) || point < 4 || point > 17) return null;
    if (okD && dices.reduce((a, v) => a + v, 0) !== point) return null;
    if (isTriple || !result) return null; // bão không thuộc chuỗi Tài/Xỉu
    return { id, result, dices: okD ? dices : null, point };
  }).filter(Boolean);
  const byId = new Map();
  for (const h of parsed) byId.set(h.id, h);
  const hist = [...byId.values()].sort((a, b) => a.id - b.id); // cũ -> mới, không nhân đôi phiên
  if (hist.length < 20) throw new Error("Dữ liệu nguồn không đủ phiên hợp lệ (" + hist.length + "/" + arr.length + "); mẫu: " + JSON.stringify(arr[0]).slice(0, 200));
  return hist;
}

// Số tổ hợp 3 xúc xắc cho từng tổng (216 khả năng).
const XS = {};
for (let a = 1; a <= 6; a++) for (let b = 1; b <= 6; b++) for (let c = 1; c <= 6; c++) XS[a + b + c] = (XS[a + b + c] || 0) + 1;
// Sicbo loại các bộ ba (bão) khỏi chuỗi Tài/Xỉu. Dùng phân phối có điều kiện không phải bão:
// tổng hợp lệ có 210/216 tổ hợp; các tổng 6, 9, 12, 15 giảm mỗi tổng đi 1 cách.
const XS_VALID = { ...XS };
for (const v of [6, 9, 12, 15]) XS_VALID[v]--;
const VALID_TOT = 210;
// 3 vị: luôn chọn tổng có tần suất hợp lệ cao nhất rồi lấy 2 tổng có trọng số từ 4 tổng còn lại.
// Mã phiên làm seed nên bộ 3 vị không đổi sau khi đã khoá dự đoán.
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
function chonVi(pick, seedId) {
  const side = Object.keys(XS_VALID).map(Number).filter((v) => (pick === T ? v >= 11 && v <= 17 : v >= 4 && v <= 10))
    .sort((a, b) => XS_VALID[b] - XS_VALID[a]).slice(0, 5);
  const rand = rng(Math.imul(seedId | 0, 0x9E3779B1) ^ (pick === T ? 1 : 2));
  const out = [side[0]], pool = side.slice(1);
  while (out.length < 3) {
    const tot = pool.reduce((a, v) => a + XS_VALID[v], 0);
    let r = rand() * tot, k = 0;
    for (; k < pool.length - 1; k++) { r -= XS_VALID[pool[k]]; if (r <= 0) break; }
    out.push(pool.splice(k, 1)[0]);
  }
  return out.sort((a, b) => a - b);
}
// Xác suất hit của bộ 3 vị trên các phiên hợp lệ (đã loại bão), không dùng mẫu số 216 sai điều kiện.
const viProb = (vi) => vi.reduce((a, v) => a + (XS_VALID[v] || 0), 0) / VALID_TOT;
// Tỷ lệ hit trung bình lý thuyết của quy tắc lấy 1 vị tốt nhất + 2 vị có trọng số.
const P_VI = 0.3079071773636991;

// ================= HTML: bảng lịch sử đối chiếu thắng/thua =================
let LICHSU_HTML = String.raw`<!doctype html>
<html lang="vi">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>TỔNG HỢP – Lịch sử dự đoán</title>
<style>
:root{--bg:#070b1c;--line:#1b2a55;--mut:#7f8cb5;--tai:#ff5c8a;--xiu:#3d8bff;--gold:#ffd23f;--ok:#19f08a;--bad:#ff3d6e}
*{box-sizing:border-box;margin:0;padding:0}
body{background:radial-gradient(900px 500px at 85% -10%,#18306b 0%,transparent 60%),radial-gradient(800px 500px at -10% 110%,#2a1260 0%,transparent 55%),var(--bg);color:#e8ecf7;font:14px/1.5 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif;min-height:100vh}
.wrap{max-width:1180px;margin:0 auto;padding:22px 14px 40px}
header{display:flex;justify-content:space-between;align-items:center;flex-wrap:wrap;gap:12px;margin-bottom:14px}
h1{font-size:20px;letter-spacing:.5px}h1 span{color:var(--gold);text-shadow:0 0 14px #ffd23f66}
.tabs{display:flex;gap:6px;flex-wrap:wrap}
.tabs button{background:#0b1230;color:var(--mut);border:1px solid var(--line);border-radius:99px;padding:6px 14px;font-size:12px;font-weight:800;cursor:pointer;letter-spacing:.5px}
.tabs button.on{color:var(--gold);border-color:#ffd23f88;box-shadow:0 0 14px #ffd23f33}
.sum{display:flex;gap:10px;flex-wrap:wrap;margin-bottom:14px}
.s{background:linear-gradient(180deg,#0e1738,#0a1130);border:1px solid var(--line);border-radius:12px;padding:8px 16px;min-width:120px}
.s b{display:block;font-size:20px}.s span{font-size:10.5px;color:var(--mut);text-transform:uppercase;letter-spacing:1.2px}
.s.w b{color:var(--ok)}.s.l b{color:var(--bad)}
.box{background:linear-gradient(180deg,#0c1431cc,#080e26cc);border:1px solid var(--line);border-radius:18px;overflow:auto;box-shadow:0 0 40px #2a6bff1a}
table{width:100%;border-collapse:collapse;min-width:1500px}
th{color:#5f9bff;font-size:11px;text-transform:uppercase;letter-spacing:1.5px;text-align:left;padding:16px 14px 12px;font-weight:700}
th.c,td.c{text-align:center}
td{padding:11px 14px;border-top:1px solid #121c40;font-size:13px;white-space:nowrap}
tr:hover td{background:#ffffff06}
.id{color:var(--gold);font-weight:800;text-shadow:0 0 10px #ffd23f55}
.dice{font-weight:700;color:#cfd8ff}
.pill{display:inline-block;min-width:60px;text-align:center;padding:4px 12px;border-radius:9px;font-weight:800;font-size:12px;border:1px solid}
.pill.tai{color:var(--tai);border-color:#ff5c8a88;background:#ff5c8a1c;box-shadow:0 0 12px #ff5c8a33}
.pill.xiu{color:var(--xiu);border-color:#3d8bff88;background:#3d8bff1c;box-shadow:0 0 12px #3d8bff33}
.pill.na{color:var(--mut);border-color:var(--line);background:transparent;box-shadow:none}
.mau{display:inline-block;padding:4px 12px;border-radius:7px;font-weight:700;font-size:12px;border:1px solid #ffd23f88;background:#ffd23f12;color:#ffe27a}
.mau.theo{border-color:#19e6d088;background:#19e6d012;color:#46f0dc}
.st{display:inline-block;min-width:78px;text-align:center;padding:4px 12px;border-radius:8px;font-weight:800;font-size:11.5px;letter-spacing:.5px}
.st.w{color:var(--ok);background:#19f08a1c;border:1px solid #19f08a88;box-shadow:0 0 12px #19f08a33}
.st.l{color:var(--bad);background:#ff3d6e1c;border:1px solid #ff3d6e88;box-shadow:0 0 12px #ff3d6e33}
.st.p{color:var(--mut);background:#ffffff0d;border:1px solid var(--line)}
.empty{padding:40px;text-align:center;color:var(--mut)}
.foot{margin-top:12px;color:var(--mut);font-size:12px}
</style>
</head>
<body>
<div class="wrap">
  <header>
    <h1>📊 LỊCH SỬ <span>DỰ ĐOÁN</span></h1>
    <div class="tabs" id="tabs"></div>
  </header>
  <div class="sum" id="sum"></div>
  <div class="foot" id="nx" style="margin:-4px 0 12px"></div>
  <div class="box"><table>
    <thead><tr><th>Phiên</th><th>Xúc xắc</th><th class="c">Dự đoán</th><th class="c">Kết quả</th><th class="c" id="th-vi">3 vị</th><th>Cầu gần nhất</th><th>Mẫu cầu</th><th>Cầu đang chạy</th><th>Thuật toán</th><th class="c">Trạng thái</th></tr></thead>
    <tbody id="body"></tbody>
  </table></div>
  <div class="foot">Chỉ gồm các phiên đã được dự đoán trước khi có kết quả, tự đối chiếu thắng/thua. Kết quả là ngẫu nhiên nên tỉ lệ thắng sẽ quanh 50%.</div>
</div>
<script>
const $ = (id) => document.getElementById(id);
const esc = (s) => String(s).replace(/[&<>"]/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;" }[c]));
const cls = (v) => (v === "Tài" ? "tai" : "xiu");
const TABS = __TABS__;
$("tabs").innerHTML = TABS.map(([k, n]) => '<button id="tab-' + k + '" onclick="setGame(\'' + k + '\')">' + esc(n) + "</button>").join("");
let game = localStorage.getItem("game");
if (!TABS.some((t) => t[0] === game)) game = TABS[0][0];
function setGame(g) {
  game = g; localStorage.setItem("game", g); mark();
  $("th-vi").style.display = /_sicbo$/.test(g) ? "" : "none";
  $("sum").innerHTML = ""; $("nx").textContent = "";
  $("body").innerHTML = '<tr><td colspan="10" class="empty">Đang tải…</td></tr>';
  load();
}
let reqSeq = 0;
function mark() { for (const [k] of TABS) $("tab-" + k).className = k === game ? "on" : ""; }
async function load() {
  try {
    const my = ++reqSeq, gm = game;
    const d = await (await fetch("/lichsu/" + gm + "?limit=60")).json();
    if (my !== reqSeq || gm !== game) return; // đã chuyển tab, bỏ phản hồi cũ
    if (d.error) throw new Error(d.error);
    const t = d.thong_ke;
    $("th-vi").style.display = t.vi ? "" : "none"; // chỉ Sicbo có cột 3 vị
    $("sum").innerHTML = [["Đã đối chiếu", t.tong, ""], ["Thắng", t.thang, "w"], ["Thua", t.thua, "l"], ["Tỉ lệ thắng", t.ti_le_thang, ""], ["Khoảng tin cậy 95%", t.ktc_95, ""]].concat(t.vi ? [["Trúng 3 vị", t.vi.trung + "/" + t.vi.tong, ""], ["Tỉ lệ trúng vị", t.vi.ti_le, ""]] : [])
      .map(([a, b, c]) => '<div class="s ' + c + '"><b>' + esc(b) + "</b><span>" + a + "</span></div>").join("");
    $("nx").textContent = (t.luu_y ? t.luu_y + " | " : "") + t.nhan_xet + (t.p_value != null ? " (p = " + t.p_value + ")" : "") +
      (t.vi ? " | 3 vị: " + t.vi.nhan_xet + " (mức cơ sở lý thuyết " + t.vi.co_so + ")" : "");
    if (!d.danh_sach.length) { $("body").innerHTML = '<tr><td colspan="10" class="empty">Chưa có phiên nào. Giữ server chạy, dự đoán sẽ tự được ghi lại.</td></tr>'; return; }
    $("body").innerHTML = d.danh_sach.map((r) => {
      const st = r.trang_thai === "Thắng" ? "w" : r.trang_thai === "Thua" ? "l" : "p";
      const ico = r.trang_thai === "Thắng" ? "✔ " : r.trang_thai === "Thua" ? "✖ " : "⏳ ";
      const theo = (r.mau_cau || "").indexOf("Theo cầu") === 0 ? " theo" : "";
      return "<tr><td class='id'>#" + esc(r.Phien) + "</td><td class='dice'>" + (r.Xuc_xac ? "[" + r.Xuc_xac.map(esc).join(", ") + "]" : "—") +
        "</td><td class='c'><span class='pill " + cls(r.du_doan) + "'>" + esc(r.du_doan.toUpperCase()) + "</span></td><td class='c'>" +
        (r.Ket_qua ? "<span class='pill " + cls(r.Ket_qua) + "'>" + esc(r.Ket_qua.toUpperCase()) + "</span>" : "<span class='pill na'>—</span>") +
        "</td>" + (t.vi ? "<td class='c'>" + (r.vi ? r.vi.map((v) => "<span class='" + (r.Tong === v ? "st w" : "pill na") + "' style='min-width:32px;margin:0 2px;padding:3px 8px'>" + esc(v) + "</span>").join("") : "—") + "</td>" : "") + "<td class='dice'>" + esc(r.cau || "—") + "</td><td><span class='mau" + theo + "'>" + esc(r.mau_cau || "") + "</span></td><td style='white-space:normal;min-width:190px;font-size:12px'>" + esc((r.cau_dang_chay || []).join(" · ") || "—") + "</td><td style='white-space:normal;min-width:230px;font-size:12px'>" + esc((r.thuat_toan || []).join(" · ") || "—") + "</td><td class='c'><span class='st " + st + "'>" + ico + esc(r.trang_thai.toUpperCase()) + "</span></td></tr>";
    }).join("");
  } catch (e) { $("body").innerHTML = '<tr><td colspan="10" class="empty" style="color:#ff3d6e">Lỗi: ' + esc(e.message) + "</td></tr>"; }
}
mark(); load(); setInterval(load, 5000);
</script>
</body>
</html>`;

// Dạng LC79 / BetVip: { list: [{ id, resultTruyenThong, dices, point }] }
function parseTele(json) {
  if (!json || !Array.isArray(json.list)) throw new Error("Dữ liệu nguồn không hợp lệ");
  const parsed = json.list.map((s) => {
    const id = Number(s.id ?? s.phien ?? s.sessionId);
    const point = Number(s.point ?? s.tong ?? s.total);
    const rawDices = s.dices ?? s.xuc_xac ?? s.dice;
    const dices = Array.isArray(rawDices) ? rawDices.map(Number) : null;
    const okD = !!dices && dices.length === 3 && dices.every((d) => Number.isInteger(d) && d >= 1 && d <= 6);
    const rawResult = noDau(s.resultTruyenThong ?? s.result ?? s.ket_qua);
    const result = rawResult === "TAI" ? T : rawResult === "XIU" ? X : null;
    const diceSumMatches = okD && dices.reduce((a, v) => a + v, 0) === point;
    const isTriple = diceSumMatches && dices[0] === dices[1] && dices[1] === dices[2];
    if (!Number.isSafeInteger(id) || id <= 0 || !Number.isFinite(point) || point < 4 || point > 17 || !result || isTriple) return null;
    // Với API MD5, không dùng trường dices làm đặc trưng nếu nó không khớp point; vẫn giữ phiên nếu kết quả hợp lệ.
    return { id, result, dices: diceSumMatches ? dices : null, point };
  }).filter(Boolean);
  const byId = new Map();
  for (const h of parsed) byId.set(h.id, h);
  const hist = [...byId.values()].sort((a, b) => a.id - b.id);
  if (hist.length < 20) throw new Error("Dữ liệu nguồn không đủ phiên hợp lệ (" + hist.length + "/" + json.list.length + ")");
  return hist;
}

// ================= SERVER =================
const PORT = process.env.PORT || 3000;
const POLL_MS = 12000;
const KEEP = 300; // số phiên lưu trong lịch sử
const DATA_DIR = path.join(__dirname, "data-tonghop");
fs.mkdirSync(DATA_DIR, { recursive: true });

// Không nhúng khóa nguồn trong mã. Thiết lập KWIN_KEY trên môi trường triển khai,
// hoặc khai báo SOURCE_<TÊN_GAME> bằng URL nguồn đầy đủ cho từng game.
const KEY = String(process.env.KWIN_KEY || "").trim();
const kw = (site, p) => KEY ? `https://kwinstore.com/${site}/${p}/history/${KEY}` : "";

// Mỗi game dùng hồ sơ riêng; ưu tiên nhóm chiến lược theo nhãn. Trọng số vẫn bị giới hạn và được kiểm định walk-forward.
// LƯU Ý: xúc xắc độc lập nên hồ sơ nào cũng chỉ đạt ~50%; khác nhau ở "phong cách" chứ không phải độ chính xác.
const PROFILES = {
  ALPHA: { name: "Nhịp Cầu", re: /^(cau-|be-cau|chu-ky|lap-chuoi|run-markov|can-bang|lag-)/ },
  BETA: { name: "Markov Sâu", re: /^(markov|run-markov|can-bang|bayes|xu-huong)/ },
  GAMMA: { name: "Thống Kê Điểm", re: /^(markov-(tong|diem|xuc)|chan-le|hoi-quy|logistic|bayes|xu-huong|can-bang|lag-|cau-bet|be-cau)/ },
  OMEGA: { name: "Tổng Hợp 48", re: /./ },
};
const GAMES = {};
function addGame(key, name, source, parse, prof, hasVi) {
  const profile = PROFILES[prof];
  GAMES[key] = { key, name, parse, hasVi: !!hasVi, profile, names: ALL_NAMES, mult: prof === "OMEGA" ? null : (n) => (profile.re.test(n) ? 1.4 : 0.75), source: process.env["SOURCE_" + key.toUpperCase()] || source };
}
addGame("sunwin_tx", "Sunwin · Tài Xỉu", kw("sunwin", "tx"), parseSunwin, "OMEGA");
addGame("sunwin_sicbo", "Sunwin · Sicbo", kw("sunwin", "sicbo"), parseSunwin, "BETA", true);
addGame("hitclub_tx", "HitClub · Tài Xỉu", kw("hitclub", "tx"), parseSunwin, "ALPHA");
addGame("hitclub_md5", "HitClub · MD5", kw("hitclub", "md5"), parseSunwin, "BETA");
addGame("hitclub_sicbo", "HitClub · Sicbo", kw("hitclub", "sicbo"), parseSunwin, "GAMMA", true);
addGame("b52_hu", "B52 · Tài Xỉu Hũ", kw("b52", "hu"), parseSunwin, "OMEGA");
addGame("b52_md5", "B52 · MD5", kw("b52", "md5"), parseSunwin, "BETA");
addGame("b52_sicbo", "B52 · Sicbo", kw("b52", "sicbo"), parseSunwin, "GAMMA", true);
addGame("club789_sicbo", "789Club · Sicbo", kw("789club", "sicbo"), parseSunwin, "ALPHA", true);
addGame("lc79_tx", "LC79 · Tài Xỉu", "https://wtx.tele68.com/v1/tx/sessions", parseTele, "GAMMA");
addGame("lc79_md5", "LC79 · MD5", "https://wtxmd52.tele68.com/v1/txmd5/sessions", parseTele, "BETA");
addGame("betvip_tx", "BetVip · Tài Xỉu", "https://wtx.macminim6.online/v1/tx/sessions", parseTele, "ALPHA");
addGame("betvip_md5", "BetVip · MD5", "https://wtxmd52.macminim6.online/v1/txmd5/sessions", parseTele, "BETA");

// Giới hạn số request đồng thời tới cùng 1 máy chủ nguồn (9 game cùng gọi kwinstore, gọi dồn dập sẽ chậm/bị nghẽn)
const HOST_LIMIT = 4, hostSem = {}; // 9 game cùng gọi kwinstore: 4 luồng để 1 game chậm không chặn các game còn lại
async function withHost(url, fn) {
  const h = new URL(url).host, s = hostSem[h] || (hostSem[h] = { n: 0, q: [] });
  if (s.n >= HOST_LIMIT) await new Promise((ok) => s.q.push(ok));
  s.n++;
  try { return await fn(); } finally { s.n--; const nx = s.q.shift(); if (nx) nx(); }
}

const vn = (r) => (r === "TAI" ? "Tài" : "Xỉu");

// ---------- Tên mẫu cầu ----------
const LABELS = {
  "run-markov": "Xác suất ngắt chuỗi", "lap-chuoi": "Lặp chuỗi", "bayes-ty-le": "Bayes tỉ lệ",
  "markov-tong": "Markov điểm", "markov-diem-chinh": "Markov điểm chính xác", "markov-tong-2": "Markov 2 vùng điểm",
  "markov-xuc-xac": "Markov xúc xắc", "xu-huong": "Xu hướng EWMA", "cau-bet": "Cầu bệt", "be-cau": "Bẻ cầu", "run-markov-2": "Nhịp chuỗi kép", "cau-guong": "Cầu gương", "chan-le": "Markov chẵn/lẻ", "hoi-quy-diem": "Hồi quy điểm", "markov-xuc-xac-2": "Markov xúc xắc 2 phiên", "logistic": "Hồi quy logistic",
};
function prettyName(n) {
  if (LABELS[n]) return LABELS[n];
  let m;
  if ((m = n.match(/^markov-(\d+)$/))) return "Markov " + m[1];
  if ((m = n.match(/^chu-ky-(\d+)$/))) return "Chu kỳ " + m[1];
  if ((m = n.match(/^lag-(\d+)$/))) return "Tương quan lag " + m[1];
  if ((m = n.match(/^cau-([\d-]+)$/))) return "Cầu " + m[1];
  if ((m = n.match(/^can-bang-(\d+)$/))) return "Cân bằng " + m[1];
  return n;
}
// Mô tả cầu đang chạy theo đúng dữ liệu (chỉ là nhãn mô tả, không phải độ tin cậy)
function moTaCau(hist) {
  const seq = hist.map((h) => h.result);
  const runs = engine.toRuns(seq);
  const cur = runs[runs.length - 1];
  const lens = runs.slice(-6).map((r) => r.len);
  const l4 = lens.slice(-4);
  const same = (a) => a.length >= 4 && a.every((v) => v === a[0]);
  let ten;
  if (cur.len >= 3) ten = "Cầu bệt " + (cur.val === "TAI" ? "Tài" : "Xỉu") + " " + cur.len;
  else if (same(l4) && l4[0] === 1) ten = "Cầu 1-1";
  else if (same(l4) && l4[0] === 2) ten = "Cầu đôi " + (cur.val === "TAI" ? "TT" : "XX");
  else if (lens.length >= 3 && lens.slice(-3).every((v, i, a) => i === 0 || v === a[i - 1] + 1)) ten = "Cầu thang";
  else if (lens.length >= 3 && lens.slice(-3).every((v, i, a) => i === 0 || v === a[i - 1] - 1)) ten = "Cầu thang lùi";
  else ten = "Nhịp " + lens.slice(-4).join("-");
  const chuoi = seq.slice(-10).map((r) => (r === "TAI" ? "T" : "X")).join("");
  return chuoi + " · " + ten;
}
// Tách các chiến lược đang "bắn" thành 2 nhóm: CẦU (mẫu cầu nhìn thấy được) và THUẬT TOÁN (mô hình thống kê)
const CAU_RE = /^(cau-|be-cau|chu-ky|can-bang|lap-chuoi)/;
function tachNhom(firing) {
  const cau = [], tt = [];
  for (const [name, pk] of Object.entries(firing || {})) {
    (CAU_RE.test(name) ? cau : tt).push(prettyName(name) + "→" + vn(pk));
  }
  return { cau, tt };
}
const PRIORITY = /^(cau-|be-cau|chu-ky|run-markov|can-bang)/;
function mauCau(e, hist) {
  const last = hist[hist.length - 1].result;
  const d = "dự " + vn(e.pick);
  if (!e.top || e.fallback) return `Tín hiệu yếu (${e.strategiesFiring} model) | Đoán theo cân bằng nhịp · phiếu T:${e.pT.toFixed(2)} X:${e.pX.toFixed(2)} → ${d}`;
  const n = (e.aligned.find((x) => PRIORITY.test(x.name)) || e.top).name;
  const kind = e.pick === last ? "Theo cầu" : "Bẻ cầu";
  let m;
  if (n === "cau-bet" || n === "be-cau") {
    const len = engine.toRuns(hist.map((h) => h.result)).pop().len;
    return `${kind} – Cầu bệt ${len} | Bệt ${len} phiên → ${d}`;
  }
  if ((m = n.match(/^cau-([\d-]+)$/))) return `${kind} – Cầu ${m[1]} | Nhịp ${m[1]} → ${d}`;
  if ((m = n.match(/^can-bang-(\d+)$/))) {
    const N = +m[1], tai = hist.slice(-N).filter((h) => h.result === "TAI").length;
    return `Cân bằng ${N} phiên | Tài ${tai}/${N} → ${d}`;
  }
  return `Ensemble ${e.strategiesFiring} model | ${prettyName(n)} · phiếu T:${e.pT.toFixed(2)} X:${e.pX.toFixed(2)} → ${d}`;
}

// ---------- Trạng thái từng game ----------
for (const [key, g] of Object.entries(GAMES)) {
  g.key = key;
  g.file = path.join(DATA_DIR, `lichsu-${key}.json`);
  g.cache = { t: 0, data: null };
  g.items = {};
  try { g.items = JSON.parse(fs.readFileSync(g.file, "utf8")); } catch (_) {}
  // chỉ giữ phiên đã THỰC SỰ được dự đoán (bỏ dữ liệu walk-forward của bản cũ)
  let migrated = false;
  for (const id of Object.keys(g.items)) {
    if (g.items[id].nguon === "backfill") { delete g.items[id]; migrated = true; }
    const it = g.items[id];
    // Sửa xác suất nền của lịch sử 3 vị cũ; không thay đổi kết quả hay bộ vị đã khóa.
    if (Array.isArray(it.vi)) {
      const corrected = viProb(it.vi);
      if (it.vi_p == null || Math.abs(Number(it.vi_p) - corrected) > 1e-9) { it.vi_p = corrected; migrated = true; }
    }
  }
  if (migrated) save(g);
}

function save(g) {
  try {
    const ids = Object.keys(g.items).map(Number).sort((a, b) => b - a).slice(0, KEEP);
    const keep = {};
    for (const id of ids) keep[id] = g.items[id];
    g.items = keep;
    const tmp = g.file + ".tmp";
    fs.writeFileSync(tmp, JSON.stringify(keep));
    fs.renameSync(tmp, g.file);
  } catch (e) { console.error("Lỗi lưu lịch sử:", e.message); }
}

// ---------- Lấy dữ liệu ----------
async function fetchHistory(g, maxAge = POLL_MS) {
  if (g.cache.data && Date.now() - g.cache.t < maxAge) return { hist: g.cache.data, stale: false };
  try {
    if (!g.source) throw new Error("Thiếu KWIN_KEY hoặc SOURCE_<TÊN_GAME> trong biến môi trường");
    const __t0 = Date.now();
    let __tStart = __t0;
const json = await withHost(g.source, async () => {
      __tStart = Date.now();
      const res = await fetch(g.source, { headers: { "User-Agent": "Mozilla/5.0" }, signal: AbortSignal.timeout(25000) });
      if (!res.ok) throw new Error("Nguồn trả về HTTP " + res.status);
      return res.json();
    });
    const hist = g.parse(json);
    g.lastMs = Date.now() - __tStart; g.waitMs = __tStart - __t0; // lastMs = thời gian tải thật; waitMs = thời gian xếp hàng
    if (g.lastMs > 5000 || g.waitMs > 5000) console.warn(`[${g.key}] chậm: nguồn trả lời ${g.lastMs}ms, xếp hàng ${g.waitMs}ms`);
    g.cache = { t: Date.now(), data: hist }; g.failUntil = 0;
    sync(g, hist);
    return { hist, stale: false };
  } catch (e) {
    g.failUntil = Date.now() + FAIL_BACKOFF; g.lastErr = e.message;
    console.error(`[${g.key}] nguồn lỗi:`, e.message);
    if (g.cache.data) return { hist: g.cache.data, stale: true };
    throw e;
  }
}

const FAIL_BACKOFF = 10000; // nguồn lỗi: 10s sau mới thử lại, không bắt người xem chờ timeout
// gộp các lần gọi cùng lúc thành 1 request tới nguồn
function refresh(g, maxAge) {
  if (!g.cache.data && Date.now() < (g.failUntil || 0)) return Promise.reject(new Error(g.lastErr || "Nguồn đang lỗi"));
  if (!g.inflight) g.inflight = fetchHistory(g, maxAge).finally(() => { g.inflight = null; });
  return g.inflight;
}
// Đã có dữ liệu -> trả NGAY (không chờ nguồn), làm mới ở nền. Chỉ chờ khi chưa có dữ liệu nào (lần đầu).
function getHistory(g, maxAge = POLL_MS) {
  const age = Date.now() - g.cache.t;
  if (g.cache.data) {
    if (age >= maxAge && Date.now() >= (g.failUntil || 0)) refresh(g, maxAge).catch(() => {});
    return Promise.resolve({ hist: g.cache.data, stale: age >= POLL_MS * 4 });
  }
  return refresh(g, maxAge);
}

// Không bắt người xem chờ nguồn chậm: tối đa `ms` giây, quá thì trả lời "đang tải" (dữ liệu vẫn được tải tiếp ở nền).
function getFast(g, ms = 6000) {
  return Promise.race([getHistory(g), new Promise((_, no) => setTimeout(() => no(new Error("Đang tải dữ liệu từ nguồn, thử lại sau vài giây")), ms))]);
}

// các dự đoán đã phát ra trước phiên nid (cũ -> mới), dùng để giữ cân bằng Tài/Xỉu
function issuedPicks(g, nid) {
  return Object.values(g.items).filter((i) => i.id < nid).sort((a, b) => a.id - b.id).map((i) => i.pick);
}

// ---------- Ghi dự đoán + đối chiếu thắng/thua ----------
function sync(g, hist) {
  let changed = false;
  const byId = new Map(hist.map((h) => [h.id, h]));

  // 1) Chấm các dự đoán đã có kết quả
  for (const it of Object.values(g.items)) {
    if (!it.ket_qua) {
      const h = byId.get(it.id);
      if (h) {
        it.ket_qua = h.result; it.dices = h.dices; it.tong = h.point;
        it.thang = it.pick === h.result;
        if (it.vi) it.vi_trung = it.vi.includes(h.point);
        changed = true;
      } else if (it.id < hist[0].id) {
        delete g.items[it.id]; changed = true; // quá cũ, không còn dữ liệu để chấm
      }
    }
  }

  // 2) Khoá dự đoán cho phiên kế tiếp (không đổi khi tính lại)
  const nid = hist[hist.length - 1].id + 1;
  if (!g.items[nid]) {
    const e = withGame(g, () => predict(hist, issuedPicks(g, nid)));
    const nhom = tachNhom(e.firing);
    g.items[nid] = { id: nid, pick: e.pick, mau_cau: mauCau(e, hist), cau: moTaCau(hist), cau_ds: nhom.cau, tt_ds: nhom.tt };
    if (g.hasVi) { g.items[nid].vi = chonVi(e.pick, nid); g.items[nid].vi_p = viProb(g.items[nid].vi); }
    changed = true;
  }
  if (changed) save(g);
}

// ---------- Định dạng response ----------
function compact(g, hist) {
  const last = hist[hist.length - 1];
  const nid = last.id + 1;
  return {
    Phien: last.id,
    Xuc_xac_1: last.dices?.[0] ?? null,
    Xuc_xac_2: last.dices?.[1] ?? null,
    Xuc_xac_3: last.dices?.[2] ?? null,
    Tong: last.point,
    Ket_qua: vn(last.result),
    phien_hien_tai: nid,
    du_doan: vn(g.items[nid].pick),
    mo_hinh: g.profile.name,
    cau_dang_chay: g.items[nid].cau_ds || [],
    thuat_toan: g.items[nid].tt_ds || [],
    ...(g.hasVi ? { vi_du_doan: (g.items[nid].vi || []).join("-") } : {}),
  };
}

// Kiểm định: tỉ lệ thắng có khác 50% (ngẫu nhiên) hay không. Wilson 95% + z-test hai phía.
function erf(x) {
  const t = 1 / (1 + 0.3275911 * Math.abs(x));
  const y = 1 - (((((1.061405429 * t - 1.453152027) * t) + 1.421413741) * t - 0.284496736) * t + 0.254829592) * t * Math.exp(-x * x);
  return x >= 0 ? y : -y;
}
function kiemDinh(n, w, p0 = 0.5) {
  if (!n) return { ktc_95: "n/a", p_value: null, nhan_xet: "Chưa có dữ liệu." };
  const p = w / n, z = 1.96, z2 = z * z;
  const den = 1 + z2 / n;
  const ctr = (p + z2 / (2 * n)) / den;
  const half = (z * Math.sqrt((p * (1 - p)) / n + z2 / (4 * n * n))) / den;
  const zs = (w - n * p0) / Math.sqrt(n * p0 * (1 - p0));
  const pv = 1 - erf(Math.abs(zs) / Math.SQRT2);
  const co = (p0 * 100).toFixed(1) + "%";
  let nx;
  if (n < 30) nx = "Mẫu quá nhỏ (" + n + " phiên), chưa thể kết luận gì.";
  else if (pv < 0.05 && p > p0) nx = "Cao hơn " + co + " có p<0.05, nhưng engine ghép ~48 chiến lược nên p-value bị lạc quan; xúc xắc độc lập, phần lớn chỉ là may mắn.";
  else if (pv < 0.05) nx = "Thấp hơn " + co + " có ý nghĩa thống kê.";
  else nx = "Chưa khác mức ngẫu nhiên " + co + ".";
  return {
    ktc_95: ((ctr - half) * 100).toFixed(1) + "% – " + ((ctr + half) * 100).toFixed(1) + "%",
    p_value: +pv.toFixed(3), nhan_xet: nx,
  };
}

function thongKeVi(done) {
  const d = done.filter((i) => i.vi);
  const w = d.filter((i) => i.vi_trung).length;
  const p0 = d.length ? d.reduce((a, i) => a + (i.vi_p ?? P_VI), 0) / d.length : P_VI;
  return {
    tong: d.length, trung: w, ti_le: d.length ? ((w / d.length) * 100).toFixed(1) + "%" : "n/a",
    co_so: (p0 * 100).toFixed(1) + "%", ...kiemDinh(d.length, w, p0),
  };
}

function lichsu(g, limit) {
  const all = Object.values(g.items).sort((a, b) => b.id - a.id);
  const done = all.filter((i) => i.ket_qua);
  const win = done.filter((i) => i.thang).length;
  return {
    game: g.key,
    mo_hinh: g.profile.name,
    thong_ke: {
      luu_y: "Mỗi phiên xúc xắc độc lập: không mẫu cầu nào dự đoán được phiên sau, kỳ vọng thắng ~50%. 'phiếu T/X' là tỉ lệ phiếu của các mẫu cầu, KHÔNG phải xác suất thật.",
      tong: done.length, thang: win, thua: done.length - win,
      ti_le_thang: done.length ? ((win / done.length) * 100).toFixed(1) + "%" : "n/a",
      ...kiemDinh(done.length, win),
      ...(g.hasVi ? { vi: thongKeVi(done) } : {}),
    },
    danh_sach: all.slice(0, limit).map((i) => ({
      Phien: i.id,
      Xuc_xac: i.dices || null,
      Tong: i.tong ?? null,
      du_doan: vn(i.pick),
      Ket_qua: i.ket_qua ? vn(i.ket_qua) : null,
      cau: i.cau || "",
      vi: i.vi || null,
      vi_trung: i.vi && i.ket_qua ? !!i.vi_trung : null,
      mau_cau: i.mau_cau,
      cau_dang_chay: i.cau_ds || [],
      thuat_toan: i.tt_ds || [],
      trang_thai: !i.ket_qua ? "Chờ" : i.thang ? "Thắng" : "Thua",
    })),
  };
}

function full(g, hist, stale) {
  const last = hist[hist.length - 1];
  const signature = hist.map((h) => `${h.id}:${h.result}`).join("|");
  // Các phép tính backtest/thống kê khá nặng; giữ kết quả theo phiên để request chỉ đọc cache.
  if (!g.analysisCache || g.analysisCache.signature !== signature) {
    g.analysisCache = {
      signature,
      prediction: withGame(g, () => engine.predict(hist, issuedPicks(g, last.id + 1))),
      backtest: withGame(g, () => engine.backtest(hist)),
      stats: engine.stats(hist),
      pickBalance: withGame(g, () => engine.pickShare(hist)),
    };
  }
  const a = g.analysisCache;
  return {
    game: g.key, totalStrategies: Object.keys(STRATEGIES).length, updatedAt: new Date().toISOString(), stale,
    latest: last, nextSessionId: last.id + 1,
    prediction: a.prediction,
    predictionNote: "Tỷ trọng phiếu không phải xác suất thắng; nhãn WEAK/CONSENSUS mô tả độ đồng thuận của mô hình, không bảo đảm kết quả.",
    lockedPick: g.items[last.id + 1] ? g.items[last.id + 1].pick : null,
    lockedVi: g.items[last.id + 1] ? g.items[last.id + 1].vi || null : null,
    backtest: a.backtest,
    stats: a.stats,
    pickBalance: a.pickBalance,
  };
}

// ---------- Routes ----------
const app = express();
app.use(cors());

const wrap = (fn) => async (req, res) => {
  try { await fn(req, res); } catch (e) { res.status(502).json({ error: e.message }); }
};
const limitOf = (req) => Math.min(Math.max(parseInt(req.query.limit) || 30, 1), KEEP);
const both = async (req) => {
  const n = limitOf(req);
  const out = {};
  await Promise.all(Object.values(GAMES).map(async (g) => {
    let loi = null;
    try { await getFast(g); } catch (e) { loi = e.message; }
    out[g.key] = lichsu(g, n);
    if (loi) out[g.key].loi = loi;
  }));
  const res = {};
  for (const k of Object.keys(GAMES)) res[k] = out[k];
  return res;
};

app.get("/", (req, res) => res.redirect("/lichsu"));

// /lichsu: trình duyệt -> bảng HTML | app/curl -> JSON
LICHSU_HTML = LICHSU_HTML.replace("__TABS__", JSON.stringify(Object.values(GAMES).map((g) => [g.key, g.name]))).replace(/TỔNG HỢP/g, "TỔNG HỢP");
app.get("/lichsu", wrap(async (req, res) => {
  if (req.accepts(["json", "html"]) === "html") return res.type("html").send(LICHSU_HTML);
  res.json(await both(req));
}));
app.get("/lichsu.json", wrap(async (req, res) => res.json(await both(req))));

for (const key of Object.keys(GAMES)) {
  const g = GAMES[key];
  app.get("/" + key, wrap(async (req, res) => { const { hist } = await getFast(g, 8000); res.json(compact(g, hist)); }));
  app.get("/api/" + key, wrap(async (req, res) => { const { hist, stale } = await getFast(g, 8000); res.json(full(g, hist, stale)); }));
  app.get("/lichsu/" + key, wrap(async (req, res) => {
    await getFast(g, 8000).catch(() => {}); // có dữ liệu thì trả ngay + làm mới ở nền; chỉ chờ lần đầu
    res.json(lichsu(g, limitOf(req)));
  }));
}
app.get("/health", (req, res) => res.json({ ok: true, nguon_ms: Object.fromEntries(Object.values(GAMES).map((g) => [g.key, g.lastMs ?? null])), cho_hang_ms: Object.fromEntries(Object.values(GAMES).map((g) => [g.key, g.waitMs ?? null])) }));

// Poll nền để dự đoán luôn được ghi + chấm dù không ai mở web. Mỗi game 1 vòng riêng, xuất phát so le để không dồn request.
function startPolling() {
  Object.values(GAMES).forEach((g, i) => {
    const tick = () => {
      const wait = Date.now() < (g.failUntil || 0) ? FAIL_BACKOFF : POLL_MS;
      refresh(g, 0).catch((e) => console.error(`[${g.key}]`, e.message)).finally(() => setTimeout(tick, wait));
    };
    setTimeout(tick, i * 700);
  });
}

app.listen(PORT, () => {
  console.log(`\n  TỔNG HỢP chạy tại http://localhost:${PORT}  (${Object.keys(GAMES).length} game)`);
  console.log("  /lichsu (bảng HTML) | /lichsu.json | /health");
  for (const g of Object.values(GAMES)) console.log(`  /${g.key}  /api/${g.key}  /lichsu/${g.key}   [${g.profile.name}]`);
  console.log("");
  startPolling();
});
