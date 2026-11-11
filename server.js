// 수완 종합게임 — 실시간 서버 (홀덤 · 블랙잭)
// 실행: npm start  (외부 패키지 없음. PORT 환경변수가 있으면 그 포트 사용)
// 서버 → 화면: Server-Sent Events(/events), 화면 → 서버: POST /api
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');

const PORT = process.env.PORT || 3000;
// 검색엔진 소유 확인 코드: Render 환경변수 GOOGLE_VERIFY / NAVER_VERIFY 에 넣으면 페이지에 자동으로 들어가요
const VERIFY_META = [
  process.env.GOOGLE_VERIFY ? `<meta name="google-site-verification" content="${String(process.env.GOOGLE_VERIFY).replace(/[^\w\-]/g, '')}">` : '',
  process.env.NAVER_VERIFY ? `<meta name="naver-site-verification" content="${String(process.env.NAVER_VERIFY).replace(/[^\w\-]/g, '')}">` : ''
].join('');
const PAGE = Buffer.from(fs.readFileSync(path.join(__dirname, 'index.html'), 'utf8').replace('<!--VERIFY-->', VERIFY_META));
const PAGE_GZ = zlib.gzipSync(PAGE, { level: 9 });
const PAGE_ETAG = '"' + crypto.createHash('sha1').update(PAGE).digest('hex').slice(0, 16) + '"';

/* ---------------- 카드 & 족보 ---------------- */
const RANKS = '23456789TJQKA', SUITS = 'shdc';
const randInt = n => crypto.randomInt(n);
function newDeck() {
  const d = [];
  for (const r of RANKS) for (const s of SUITS) d.push(r + s);
  for (let i = d.length - 1; i > 0; i--) { const j = randInt(i + 1); [d[i], d[j]] = [d[j], d[i]]; }
  return d;
}
// 점수 배열: [족보 등급, 비교용 숫자들...] — 앞에서부터 비교해서 큰 쪽이 이김, 전부 같으면 무승부
function eval5(cs) {
  const rs = cs.map(c => RANKS.indexOf(c[0])).sort((a, b) => b - a);
  const flush = cs.every(c => c[1] === cs[0][1]);
  const uniq = [...new Set(rs)];
  let sh = -1;
  if (uniq.length === 5) { if (uniq[0] - uniq[4] === 4) sh = uniq[0]; else if (uniq[0] === 12 && uniq[1] === 3) sh = 3; }
  const cnt = {}; rs.forEach(r => cnt[r] = (cnt[r] || 0) + 1);
  const g = Object.entries(cnt).map(([r, c]) => [+r, c]).sort((a, b) => b[1] - a[1] || b[0] - a[0]);
  const gr = g.map(x => x[0]);
  if (sh >= 0 && flush) return [8, sh];
  if (g[0][1] === 4) return [7, ...gr];
  if (g[0][1] === 3 && g[1][1] === 2) return [6, ...gr];
  if (flush) return [5, ...rs];
  if (sh >= 0) return [4, sh];
  if (g[0][1] === 3) return [3, ...gr];
  if (g[0][1] === 2 && g[1][1] === 2) return [2, ...gr];
  if (g[0][1] === 2) return [1, ...gr];
  return [0, ...rs];
}
function cmpScore(a, b) { for (let i = 0; i < Math.max(a.length, b.length); i++) { const d = (a[i] ?? -1) - (b[i] ?? -1); if (d) return d; } return 0; }
// 7장 중 가장 좋은 5장과 점수
function bestHand(cards) {
  let best = null, bestCards = null; const n = cards.length;
  const pick = (start, acc) => {
    if (acc.length === 5) { const s = eval5(acc); if (!best || cmpScore(s, best) > 0) { best = s; bestCards = acc; } return; }
    for (let i = start; i <= n - (5 - acc.length); i++) pick(i + 1, [...acc, cards[i]]);
  };
  pick(0, []);
  return { score: best, cards: bestCards };
}
const RN = r => r === 8 ? '10' : RANKS[r];
function handName(s) {
  switch (s[0]) {
    case 8: return s[1] === 12 ? '로열 플러시' : `${RN(s[1])} 스트레이트 플러시`;
    case 7: return `${RN(s[1])} 포카드`;
    case 6: return `${RN(s[1])} 풀하우스`;
    case 5: return `${RN(s[1])} 하이 플러시`;
    case 4: return `${RN(s[1])} 하이 스트레이트`;
    case 3: return `${RN(s[1])} 트리플`;
    case 2: return `${RN(s[1])}·${RN(s[2])} 투페어`;
    case 1: return `${RN(s[1])} 원페어`;
    default: return `${RN(s[1])} 하이`;
  }
}
// 최종 5장을 족보 순서대로 (예: 10 10 A K Q)
function fiveLabel(cards) {
  const cnt = {}; cards.forEach(c => { cnt[c[0]] = (cnt[c[0]] || 0) + 1; });
  return [...cards].sort((a, b) => (cnt[b[0]] - cnt[a[0]]) || (RANKS.indexOf(b[0]) - RANKS.indexOf(a[0]))).map(c => c[0] === 'T' ? '10' : c[0]).join(' ');
}
// 같은 족보 이름인데 승부가 갈렸으면, 갈린 카드를 설명
function kickerNote(win, lose) {
  if (!lose || win[0] !== lose[0] || handName(win) !== handName(lose)) return '';
  for (let i = 1; i < win.length; i++) if (win[i] !== lose[i]) return `킥커 ${RN(win[i])}`;
  return '';
}
const fmt = n => Number(n || 0).toLocaleString('ko-KR');
const BETTING = new Set(['pre', 'flop', 'turn', 'river']);
const CODE_ABC = 'ABCDEFGHJKLMNPQRSTUVWXYZ23456789';
const EMOJIS = ['😂', '👍', '🔥', '😱', '😭', '🤔', '👏', '😎', '🙏', '💸', '🤬', '❤️'];

/* ---------------- AI 플레이어 ---------------- */
// 서버 안에서 돌아가는 규칙 기반 AI. 외부 API를 쓰지 않아서 비용이 없어요.
// 몬테카를로로 승률(이길 확률)을 어림잡고, 팟 오즈·포지션·난이도에 따라 행동을 고릅니다.
const BOT_NAMES = ['철수', '영희', '도윤', '하린', '준호', '서아', '민재', '지아', '태오', '유나'];
const BOT_LEVELS = {
  easy:   { label: '쉬움',   sims: 250, noise: 0.14, loose: 0.30, aggr: 0.55, bluff: 0.05, slow: [900, 1900] },
  normal: { label: '보통',   sims: 600, noise: 0.07, loose: 0.12, aggr: 0.85, bluff: 0.10, slow: [1100, 2600] },
  hard:   { label: '어려움', sims: 1200, noise: 0.03, loose: 0.02, aggr: 1.05, bluff: 0.14, slow: [1200, 3200] },
  // 챌린지 보스 전용 (상대 습관을 읽고 범위로 계산하는 고수 AI)
  pro:    { label: '고수',   sims: 1100, noise: 0.025, pro: 1, exploit: 0.55, slow: [1200, 3000] },
  boss:   { label: '극악',   sims: 2200, noise: 0, pro: 1, exploit: 1, slow: [1300, 3200] }
};
const FULL_DECK = (() => { const d = []; for (const r of RANKS) for (const su of SUITS) d.push(r + su); return d; })();
const rnd = () => Math.random();
// 빠른 7장 족보 점수 (AI 계산용). 카드 = 숫자(랭크*4+무늬), 큰 숫자가 강한 패, 같으면 무승부.
const B13 = [1, 13, 169, 2197, 28561, 371293];
const CARD_INT = Object.fromEntries(FULL_DECK.map(c => [c, RANKS.indexOf(c[0]) * 4 + SUITS.indexOf(c[1])]));
const _rc = new Int8Array(13), _sm = new Int32Array(4), _sc = new Int8Array(4);
function straightHigh(mask) {
  const m = (mask << 1) | ((mask >> 12) & 1); // 0번 비트 = A를 1로 쓰는 경우
  for (let h = 12; h >= 3; h--) if (((m >> (h - 3)) & 31) === 31) return h;
  return -1;
}
function topBits(mask, n) { const out = []; for (let r = 12; r >= 0 && out.length < n; r--) if (mask & (1 << r)) out.push(r); return out; }
function packScore(cat, ks) { let v = cat * B13[5]; for (let k = 0; k < ks.length; k++) v += ks[k] * B13[4 - k]; return v; }
function eval7i(cs) {
  _rc.fill(0); _sm.fill(0); _sc.fill(0);
  let rmask = 0;
  for (let k = 0; k < cs.length; k++) { const c = cs[k], r = c >> 2, su = c & 3; _rc[r]++; rmask |= 1 << r; _sm[su] |= 1 << r; _sc[su]++; }
  let flushMask = 0;
  for (let su = 0; su < 4; su++) if (_sc[su] >= 5) flushMask = _sm[su];
  if (flushMask) { const sf = straightHigh(flushMask); if (sf >= 0) return packScore(8, [sf]); }
  let quad = -1, t1 = -1, t2 = -1, p1 = -1, p2 = -1, p3 = -1;
  for (let r = 12; r >= 0; r--) {
    const n = _rc[r];
    if (n === 4) quad = r;
    else if (n === 3) { if (t1 < 0) t1 = r; else if (t2 < 0) t2 = r; }
    else if (n === 2) { if (p1 < 0) p1 = r; else if (p2 < 0) p2 = r; else if (p3 < 0) p3 = r; }
  }
  if (quad >= 0) return packScore(7, [quad, topBits(rmask & ~(1 << quad), 1)[0]]);
  if (t1 >= 0 && (t2 >= 0 || p1 >= 0)) return packScore(6, [t1, Math.max(t2, p1)]);
  if (flushMask) return packScore(5, topBits(flushMask, 5));
  const st = straightHigh(rmask);
  if (st >= 0) return packScore(4, [st]);
  if (t1 >= 0) return packScore(3, [t1, ...topBits(rmask & ~(1 << t1), 2)]);
  if (p1 >= 0 && p2 >= 0) return packScore(2, [p1, p2, topBits(rmask & ~(1 << p1) & ~(1 << p2), 1)[0]]);
  if (p1 >= 0) return packScore(1, [p1, ...topBits(rmask & ~(1 << p1), 3)]);
  return packScore(0, topBits(rmask, 5));
}
function equity(hole, board, opps, sims) {
  if (opps <= 0) return 1;
  const known = new Set([...hole, ...board]);
  const rest = FULL_DECK.filter(c => !known.has(c)).map(c => CARD_INT[c]);
  const h = hole.map(c => CARD_INT[c]), b = board.map(c => CARD_INT[c]);
  const need = 5 - b.length, take = need + opps * 2;
  const mine7 = new Array(7), opp7 = new Array(7);
  let score = 0;
  for (let k = 0; k < sims; k++) {
    for (let i = 0; i < take; i++) { const j = i + Math.floor(rnd() * (rest.length - i)); const t = rest[i]; rest[i] = rest[j]; rest[j] = t; }
    for (let i = 0; i < b.length; i++) { mine7[2 + i] = b[i]; opp7[2 + i] = b[i]; }
    for (let i = 0; i < need; i++) { mine7[2 + b.length + i] = rest[i]; opp7[2 + b.length + i] = rest[i]; }
    mine7[0] = h[0]; mine7[1] = h[1];
    const mine = eval7i(mine7);
    let lose = false, ties = 0;
    for (let o = 0; o < opps; o++) {
      opp7[0] = rest[need + o * 2]; opp7[1] = rest[need + o * 2 + 1];
      const p = eval7i(opp7);
      if (p > mine) { lose = true; break; }
      if (p === mine) ties++;
    }
    if (!lose) score += 1 / (ties + 1);
  }
  return score / sims;
}
function botDecide(room, i) {
  const hd = room.hand, s = room.seats[i], L = BOT_LEVELS[s.lv] || BOT_LEVELS.normal;
  if (L.pro) return proDecide(room, i);
  const hole = hd.holes[s.pid];
  const live = room.seats.filter((o, k) => k !== i && o.inHand && !o.folded);
  const opps = Math.max(1, live.length);
  let eq = equity(hole, hd.bd, opps, L.sims);
  eq = Math.min(1, Math.max(0, eq + (rnd() * 2 - 1) * L.noise));
  const fair = 1 / (opps + 1);
  const rel = eq / fair;                        // 1보다 크면 평균보다 강한 패
  const pot = hd.pot + room.seats.reduce((a, o) => a + o.bet, 0);
  const toCall = Math.max(0, hd.cb - s.bet);
  const maxT = s.bet + s.stack;
  const bb = room.settings.bb;
  const canRaise = !s.acted && maxT > hd.cb && room.seats.some((o, k) => k !== i && o.inHand && !o.folded && !o.allIn);
  const minT = hd.cb === 0 ? Math.min(bb, maxT) : Math.min(hd.cb + hd.mr, maxT);
  const sizeTo = frac => {
    let t = hd.cb + Math.max(hd.mr, Math.round((pot + toCall) * frac / bb) * bb);
    if (hd.cb === 0) t = Math.max(bb, Math.round(pot * frac / bb) * bb);
    t = Math.max(minT, Math.min(maxT, t));
    if (t > maxT * 0.7) t = maxT; // 스택 대부분이면 그냥 올인
    return t;
  };
  const late = hd.st === 'turn' || hd.st === 'river';
  if (toCall === 0) {
    if (canRaise && rel > 1.55 / L.aggr && rnd() < 0.85) return ['raise', sizeTo(rel > 2.2 ? 0.8 : 0.55)];
    if (canRaise && hd.st !== 'pre' && rnd() < L.bluff * (late ? 1.3 : 0.8)) return ['raise', sizeTo(0.5)];
    return ['check'];
  }
  const potOdds = toCall / (pot + toCall);
  const big = toCall > s.stack * 0.5;             // 큰 베팅에는 더 신중
  const needEq = potOdds * (1 - L.loose) + (big ? 0.06 : 0);
  if (eq < needEq) {
    if (toCall <= bb && hd.st === 'pre' && rnd() < 0.5 + L.loose) return ['call'];
    if (canRaise && !big && rnd() < L.bluff * 0.4) return ['raise', sizeTo(0.7)];
    return ['fold'];
  }
  if (canRaise && rel > 1.75 / L.aggr && rnd() < 0.7) {
    if (rel > 2.6 && rnd() < 0.35) return ['allin'];
    return ['raise', sizeTo(rel > 2.2 ? 0.9 : 0.6)];
  }
  return ['call'];
}

/* ---------------- 고수 AI (챌린지 4·5단계 보스) ---------------- */
// 1) 시작할 때 169가지 손패의 강함(무작위 1명 상대 승률)을 미리 계산 → "상위 몇 %" 표
// 2) 상대가 이번 판에 한 행동(레이즈/콜/체크)으로 상대 손패 범위를 좁혀서 승률 계산
// 3) 상대 습관(얼마나 자주 참여·레이즈·폴드하는지)을 판마다 기록해서 블러핑·콜 기준을 조절
const PRE = (() => {
  const t0 = Date.now(), list = [];
  const deck = FULL_DECK.map(c => CARD_INT[c]);
  for (let a = 12; a >= 0; a--) for (let b = a; b >= 0; b--) {
    for (const kind of a === b ? ['p'] : ['s', 'o']) {
      const h1 = a * 4, h2 = b * 4 + (kind === 's' ? 0 : 1);
      const rest = deck.filter(c => c !== h1 && c !== h2);
      let sc = 0; const S = 900, m = new Array(7), o = new Array(7);
      for (let k = 0; k < S; k++) {
        for (let i = 0; i < 7; i++) { const j = i + Math.floor(rnd() * (rest.length - i)); const t = rest[i]; rest[i] = rest[j]; rest[j] = t; }
        m[0] = h1; m[1] = h2; o[0] = rest[5]; o[1] = rest[6];
        for (let i = 0; i < 5; i++) { m[2 + i] = rest[i]; o[2 + i] = rest[i]; }
        const x = eval7i(m), y = eval7i(o); sc += x > y ? 1 : x === y ? 0.5 : 0;
      }
      list.push({ key: a + ',' + b + kind, eq: sc / S, n: kind === 'p' ? 6 : kind === 's' ? 4 : 12 });
    }
  }
  list.sort((x, y) => y.eq - x.eq);
  const map = {}; let cum = 0;
  for (const x of list) { map[x.key] = { eq: x.eq, pct: (cum + x.n / 2) / 1326 }; cum += x.n; }
  if (require.main === module) console.log(`프리플랍 표 계산 ${Date.now() - t0}ms`);
  return map;
})();
function preKeyI(c1, c2) { const r1 = c1 >> 2, r2 = c2 >> 2, a = Math.max(r1, r2), b = Math.min(r1, r2); return a + ',' + b + (a === b ? 'p' : (c1 & 3) === (c2 & 3) ? 's' : 'o'); }
const prePct = (c1, c2) => PRE[preKeyI(c1, c2)].pct;
const catOf = sc => Math.floor(sc / B13[5]);
// 드로우: 플러시 드로우(같은 무늬 4장, 내 카드 포함) / 양방향 스트레이트 드로우
function drawInfo(h, b) {
  if (b.length < 3 || b.length >= 5) return { fd: false, oe: false };
  const all = [...h, ...b];
  let fd = false;
  for (let su = 0; su < 4; su++) { const n = all.filter(c => (c & 3) === su).length; if (n === 4 && h.some(c => (c & 3) === su)) fd = true; }
  let mask = 0; for (const c of all) mask |= 1 << (c >> 2);
  let outs = 0;
  if (straightHigh(mask) < 0) for (let r = 0; r < 13; r++) if (!(mask & (1 << r)) && straightHigh(mask | (1 << r)) >= 0) outs++;
  return { fd, oe: outs >= 2 };
}
// 상대 손패가 지금 보드와 얼마나 잘 맞는지 (페어 이상 또는 강한 드로우면 "맞음")
function connects(h, b) {
  if (b.length < 3) return true;
  const base = catOf(eval7i(b)), mine = catOf(eval7i([...h, ...b]));
  if (mine > base) return true;
  const d = drawInfo(h, b); return d.fd || d.oe;
}
// 사람 플레이어 습관 기록 (방마다)
function oppStats(room, pid) {
  if (!room.opp) room.opp = new Map();
  let s = room.opp.get(pid);
  if (!s) { s = { hands: 0, vpip: 0, pfr: 0, bets: 0, calls: 0, checks: 0, faced: 0, folds: 0 }; room.opp.set(pid, s); }
  return s;
}
function oppModel(room, o, ex) {
  const st = oppStats(room, o.pid), hx = o.hx || {};
  const mix = (obs, n, prior, w) => prior + (n > 0 ? (obs / n - prior) * Math.min(1, n / w) * ex : 0);
  const vpip = mix(st.vpip, st.hands, 0.55, 25), pfr = mix(st.pfr, st.hands, 0.25, 25);
  const af = mix(st.bets, st.bets + st.calls + st.checks, 0.35, 30), fold = mix(st.folds, st.faced, 0.42, 20);
  let top = 1;
  if (hx.pf === '3') top = Math.max(0.04, Math.min(0.22, pfr * 0.45));
  else if (hx.pf === 'r') top = Math.max(0.12, Math.min(0.75, pfr * 1.15));
  else if (hx.pf === 'c') top = Math.max(0.3, Math.min(0.95, vpip));
  const agg = !!(hx.agg && Object.keys(hx.agg).length), called = !!(hx.call && Object.keys(hx.call).length);
  const air = Math.max(0.06, Math.min(0.6, 0.2 + (af - 0.35) * 0.9));
  return { top, agg, called, air, fold, af };
}
function rangeEquity(hole, board, models, sims) {
  if (!models.length) return 1;
  const known = new Set([...hole, ...board]);
  const rest = FULL_DECK.filter(c => !known.has(c)).map(c => CARD_INT[c]);
  const h = hole.map(c => CARD_INT[c]), b = board.map(c => CARD_INT[c]);
  const need = 5 - b.length, N = rest.length;
  const used = new Uint8Array(64);
  const mine7 = new Array(7), opp7 = new Array(7);
  let score = 0;
  const weight = (m, c1, c2) => {
    let w = prePct(c1, c2) <= m.top ? 1 : 0.05;
    if (b.length >= 3 && (m.agg || m.called)) w *= connects([c1, c2], b) ? 1 : (m.agg ? m.air : 0.4);
    return w;
  };
  for (let k = 0; k < sims; k++) {
    used.fill(0);
    const pick = () => { for (;;) { const c = rest[Math.floor(rnd() * N)]; if (!used[c]) { used[c] = 1; return c; } } };
    const oh = [];
    for (const m of models) {
      let c1, c2;
      for (let t = 0; t < 14; t++) {
        c1 = pick(); c2 = pick();
        if (t === 13 || rnd() < weight(m, c1, c2)) break;
        used[c1] = 0; used[c2] = 0;
      }
      oh.push(c1, c2);
    }
    for (let i = 0; i < b.length; i++) { mine7[2 + i] = b[i]; opp7[2 + i] = b[i]; }
    for (let i = 0; i < need; i++) { const c = pick(); mine7[2 + b.length + i] = c; opp7[2 + b.length + i] = c; }
    mine7[0] = h[0]; mine7[1] = h[1];
    const mine = eval7i(mine7);
    let lose = false, ties = 0;
    for (let o = 0; o < models.length; o++) {
      opp7[0] = oh[o * 2]; opp7[1] = oh[o * 2 + 1];
      const p = eval7i(opp7);
      if (p > mine) { lose = true; break; }
      if (p === mine) ties++;
    }
    if (!lose) score += 1 / (ties + 1);
  }
  return score / sims;
}
function proDecide(room, i) {
  const hd = room.hand, s = room.seats[i], L = BOT_LEVELS[s.lv];
  const ex = L.exploit;
  const hole = hd.holes[s.pid], hI = hole.map(c => CARD_INT[c]), bI = hd.bd.map(c => CARD_INT[c]);
  const opps = room.seats.filter((o, k) => k !== i && o.inHand && !o.folded);
  const models = opps.map(o => oppModel(room, o, ex));
  let eq = rangeEquity(hole, hd.bd, models, L.sims);
  eq = Math.min(1, Math.max(0, eq + (rnd() * 2 - 1) * L.noise));
  const bb = room.settings.bb;
  const bets = room.seats.reduce((a, o) => a + o.bet, 0);
  const pot = hd.pot + bets;
  const toCall = Math.max(0, hd.cb - s.bet);
  const maxT = s.bet + s.stack;
  const canRaise = !s.acted && maxT > hd.cb && room.seats.some((o, k) => k !== i && o.inHand && !o.folded && !o.allIn);
  const minT = hd.cb === 0 ? Math.min(bb, maxT) : Math.min(hd.cb + hd.mr, maxT);
  const effStack = Math.min(maxT, Math.max(...opps.map(o => o.stack + o.bet), 0));
  const hu = opps.length === 1;
  const fold = models.reduce((a, m) => a + m.fold, 0) / Math.max(1, models.length);
  const potOdds = toCall / (pot + toCall);
  const pct = prePct(hI[0], hI[1]);
  const clampT = t => { t = Math.max(minT, Math.min(maxT, Math.round(t / 10) * 10)); if (t > maxT * 0.62) t = maxT; return t; };
  const betPot = frac => clampT(hd.cb + Math.max(hd.mr, (pot + toCall) * frac));
  const R = (t) => canRaise ? (t >= maxT ? ['allin'] : ['raise', t]) : (toCall > 0 ? ['call'] : ['check']);
  const st = hd.st, nr = hd.nr || 0;

  if (st === 'pre') {
    const bbs = effStack / bb;
    const opened = nr > 0;
    if (bbs <= 13) { // 짧은 스택: 올인 아니면 폴드
      if (!opened) {
        const pushTop = hu ? Math.min(1, 0.32 + (13 - bbs) * 0.06) : Math.min(0.8, 0.14 + (13 - bbs) * 0.045);
        if (pct <= pushTop && canRaise) return ['allin'];
        return toCall === 0 ? ['check'] : ['fold'];
      }
      if (eq >= potOdds + 0.02) return canRaise && pct <= 0.1 ? ['allin'] : ['call'];
      return ['fold'];
    }
    if (!opened) {
      const limpers = room.seats.filter(o => o.inHand && !o.folded && o.bet >= bb && o !== s).length - 1;
      if (toCall === 0) { // BB 옵션
        if (canRaise && pct <= (hu ? 0.32 : 0.14)) return R(clampT(bb * (3.5 + Math.max(0, limpers))));
        return ['check'];
      }
      const openTop = hu ? 0.82 : opps.length === 2 ? 0.42 : 0.28;
      if (pct <= openTop && canRaise) return R(clampT(bb * (hu ? 2.5 : 3) + Math.max(0, limpers) * bb));
      return ['fold'];
    }
    if (nr === 1) {
      if (canRaise && pct <= 0.07) return R(clampT(hd.cb * 3.2));
      if (canRaise && hu && pct > 0.12 && pct < 0.3 && rnd() < 0.22 * (0.6 + fold)) return R(clampT(hd.cb * 3.2));
      if (eq >= potOdds + (hu ? -0.03 : 0.04)) return ['call'];
      return ['fold'];
    }
    if (canRaise && pct <= 0.022) return ['allin'];
    if (eq >= potOdds + 0.03) return ['call'];
    return ['fold'];
  }
  const d = drawInfo(hI, bI);
  const drawy = d.fd || d.oe;
  const spr = effStack / Math.max(1, pot);
  const iAgg = hd.pfAgg === s.id;
  if (toCall === 0) {
    if (canRaise) {
      const valueT = hu ? 0.6 : 0.67;
      if (eq >= 0.84 && spr < 2.2) return ['allin'];
      if (eq >= valueT) return R(betPot(eq > 0.8 ? (st === 'river' ? 0.95 : 0.75) : 0.58));
      if (st === 'flop' && iAgg && hu && rnd() < 0.5 + ex * (fold - 0.42)) return R(betPot(0.35));
      if (st !== 'river' && drawy && rnd() < 0.55) return R(betPot(0.6));
      const bl = Math.max(0.03, Math.min(0.42, 0.1 + ex * (fold - 0.42) * 1.2)) * (st === 'river' ? 1 : 0.7);
      if (eq < 0.35 && rnd() < bl) return R(betPot(st === 'river' ? 0.75 : 0.55));
    }
    return ['check'];
  }
  const margin = st === 'flop' ? 0.02 : st === 'turn' ? 0.03 : 0;
  const implied = st !== 'river' && drawy ? 0.05 : 0;
  if (canRaise) {
    if (eq >= 0.84 && (spr < 3 || rnd() < 0.45)) return ['allin'];
    if (eq >= (st === 'river' ? 0.74 : 0.7) && rnd() < 0.75) return R(clampT(hd.cb * 2.8 + (pot - bets) * 0.3));
    if (st === 'flop' && d.fd && d.oe && rnd() < 0.5) return R(clampT(hd.cb * 3));
    if (st !== 'river' && drawy && hu && rnd() < 0.14) return R(clampT(hd.cb * 2.8));
  }
  if (eq + implied >= potOdds + margin) return ['call'];
  return ['fold'];
}

/* ---------------- 행운 모드 (비밀) ---------------- */
// Render 환경변수 LUCKY_PW 로 바꿀 수 있어요. 없으면 기본값 사용.
const LUCKY_PW = process.env.LUCKY_PW || '0104';
const LUCKY_RATE = 0.92; // 92%는 이기는 판, 나머지 8%는 지는 판 (티 안 나게)
const pwFails = new Map();
// 관리자: 같은 비밀번호로 로그인하면 12시간짜리 토큰을 줌. 토큰이 있으면 모든 방 목록을 보고 몰래 관전 가능
const ADMIN_PW = process.env.ADMIN_PW || '0104';
const adminTokens = new Map(); // token -> 만료 시각
function isAdmin(tok) { const t = adminTokens.get(String(tok || '')); if (!t) return false; if (Date.now() > t) { adminTokens.delete(String(tok)); return false; } return true; }

/* ---------------- 방 ---------------- */
const rooms = new Map();

class Room {
  constructor(code) {
    this.code = code;
    this.created = Date.now();
    this.hostPid = null;
    this.settings = { stack: 1000, sb: 10, bb: 20, timer: 30 };
    this.status = 'lobby';
    this.seats = [];
    this.hand = this.blankHand(0);
    this.chat = [];
    this.chatI = 0;
    this.socks = new Set();
    this.msg = '';
    this.champ = '';
    this.turnStart = 0; this.runoutAt = 0; this.nextAt = 0;
    this.emptySince = Date.now();
    this.dirty = false;
    this.botFor = -1; this.botAt = 0;
    this.banned = new Set();
    this.stats = null;
  }
  /* ---- 순위 기록 (게임 시작부터) ---- */
  statInit() { this.stats = new Map(); for (const s of this.seats) this.statAdd(s); }
  statAdd(s) { if (!this.stats || this.stats.has(s.id)) return; this.stats.set(s.id, { n: s.name, bot: !!s.bot, buy: s.stack, g: 0, w: 0, b: 0, stack: s.stack }); }
  statBuy(s, amt) { const st = this.stats && this.stats.get(s.id); if (st && amt > 0) st.buy += amt; }
  statHand(s, profit) {
    if (!this.stats) return;
    if (!this.stats.has(s.id)) { this.statAdd(s); this.stats.get(s.id).buy = s.stack - profit; }
    const st = this.stats.get(s.id);
    st.g++; if (profit > 0) { st.w++; if (profit > st.b) st.b = profit; }
    st.n = s.name; st.stack = s.stack;
  }
  ranking() {
    if (!this.stats) return [];
    const here = new Map(this.seats.map(s => [s.id, s]));
    const arr = [];
    for (const [id, st] of this.stats) {
      const s = here.get(id);
      if (s) { st.stack = s.stack; st.n = s.name; }
      arr.push({ id, n: st.n, bot: st.bot ? 1 : 0, p: st.stack - st.buy, w: st.w, g: st.g, b: st.b, here: s && !s.kicked ? 1 : 0 });
    }
    arr.sort((a, b) => b.p - a.p || b.w - a.w || a.n.localeCompare(b.n));
    return arr;
  }
  rankLog() {
    const rk = this.ranking().filter(x => x.g > 0); if (!rk.length) return;
    const m = ['🥇', '🥈', '🥉'];
    this.log('🏆 최종 순위 · ' + rk.slice(0, 6).map((x, i) => `${m[i] || (i + 1) + '위'} ${x.n} ${x.p > 0 ? '+' : ''}${fmt(x.p)}`).join(' / '));
  }
  /* ---- 방장 칩 지급 ---- */
  seatBusy(seat) { return this.status === 'playing' && !!seat.inHand && !this.safeToRemove(); }
  giveChips(seat, amt) {
    seat.pendGive = (seat.pendGive || 0) + amt;
    if (this.seatBusy(seat)) this.log(`방장이 ${seat.name}에게 칩 ${fmt(amt)} 지급 · 이번 판이 끝나면 들어가요`);
    else this.log(`방장이 ${seat.name}에게 칩 ${fmt(amt)} 지급`);
    this.applyGives();
    this.dirty = true;
  }
  applyGives() {
    for (const s of this.seats) {
      if (!s.pendGive || this.seatBusy(s)) continue;
      s.stack += s.pendGive; this.statBuy(s, s.pendGive); s.pendGive = 0;
      if (s.stack > 0 && this.game !== 'bj' && this.game !== 'bac') s.out = false;
      if ((this.game === 'bj' || this.game === 'bac') && s.stack >= this.settings.minBet) s.out = false;
      this.dirty = true;
    }
  }
  /* ---- 추방 ---- */
  kickSeat(seat) {
    seat.kicked = true; seat.online = false; seat.offSince = Date.now();
    this.log(`${seat.name}님이 추방됐어요`);
    this.onKick(seat);
    this.sweepKicked();
    this.dirty = true;
  }
  onKick(seat) { // 홀덤: 진행 중인 핸드면 바로 폴드 처리
    const hd = this.hand, i = this.seats.indexOf(seat);
    if (this.status !== 'playing' || !seat.inHand || seat.folded || !BETTING.has(hd.st)) return;
    if (hd.tu === i) { this.act(i, 'fold'); return; }
    seat.folded = true; seat.la = '폴드';
    const live = this.seats.filter(o => o.inHand && !o.folded);
    if (live.length === 1) this.winByFold(live[0]);
  }
  safeToRemove() { return this.status !== 'playing' || this.hand.st === 'show' || this.hand.st === 'idle'; }
  canDropOffline() { return this.status !== 'playing'; }
  removeSeatAt(i) { const hd = this.hand; this.seats.splice(i, 1); if (hd.d >= i && hd.d > 0) hd.d--; }
  sweepKicked() {
    if (!this.safeToRemove()) return;
    for (let i = this.seats.length - 1; i >= 0; i--) if (this.seats[i].kicked) { this.removeSeatAt(i); this.dirty = true; }
  }
  commonTick(now) {
    const host = this.seatOf(this.hostPid);
    if (!host || host.kicked || (!host.online && now - host.offSince > 30000)) {
      const next = this.seats.find(s => s.online && !s.bot && !s.kicked && s.pid !== this.hostPid);
      if (next) { this.hostPid = next.pid; this.log(`${next.name}님이 새 방장이 됐어요`); this.dirty = true; }
    }
    this.sweepKicked();
    this.applyGives();
    if (this.canDropOffline() && this.safeToRemove()) {
      for (let i = this.seats.length - 1; i >= 0; i--) {
        const s = this.seats[i];
        if (!s.online && !s.bot && now - s.offSince >= 60000) { this.log(`${s.name} 퇴장`); this.removeSeatAt(i); this.dirty = true; }
      }
    }
  }
  blankHand(sq) { return { no: 0, d: -1, sq, tu: -1, st: 'idle', bd: [], pot: 0, cb: 0, mr: 0, holes: {}, deck: [], res: null, sbI: -1, bbI: -1 }; }
  newSeat(pid, name) {
    return { pid, id: crypto.randomBytes(4).toString('hex'), name, stack: this.settings.stack, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, out: false, online: true, offSince: 0, shown: null, best: null, la: '', won: 0, hn: '' };
  }
  resetSeatHand(s) { Object.assign(s, { popped: false, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, shown: null, best: null, la: '', won: 0, hn: '', hx: { pf: '', agg: {}, call: {}, v: 0, r: 0 } }); }
  // 행동 기록: 이번 판 손패 범위 추정(hx) + 사람 플레이어 습관(opp)
  noteAct(s, kind, toCall) {
    const hd = this.hand, st = hd.st, hx = s.hx || (s.hx = { pf: '', agg: {}, call: {}, v: 0, r: 0 });
    if (kind === 'r') hd.nr = (hd.nr || 0) + 1;
    if (st === 'pre') {
      if (kind === 'r') { hx.pf = hd.nr >= 2 ? '3' : 'r'; hd.pfAgg = s.id; }
      else if (kind === 'c' && !hx.pf) hx.pf = 'c';
    } else if (kind === 'r') hx.agg[st] = 1; else if (kind === 'c') hx.call[st] = 1;
    if (s.bot) return;
    const o = oppStats(this, s.pid);
    if (st === 'pre') {
      if ((kind === 'c' || kind === 'r') && !hx.v) { hx.v = 1; o.vpip++; }
      if (kind === 'r' && !hx.r) { hx.r = 1; o.pfr++; }
    } else {
      if (toCall > 0) { o.faced++; if (kind === 'f') o.folds++; }
      if (kind === 'r') o.bets++; else if (kind === 'c') o.calls++; else if (kind === 'x') o.checks++;
    }
  }
  seatOf(pid) { return this.seats.find(s => s.pid === pid); }
  addBot(lv) {
    if (this.seats.length >= 8) return '자리가 꽉 찼어요 (최대 8명)';
    if (!BOT_LEVELS[lv]) lv = 'normal';
    const used = new Set(this.seats.map(s => s.name));
    const pool = BOT_NAMES.filter(n => !used.has('AI ' + n));
    const name = 'AI ' + (pool.length ? pool[randInt(pool.length)] : BOT_NAMES[randInt(BOT_NAMES.length)]);
    const seat = this.newSeat('bot:' + crypto.randomBytes(6).toString('hex'), name);
    seat.bot = true; seat.lv = lv;
    this.seats.push(seat);
    if (this.status === 'playing') this.statAdd(seat);
    this.log(`${name}(${BOT_LEVELS[lv].label}) 참가${this.status === 'playing' ? ' · 다음 핸드부터' : ''}`);
    this.dirty = true;
    return '';
  }
  emitReact(seat, e) { const r = { e, sid: seat.id, n: seat.name, k: crypto.randomBytes(3).toString('hex') }; for (const c of this.socks) c.emit('react', r); }
  log(t) { this.pushChat({ sys: 1, t }); }
  pushChat(m) {
    m.id = ++this.chatI; m.at = Date.now();
    this.chat.push(m); if (this.chat.length > 60) this.chat.shift();
    for (const c of this.socks) c.emit('chat', m);
  }

  /* ---- 베팅 엔진 ---- */
  needsAct(s) { const hd = this.hand; return s.inHand && !s.folded && !s.allIn && (!s.acted || s.bet < hd.cb); }
  findNeed(start, inclusive) {
    const n = this.seats.length;
    const can = this.seats.filter(s => s.inHand && !s.folded && !s.allIn);
    if (can.length === 1 && can[0].bet >= this.hand.cb) return -1;
    for (let k = inclusive ? 0 : 1; k <= n; k++) { const j = ((start + k) % n + n) % n; if (this.needsAct(this.seats[j])) return j; }
    return -1;
  }
  nextIn(from) { const n = this.seats.length; for (let k = 1; k <= n; k++) { const j = ((from + k) % n + n) % n; if (this.seats[j].inHand) return j; } return -1; }
  pay(s, amt) { const p = Math.max(0, Math.min(amt, s.stack)); s.stack -= p; s.bet += p; s.contrib += p; if (s.stack === 0 && s.inHand && !s.folded) s.allIn = true; return p; }

  startHand() {
    const hd = this.hand;
    const elig = this.seats.map((s, i) => i).filter(i => this.seats[i].stack > 0 && this.seats[i].online);
    this.seats.forEach(s => this.resetSeatHand(s));
    const humanHere = this.seats.some(s => !s.bot && s.online);
    if (elig.length < 2 || !humanHere) {
      this.status = 'playing'; hd.st = 'idle'; hd.tu = -1; hd.bd = []; hd.pot = 0; hd.res = null;
      this.msg = !humanHere ? '접속한 사람이 없어서 쉬는 중이에요' : '칩이 있는 플레이어가 2명 이상 접속해야 다음 핸드를 시작해요';
      hd.sq++; this.nextAt = Date.now() + 3000; this.dirty = true; return;
    }
    this.msg = '';
    elig.forEach(i => { this.seats[i].inHand = true; this.seats[i].st0 = this.seats[i].stack; if (!this.seats[i].bot) oppStats(this, this.seats[i].pid).hands++; });
    hd.no++;
    hd.d = this.nextIn(hd.d ?? -1);
    let sbI, bbI;
    if (elig.length === 2) { sbI = hd.d; bbI = this.nextIn(hd.d); } else { sbI = this.nextIn(hd.d); bbI = this.nextIn(sbI); }
    this.pay(this.seats[sbI], this.settings.sb); this.seats[sbI].la = 'SB';
    this.pay(this.seats[bbI], this.settings.bb); this.seats[bbI].la = 'BB';
    Object.assign(hd, { sbI, bbI, cb: this.settings.bb, mr: this.settings.bb, pot: 0, bd: [], st: 'pre', res: null, deck: newDeck(), holes: {}, nr: 0, pfAgg: '' });
    const dealHoles = deck => { const holes = {}; for (let r = 0; r < 2; r++) { let j = hd.d; for (let c = 0; c < elig.length; c++) { j = this.nextIn(j); const pid = this.seats[j].pid; (holes[pid] || (holes[pid] = [])).push(deck.pop()); } } return holes; };
    hd.holes = dealHoles(hd.deck);
    // 행운 모드: 리버까지 가면 이 플레이어가 반드시 혼자 이기도록 덱을 골라요
    const lucky = this.seats.find(s => s.lucky && s.inHand);
    if (lucky && rnd() < LUCKY_RATE) {
      const ints = cs => cs.map(c => CARD_INT[c]);
      const boardOf = deck => { const d = deck.slice(); d.pop(); const bd = [d.pop(), d.pop(), d.pop()]; d.pop(); bd.push(d.pop()); d.pop(); bd.push(d.pop()); return bd; };
      let picked = null, backup = null;
      for (let t = 0; t < 4000 && !picked; t++) {
        const deck = newDeck(), holes = dealHoles(deck), bd = boardOf(deck);
        const mine = eval7i(ints([...holes[lucky.pid], ...bd]));
        let ok = true;
        for (const pid of Object.keys(holes)) if (pid !== lucky.pid && eval7i(ints([...holes[pid], ...bd])) >= mine) { ok = false; break; }
        if (!ok) continue;
        if (mine >= B13[5]) picked = { deck, holes }; // 원페어 이상이면 바로 채택
        else if (!backup) backup = { deck, holes };   // 하이카드라도 혼자 이기면 예비로
      }
      if (!picked) picked = backup;
      if (!picked) { // 아주 드문 경우: 가장 센 손패를 행운 플레이어에게 바꿔 줌
        const deck = hd.deck, holes = hd.holes, bd = boardOf(deck);
        let bestPid = lucky.pid, best = -1;
        for (const pid of Object.keys(holes)) { const v = eval7i(ints([...holes[pid], ...bd])); if (v > best) { best = v; bestPid = pid; } }
        const tmp = holes[lucky.pid]; holes[lucky.pid] = holes[bestPid]; holes[bestPid] = tmp;
        picked = { deck, holes };
      }
      hd.deck = picked.deck; hd.holes = picked.holes;
    } else if (lucky) {
      // 나머지 8%: 끝까지 가면 다른 누군가가 이기는 판
      const ints = cs => cs.map(c => CARD_INT[c]);
      const boardOf = deck => { const d = deck.slice(); d.pop(); const bd = [d.pop(), d.pop(), d.pop()]; d.pop(); bd.push(d.pop()); d.pop(); bd.push(d.pop()); return bd; };
      for (let t = 0; t < 400; t++) {
        const deck = newDeck(), holes = dealHoles(deck), bd = boardOf(deck);
        const mine = eval7i(ints([...holes[lucky.pid], ...bd]));
        if (Object.keys(holes).some(pid => pid !== lucky.pid && eval7i(ints([...holes[pid], ...bd])) > mine)) { hd.deck = deck; hd.holes = holes; break; }
      }
    }
    this.status = 'playing';
    const first = elig.length === 2 ? sbI : this.nextIn(bbI);
    hd.tu = this.findNeed(first, true); hd.sq++; this.turnStart = Date.now();
    this.log(`#${hd.no} 핸드 시작 · 딜러 ${this.seats[hd.d].name}`);
    if (hd.tu < 0) this.runoutAt = Date.now() + 900;
    this.dirty = true;
  }
  act(i, a, amt) {
    const hd = this.hand, s = this.seats[i];
    if (!s || hd.tu !== i || !BETTING.has(hd.st)) return false;
    const toCall = hd.cb - s.bet, cb0 = hd.cb;
    if (a === 'fold') { s.folded = true; s.la = '폴드'; }
    else if (a === 'check') { if (toCall > 0) return false; s.la = '체크'; }
    else if (a === 'call') { if (toCall <= 0) s.la = '체크'; else { this.pay(s, toCall); s.la = s.stack === 0 ? '올인' : '콜'; } }
    else if (a === 'raise' || a === 'allin') {
      const maxT = s.bet + s.stack;
      let target = a === 'allin' ? maxT : Math.floor(Number(amt) || 0);
      if (target > maxT) target = maxT;
      if (target <= hd.cb || s.acted) { if (a === 'allin') return this.act(i, 'call'); return false; }
      const others = this.seats.filter((o, k) => k !== i && o.inHand && !o.folded && !o.allIn).length;
      if (!others) return this.act(i, 'call');
      const minT = hd.cb + hd.mr;
      if (target < minT && target < maxT) target = Math.min(minT, maxT);
      const raiseBy = target - hd.cb, wasZero = hd.cb === 0;
      this.pay(s, target - s.bet);
      if (raiseBy >= hd.mr) { hd.mr = raiseBy; this.seats.forEach((o, k) => { if (k !== i && o.inHand && !o.folded && !o.allIn) o.acted = false; }); }
      hd.cb = target;
      s.la = s.stack === 0 ? '올인' : (wasZero ? '벳 ' : '레이즈 ') + fmt(target);
    } else return false;
    s.acted = true;
    try { this.noteAct(s, a === 'fold' ? 'f' : hd.cb > cb0 ? 'r' : toCall > 0 ? 'c' : 'x', toCall); } catch (e) {}
    const live = this.seats.filter(o => o.inHand && !o.folded);
    if (live.length === 1) { this.winByFold(live[0]); return true; }
    const nt = this.findNeed(i, false);
    if (nt < 0) this.endStreet(); else { hd.tu = nt; hd.sq++; this.turnStart = Date.now(); this.dirty = true; }
    return true;
  }
  endStreet() {
    const hd = this.hand;
    this.seats.forEach(o => { hd.pot += o.bet; o.bet = 0; o.acted = false; if (o.inHand && !o.folded && o.la !== '올인') o.la = ''; });
    hd.cb = 0; hd.mr = this.settings.bb; hd.nr = 0;
    if (hd.st === 'river') { this.showdown(); return; }
    const can = this.seats.filter(o => o.inHand && !o.folded && !o.allIn);
    const runout = can.length <= 1;
    if (runout) this.seats.forEach(o => { if (o.inHand && !o.folded) o.shown = hd.holes[o.pid]; });
    hd.deck.pop(); // 번
    if (hd.st === 'pre') { hd.bd = [hd.deck.pop(), hd.deck.pop(), hd.deck.pop()]; hd.st = 'flop'; }
    else if (hd.st === 'flop') { hd.bd = [...hd.bd, hd.deck.pop()]; hd.st = 'turn'; }
    else if (hd.st === 'turn') { hd.bd = [...hd.bd, hd.deck.pop()]; hd.st = 'river'; }
    if (runout) { hd.tu = -1; this.runoutAt = Date.now() + 1500; }
    else { hd.tu = this.findNeed(hd.d, false); this.turnStart = Date.now(); if (hd.tu < 0) this.runoutAt = Date.now() + 1500; }
    hd.sq++; this.dirty = true;
  }
  orderFromDealer(s) { const n = this.seats.length; return ((this.seats.indexOf(s) - this.hand.d + n) % n) || n; }

  // 쇼다운: 팟을 베팅 금액 층마다 나누고(메인/사이드), 층마다 가장 좋은 패가 가져감.
  // 점수가 완전히 같으면 무승부 → 똑같이 나누고, 나눠지지 않는 1칩은 딜러 왼쪽부터.
  showdown() {
    const hd = this.hand;
    const all = this.seats.filter(o => o.inHand), cont = all.filter(o => !o.folded);
    const score = new Map();
    cont.forEach(o => {
      o.shown = hd.holes[o.pid];
      const b = bestHand([...hd.holes[o.pid], ...hd.bd]);
      score.set(o, b.score); o.best = b.cards; o.hn = handName(b.score);
    });
    const levels = [...new Set(all.map(o => o.contrib).filter(x => x > 0))].sort((a, b) => a - b);
    let prev = 0;
    const pots = []; // {amt, el:[seat], ret:bool}
    for (const L of levels) {
      let amt = 0; all.forEach(o => { amt += Math.min(o.contrib, L) - Math.min(o.contrib, prev); });
      prev = L;
      if (!amt) continue;
      const payers = all.filter(o => o.contrib >= L);
      let el = cont.filter(o => o.contrib >= L);
      if (payers.length === 1 && el.length === 1) { pots.push({ amt, el, ret: true }); continue; } // 아무도 받지 않은 베팅 → 돌려줌
      if (!el.length) el = cont;
      const last = pots[pots.length - 1];
      if (last && !last.ret && last.el.length === el.length && last.el.every(x => el.includes(x))) last.amt += amt;
      else pots.push({ amt, el, ret: false });
    }
    const won = new Map();
    const result = { kind: 'show', pots: [], hi: [], line: '' };
    let sideNo = 0;
    for (const p of pots) {
      if (p.ret) { const o = p.el[0]; o.stack += p.amt; continue; }
      let best = null; p.el.forEach(o => { const sc = score.get(o); if (!best || cmpScore(sc, best) > 0) best = sc; });
      const w = p.el.filter(o => cmpScore(score.get(o), best) === 0).sort((a, b) => this.orderFromDealer(a) - this.orderFromDealer(b));
      const losers = p.el.filter(o => !w.includes(o));
      let runner = null; losers.forEach(o => { const sc = score.get(o); if (!runner || cmpScore(sc, runner) > 0) runner = sc; });
      const share = Math.floor(p.amt / w.length); let rem = p.amt - share * w.length;
      const shares = w.map(o => { const x = share + (rem > 0 ? 1 : 0); if (rem > 0) rem--; won.set(o, (won.get(o) || 0) + x); return x; });
      result.pots.push({
        name: sideNo === 0 ? '메인 팟' : `사이드 팟 ${sideNo}`,
        amt: p.amt,
        win: w.map(o => o.id), names: w.map(o => o.name), shares,
        split: w.length > 1,
        hn: handName(best),
        note: w.length > 1 ? `최종 5장이 똑같아서 무승부 (${fiveLabel(w[0].best || [])})` : kickerNote(best, runner),
        solo: p.el.length === 1
      });
      sideNo++;
    }
    won.forEach((x, o) => { o.stack += x; o.won = x; });
    // 메인 팟 승자의 베스트 5장을 하이라이트
    const main = result.pots[0];
    if (main) {
      const hi = new Set();
      main.win.forEach(id => { const o = this.seats.find(s => s.id === id); (o.best || []).forEach(c => hi.add(c)); });
      result.hi = [...hi];
    }
    result.line = this.resultLine(result);
    hd.res = result;
    this.log(`#${hd.no} 쇼다운 · ${result.line}`);
    hd.st = 'show'; hd.tu = -1; hd.sq++; this.endHand();
  }
  resultLine(r) {
    return r.pots.filter(p => !p.solo || r.pots.length === 1).map(p => {
      const head = r.pots.length > 1 ? `${p.name} ` : '';
      if (p.split) return `${head}무승부 · ${p.names.join(', ')} ${p.hn}로 ${fmt(p.amt)} 나눔${p.note ? ' · ' + p.note : ''}`;
      return `${head}${p.names[0]} +${fmt(p.amt)} · ${p.hn}${p.note ? ' (' + p.note + ')' : ''}`;
    }).join(' / ');
  }
  winByFold(w) {
    const hd = this.hand;
    let total = hd.pot; this.seats.forEach(o => { total += o.bet; o.bet = 0; });
    hd.pot = total; w.stack += total; w.won = total;
    hd.res = { kind: 'fold', pots: [{ name: '메인 팟', amt: total, win: [w.id], names: [w.name], shares: [total], split: false, hn: '', note: '' }], hi: [], line: `${w.name} +${fmt(total)} · 모두 폴드` };
    this.log(`#${hd.no} ${hd.res.line}`);
    hd.st = 'show'; hd.tu = -1; hd.sq++; this.endHand();
  }
  endHand() {
    this.botReactions();
    this.seats.forEach(o => { if (o.inHand) this.statHand(o, o.stack - (o.st0 ?? o.stack)); });
    this.seats.forEach(o => { if (o.stack <= 0) o.out = true; });
    const alive = this.seats.filter(o => o.stack > 0);
    if (alive.length < 2) { this.status = 'over'; this.champ = alive[0] ? alive[0].name : ''; this.log(`게임 종료 · ${this.champ} 우승`); this.rankLog(); this.nextAt = 0; }
    else this.nextAt = Date.now() + (this.hand.res && this.hand.res.kind === 'show' ? 9000 : 6500);
    this.dirty = true;
  }

  // 핸드가 끝난 뒤 자기 패를 모두에게 보여주기 (모두 폴드로 이긴 사람, 블러핑 자랑 등)
  reveal(seat) {
    const hd = this.hand;
    if (!seat || !seat.inHand || seat.popped) return false; // 한 핸드에 한 번
    if (!(hd.st === 'show' || (BETTING.has(hd.st) && seat.folded))) return false; // 핸드가 끝났거나, 내가 이미 폴드했을 때만
    const hole = hd.holes[seat.pid]; if (!hole) return false;
    seat.popped = true;
    seat.shown = hole;
    if (hd.bd.length >= 3) { const b = bestHand([...hole, ...hd.bd]); seat.hn = handName(b.score); seat.best = b.cards; }
    this.log(`${seat.name} 패 공개 · ${hole.map(c => (c[0] === 'T' ? '10' : c[0]) + { s: '♠', h: '♥', d: '♦', c: '♣' }[c[1]]).join(' ')}${seat.hn ? ' (' + seat.hn + ')' : ''}`);
    const ev = { sid: seat.id, n: seat.name, cards: hole, hn: seat.hn || '', folded: !!seat.folded, k: crypto.randomBytes(3).toString('hex') };
    for (const c of this.socks) c.emit('shown', ev);
    this.dirty = true;
    return true;
  }
  botReactions() {
    const r = this.hand.res; if (!r) return;
    const bigPot = this.settings.bb * 15;
    const total = r.pots.reduce((a, p) => a + p.amt, 0);
    const winners = new Set(r.pots.flatMap(p => p.win));
    const bots = this.seats.filter(s => s.bot && s.inHand);
    if (r.kind === 'fold') bots.forEach(b => { if (winners.has(b.id) && rnd() < 0.35) setTimeout(() => { this.reveal(b); this.tick(Date.now()); }, 1500 + randInt(1200)); });
    const pick = arr => arr[randInt(arr.length)];
    bots.forEach((b, k) => {
      let e = null;
      if (winners.has(b.id) && r.pots[0] && r.pots[0].split) { if (rnd() < 0.4) e = pick(['🙏', '👍', '😂']); }
      else if (winners.has(b.id) && total >= bigPot) { if (rnd() < 0.55) e = pick(['😎', '🔥', '💸', '😂']); }
      else if (!winners.has(b.id) && !b.folded && b.contrib >= bigPot / 2) { if (rnd() < 0.45) e = pick(['😭', '🤬', '😱', '🤔']); }
      if (e && EMOJIS.includes(e)) setTimeout(() => this.emitReact(b, e), 700 + k * 500 + randInt(600));
    });
  }

  /* ---- 방장 명령 ---- */
  hostCmd(cmd, arg) {
    if (cmd === 'set' && this.status === 'lobby' && arg && typeof arg === 'object') {
      const ok = { stack: [500, 1000, 2000, 5000, 10000], sb: [5, 10, 25, 50, 100], bb: [10, 20, 50, 100, 200], timer: [20, 30, 60, 0] };
      for (const k of Object.keys(ok)) if (arg[k] !== undefined && ok[k].includes(+arg[k])) this.settings[k] = +arg[k];
      this.seats.forEach(s => { s.stack = this.settings.stack; });
      this.dirty = true;
    } else if (cmd === 'addbot') {
      return this.addBot(String(arg && arg.lv || 'normal'));
    } else if (cmd === 'kickbot') {
      const b = this.seats.find(s => s.bot && s.id === String(arg && arg.id));
      if (!b) return '';
      if (this.status === 'playing' && b.inHand && this.hand.st !== 'show' && this.hand.st !== 'idle') return '핸드가 끝난 뒤에 뺄 수 있어요';
      const i = this.seats.indexOf(b), hd = this.hand;
      this.seats.splice(i, 1);
      if (hd.d >= i && hd.d > 0) hd.d--;
      this.log(`${b.name} 퇴장`); this.dirty = true;
    } else if (cmd === 'start' && this.status === 'lobby') {
      if (this.seats.filter(s => s.online).length < 2) return '2명 이상 있어야 시작할 수 있어요. 혼자라면 AI를 추가해 보세요';
      this.seats.forEach(s => Object.assign(s, { stack: this.settings.stack, out: false }));
      this.hand = this.blankHand(this.hand.sq + 1); this.champ = '';
      this.statInit();
      this.log(`게임 시작 · 시작 칩 ${fmt(this.settings.stack)}, 블라인드 ${this.settings.sb}/${this.settings.bb}`);
      this.startHand();
    } else if (cmd === 'next' && this.status === 'playing' && (this.hand.st === 'show' || this.hand.st === 'idle')) {
      this.nextAt = 0; this.startHand();
    } else if (cmd === 'rebuy') {
      let k = 0; this.seats.forEach(s => { if (s.out && !s.inHand) { this.statBuy(s, this.settings.stack - s.stack); s.stack = this.settings.stack; s.out = false; k++; } });
      if (k) { this.log(`탈락자 ${k}명 리바이 (${fmt(this.settings.stack)})`); this.dirty = true; }
    } else if (cmd === 'lobby') {
      if (this.status !== 'over') this.rankLog();
      this.status = 'lobby'; this.nextAt = 0; this.runoutAt = 0;
      this.hand = this.blankHand(this.hand.sq + 1); this.champ = ''; this.msg = '';
      this.seats = this.seats.filter(s => s.online && !s.kicked);
      this.seats.forEach(s => { this.resetSeatHand(s); s.stack = this.settings.stack; s.out = false; });
      this.log('대기실로 돌아왔어요'); this.dirty = true;
    }
    return '';
  }

  /* ---- 주기 처리 ---- */
  tick(now) {
    this.commonTick(now);
    if (this.status === 'playing') {
      const hd = this.hand;
      if (this.runoutAt && now >= this.runoutAt) { this.runoutAt = 0; this.endStreet(); }
      else if (this.nextAt && now >= this.nextAt) { this.nextAt = 0; this.startHand(); }
      else if (hd.tu >= 0 && BETTING.has(hd.st) && this.seats[hd.tu].bot) {
        const s = this.seats[hd.tu], L = BOT_LEVELS[s.lv] || BOT_LEVELS.normal;
        if (this.botFor !== hd.sq) { this.botFor = hd.sq; this.botAt = now + L.slow[0] + randInt(L.slow[1] - L.slow[0]); }
        else if (now >= this.botAt) {
          let d; try { d = botDecide(this, hd.tu); } catch (e) { console.error('bot error', e); d = [hd.cb > s.bet ? 'fold' : 'check']; }
          if (!this.act(hd.tu, d[0], d[1])) this.act(hd.tu, hd.cb > s.bet ? 'call' : 'check');
        }
      }
      else if (hd.tu >= 0 && BETTING.has(hd.st)) {
        const s = this.seats[hd.tu];
        if (now - this.turnStart > this.turnLimit(s)) { this.log(`${s.name} 시간 초과`); this.act(hd.tu, hd.cb > s.bet ? (s.lucky ? 'call' : 'fold') : 'check'); }
      }
    }
    if (this.dirty) { this.dirty = false; this.broadcast(); }
  }
  turnLimit(s) { return s.bot ? 0 : !s.online ? 8000 : (this.settings.timer ? this.settings.timer * 1000 : Infinity); }

  /* ---- 화면에 보낼 상태 ---- */
  publicState() {
    const hd = this.hand, now = Date.now();
    const turnSeat = hd.tu >= 0 ? this.seats[hd.tu] : null;
    const lim = turnSeat ? this.turnLimit(turnSeat) : Infinity;
    return {
      game: 'holdem', code: this.code, status: this.status, set: this.settings, msg: this.msg, champ: this.champ, rk: this.ranking(),
      seats: this.seats.map(s => ({ id: s.id, n: s.name, s: s.stack, b: s.bet, f: s.folded ? 1 : 0, a: s.allIn ? 1 : 0, ac: s.acted ? 1 : 0, ih: s.inHand ? 1 : 0, o: s.out ? 1 : 0, aw: s.online ? 0 : 1, sh: s.shown || 0, bc: s.best || 0, la: s.la, w: s.won, hn: s.hn, host: s.pid === this.hostPid ? 1 : 0, bot: s.bot ? 1 : 0, pp: s.popped ? 1 : 0, pg: s.pendGive || 0, lv: s.bot ? BOT_LEVELS[s.lv].label : '' })),
      h: {
        no: hd.no, d: hd.d, sb: hd.sbI, bb: hd.bbI, st: hd.st, bd: hd.bd, pot: hd.pot, cb: hd.cb, mr: hd.mr, tu: hd.tu, sq: hd.sq, res: hd.res,
        tl: turnSeat && !turnSeat.bot && BETTING.has(hd.st) && isFinite(lim) ? Math.max(0, lim - (now - this.turnStart)) : -1,
        tt: isFinite(lim) ? lim : 0,
        nx: this.nextAt ? Math.max(0, this.nextAt - now) : -1
      }
    };
  }
  sendTo(c, pub) {
    const pid = c.pid;
    const me = this.seats.findIndex(s => s.pid === pid);
    const seat = this.seats[me];
    const hole = seat && seat.inHand ? (this.hand.holes[pid] || null) : null;
    c.emit('state', { ...pub, me, hole, isHost: pid === this.hostPid, lk: seat && seat.lucky ? 1 : 0 });
  }
  broadcast() { const pub = this.publicState(); for (const c of this.socks) this.sendTo(c, pub); }
}

/* ================= 블랙잭 ================= */
// 규칙 (일반적인 카지노 기준)
// · 6덱 슈, 75% 정도 쓰면 새로 섞음 · 딜러는 소프트 17에서 스탠드(S17) · 블랙잭 3:2
// · 딜러가 A를 보이면 인슈어런스(베팅의 절반, 2:1) / 블랙잭이면 이븐 머니(1:1 확정)
// · 딜러가 A나 10을 보이면 블랙잭인지 먼저 확인(피크) → 딜러 블랙잭이면 바로 정산
// · 더블: 처음 2장일 때, 스플릿 후에도 가능 · 스플릿: 최대 4손, A는 한 번만 + 한 장씩만
// · 레이트 서렌더: 처음 2장일 때 베팅 절반을 돌려받고 포기 (스플릿 후 불가)
const BJ_DECKS = 6;
const cardVal = c => c[0] === 'A' ? 11 : 'TJQK'.includes(c[0]) ? 10 : +c[0];
function bjTotal(cards) {
  let t = 0, aces = 0;
  for (const c of cards) { t += cardVal(c); if (c[0] === 'A') aces++; }
  while (t > 21 && aces) { t -= 10; aces--; }
  return { t, soft: aces > 0 };
}
const isBJ = (cards, fromSplit) => !fromSplit && cards.length === 2 && bjTotal(cards).t === 21;
function newShoe(decks = BJ_DECKS) {
  const d = [];
  for (let k = 0; k < decks; k++) for (const r of RANKS) for (const su of SUITS) d.push(r + su);
  for (let i = d.length - 1; i > 0; i--) { const j = randInt(i + 1); [d[i], d[j]] = [d[j], d[i]]; }
  return d;
}
// 기본 전략 (6덱, S17, 더블 애프터 스플릿, 레이트 서렌더)
function basicStrategy(cards, up, canDouble, canSplit, canSurrender) {
  const u = cardVal(up);
  const { t, soft } = bjTotal(cards);
  if (canSurrender && cards.length === 2 && !soft) {
    const p88 = cards[0][0] === '8' && cards[1][0] === '8';
    if (!p88 && ((t === 16 && u >= 9) || (t === 15 && u === 10))) return 'surrender';
  }
  if (canSplit && cards.length === 2 && cardVal(cards[0]) === cardVal(cards[1])) {
    const p = cardVal(cards[0]);
    if (p === 11 || p === 8) return 'split';
    if (p === 9 && u !== 7 && u <= 9) return 'split';
    if ((p === 2 || p === 3 || p === 7) && u <= 7) return 'split';
    if (p === 6 && u <= 6) return 'split';
    if (p === 4 && (u === 5 || u === 6)) return 'split';
  }
  if (soft && t < 21) {
    if (t >= 19) return 'stand';
    if (t === 18) { if (u >= 3 && u <= 6) return canDouble ? 'double' : 'stand'; return u <= 8 ? 'stand' : 'hit'; }
    if (t === 17) return (u >= 3 && u <= 6 && canDouble) ? 'double' : 'hit';
    if (t >= 15) return (u >= 4 && u <= 6 && canDouble) ? 'double' : 'hit';
    return (u >= 5 && u <= 6 && canDouble) ? 'double' : 'hit';
  }
  if (t >= 17) return 'stand';
  if (t >= 13) return u <= 6 ? 'stand' : 'hit';
  if (t === 12) return (u >= 4 && u <= 6) ? 'stand' : 'hit';
  if (t === 11) return (u <= 10 && canDouble) ? 'double' : 'hit';
  if (t === 10) return (u <= 9 && canDouble) ? 'double' : 'hit';
  if (t === 9) return (u >= 3 && u <= 6 && canDouble) ? 'double' : 'hit';
  return 'hit';
}
function bjBotMove(room, s, hand) {
  const L = s.lv || 'normal';
  const up = room.r.dl[0];
  const canDouble = room.canDouble(s, hand), canSplit = room.canSplit(s, hand), canSur = room.canSurrender(s, hand);
  const { t } = bjTotal(hand.cards);
  if (L === 'easy') {
    if (canSplit && cardVal(hand.cards[0]) === 11 && rnd() < 0.6) return 'split';
    if (canDouble && t === 11 && rnd() < 0.4) return 'double';
    return t < 15 || (t < 17 && rnd() < 0.4) ? 'hit' : 'stand';
  }
  if (L === 'normal' && rnd() < 0.12) return t < 13 ? 'hit' : (rnd() < 0.5 ? 'hit' : 'stand');
  return basicStrategy(hand.cards, up, canDouble, canSplit, L === 'hard' && canSur);
}
function bjBotBet(room, s) {
  const mb = room.settings.minBet, L = s.lv || 'normal';
  let units = L === 'easy' ? 1 + randInt(4) : L === 'hard' ? 2 + randInt(2) : 1 + randInt(3);
  if (rnd() < 0.08) units *= 3;
  return Math.max(mb, Math.min(s.stack, units * mb));
}
// 행운 모드 블랙잭 승률 맞추기: 이 비율만큼은 '이기는 판', 나머지는 '지는 쪽으로 기우는 판'
// (지는 쪽 판에서도 블랙잭·21이 나오면 이길 수 있어서 실제 승률은 이보다 조금 높게 나옴 → 시뮬레이션으로 92%에 맞춤)
const BJ_LUCKY_WIN = 0.905;
const newHand = bet => ({ cards: [], bet, done: false, dbl: false, split: false, aceSplit: false, nat: false, sur: false, even: false, res: '', pay: 0 });

class BJRoom extends Room {
  constructor(code) {
    super(code);
    this.game = 'bj';
    this.settings = { stack: 1000, minBet: 20, timer: 30 };
    // 규칙 스위치 (챌린지 보스 단계마다 바뀜): h17 = 딜러 소프트 17 히트, bjPay = 블랙잭 배당, sur = 서렌더, das = 스플릿 후 더블
    this.rules = { h17: false, bjPay: 1.5, sur: true, das: true };
    this.shoe = newShoe(BJ_DECKS);
    this.r = this.blankRound(0);
    this.dealerAt = 0; this.betEnd = 0; this.insEnd = 0;
  }
  blankRound(sq) { return { no: 0, sq, st: 'idle', tu: -1, hi: 0, dl: [], hide: true, line: '', dealerBJ: false, lucky: null, unlucky: null }; }
  newSeat(pid, name) { const s = super.newSeat(pid, name); s.bj = { want: 0, ok: false, sit: false, inR: false, hands: [], net: 0, ins: 0, insd: false, insRes: '' }; return s; }
  resetBJ(s) { s.bj = { want: s.bj ? s.bj.want : 0, ok: false, sit: false, inR: false, hands: [], net: 0, ins: 0, insd: false, insRes: '' }; s.won = 0; }
  reveal() { return false; }
  live() { return this.r.st === 'ins' || this.r.st === 'play' || this.r.st === 'dealer'; }
  safeToRemove() { return this.status !== 'playing' || !this.live(); }
  canDropOffline() { return this.safeToRemove() && this.r.st !== 'bet'; }
  removeSeatAt(i) { this.seats.splice(i, 1); if (this.r.tu > i) this.r.tu--; }
  onKick(seat) {
    const r = this.r, i = this.seats.indexOf(seat);
    if (this.status !== 'playing' || !seat.bj.inR) return;
    seat.bj.insd = true;
    if (r.st === 'play') { seat.bj.hands.forEach(h => { h.done = true; }); if (r.tu === i) this.advance(); }
  }

  /* ---- 카드 뽑기: prefs(조건 목록)가 있으면 남은 카드 중 조건에 맞는 카드를 무작위 위치에서 가져옴 ---- */
  draw(prefs) {
    if (prefs && prefs.length) {
      const top = this.shoe.length - 1;
      for (const pred of prefs) {
        for (let k = top; k >= 0; k--) if (pred(this.shoe[k])) { const t = this.shoe[top]; this.shoe[top] = this.shoe[k]; this.shoe[k] = t; return this.shoe.pop(); }
      }
    }
    return this.shoe.pop();
  }
  isLucky(s) { return !!this.r.lucky && s.id === this.r.lucky; }
  hitPrefs(s, h) { return this.isLucky(s) ? [c => bjTotal([...h.cards, c]).t <= 21] : null; }
  liveTotals(s) { return s.bj.hands.filter(h => !h.sur && !h.even && !h.nat && bjTotal(h.cards).t <= 21).map(h => bjTotal(h.cards).t); }

  /* ---- 진행 ---- */
  startRound() {
    const r = this.r, now = Date.now();
    this.seats.forEach(s => this.resetBJ(s));
    const humanHere = this.seats.some(s => !s.bot && s.online);
    const mb = this.settings.minBet;
    this.seats.forEach(s => { s.out = s.stack < mb; });
    const elig = this.seats.filter(s => s.online && !s.out && !s.kicked);
    if (!humanHere || !elig.length) {
      r.st = 'idle'; r.sq++; this.msg = !humanHere ? '접속한 사람이 없어서 쉬는 중이에요' : '베팅할 칩이 있는 사람이 없어요. 방장이 리바이를 해 주세요';
      this.nextAt = now + 3000; this.dirty = true; return;
    }
    this.msg = '';
    if (this.shoe.length < 52 * BJ_DECKS * 0.25) { this.shoe = newShoe(BJ_DECKS); this.log('카드를 새로 섞었어요'); }
    Object.assign(r, { st: 'bet', tu: -1, hi: 0, dl: [], hide: true, line: '', dealerBJ: false, lucky: null, unlucky: null });
    r.no++; r.sq++;
    const ls = this.seats.find(s => s.lucky && elig.includes(s));
    if (ls) { if (rnd() < BJ_LUCKY_WIN) r.lucky = ls.id; else r.unlucky = ls.id; }
    elig.forEach(s => {
      s.bj.inR = true;
      s.bj.want = Math.max(mb, Math.min(s.stack, s.bj.want || mb));
      if (s.bot) s.bj.botAt = now + 700 + randInt(1600);
    });
    this.betEnd = this.settings.timer ? now + 15000 : 0;
    this.log(`#${r.no} 베팅 시작`);
    this.dirty = true;
  }
  bjMsg(pid, msg) {
    const r = this.r, i = this.seats.findIndex(s => s.pid === pid), s = this.seats[i];
    if (!s) return;
    const a = String(msg.a || '');
    if (r.st === 'bet' && s.bj.inR && !s.bj.ok) {
      const mb = this.settings.minBet;
      if (a === 'betok') {
        const x = Math.floor(+msg.x || 0);
        if (x < mb && s.stack >= mb) { tell(pid, 'err', `최소 베팅은 ${fmt(mb)}이에요`); return; }
        s.bj.want = Math.max(Math.min(mb, s.stack), Math.min(s.stack, x));
        s.bj.ok = true; s.bj.sit = false; this.dirty = true;
      } else if (a === 'sit') { s.bj.ok = true; s.bj.sit = true; this.log(`${s.name} 이번 판 쉬기`); this.dirty = true; }
      this.tick(Date.now()); return;
    }
    if (r.st === 'ins' && s.bj.inR && s.bj.hands.length && !s.bj.insd && a === 'ins') {
      this.insDecide(s, !!+msg.x); this.tick(Date.now()); return;
    }
    if (r.st === 'play' && r.tu === i && msg.sq === r.sq) {
      if (!this.act(i, a)) { tell(pid, 'err', '지금은 그 행동을 할 수 없어요'); return; }
      this.tick(Date.now());
    }
  }
  insDecide(s, take) {
    const h = s.bj.hands[0];
    if (take && h) {
      if (h.nat) { h.even = true; this.log(`${s.name} 이븐 머니`); }
      else { const amt = Math.floor(h.bet / 2); if (amt > 0 && s.stack >= amt) { s.stack -= amt; s.bj.ins = amt; this.log(`${s.name} 인슈어런스 ${fmt(amt)}`); } }
    }
    s.bj.insd = true; this.dirty = true;
  }
  deal() {
    const r = this.r, now = Date.now();
    const players = this.seats.filter(s => s.bj.inR && !s.bj.sit && s.online && !s.kicked && s.stack >= Math.min(this.settings.minBet, s.bj.want));
    this.seats.forEach(s => { if (s.bj.inR && !players.includes(s)) s.bj.inR = false; });
    if (!players.length) { r.st = 'show'; r.line = '모두 이번 판을 쉬었어요'; this.nextAt = now + 2500; r.sq++; this.dirty = true; return; }
    players.forEach(s => { const b = Math.max(1, Math.min(s.stack, s.bj.want)); s.stack -= b; s.bj.hands = [newHand(b)]; s.inHand = true; });
    const luckyIn = r.lucky && players.some(p => p.id === r.lucky);
    // 실제 카지노처럼 1장씩 두 바퀴: 플레이어들 → 딜러 (행운 판이면 딜러 두 번째 카드만 16 이하가 되도록)
    for (let round = 0; round < 2; round++) {
      for (const s of players) s.bj.hands[0].cards.push(this.draw(null));
      r.dl.push(this.draw(luckyIn && round === 1 ? [c => bjTotal([r.dl[0], c]).t <= 16] : null));
    }
    r.hide = true;
    players.forEach(s => { const h = s.bj.hands[0]; if (isBJ(h.cards)) { h.nat = true; h.done = true; } });
    if (r.dl[0][0] === 'A') {
      r.st = 'ins'; r.sq++; this.insEnd = now + 12000;
      players.forEach(s => { s.bj.insd = false; if (s.bot) s.bj.botAt = now + 800 + randInt(1500); });
      this.log('딜러가 A를 보여요 · 인슈어런스 받는 중');
      this.dirty = true; return;
    }
    this.afterInsurance();
  }
  afterInsurance() {
    const r = this.r, upV = cardVal(r.dl[0]);
    if ((upV === 10 || upV === 11) && isBJ(r.dl)) {
      r.dealerBJ = true; r.st = 'dealer'; r.hide = false; r.tu = -1; r.sq++;
      this.dealerAt = Date.now() + 1300; this.dirty = true; return;
    }
    if (upV === 11) this.log('딜러 블랙잭 아님 · 게임 계속');
    r.st = 'play'; r.tu = -1; r.hi = 0;
    this.advance();
  }
  advance() {
    const r = this.r, n = this.seats.length;
    const start = r.tu < 0 ? 0 : r.tu;
    for (let i = start; i < n; i++) {
      const s = this.seats[i]; if (!s.bj.inR || !s.bj.hands.length) continue;
      const hs = s.bj.hands;
      for (let k = i === r.tu ? r.hi : 0; k < hs.length; k++) {
        if (!hs[k].done) { r.tu = i; r.hi = k; r.sq++; this.turnStart = Date.now(); this.dirty = true; return; }
      }
    }
    r.tu = -1; r.hi = 0; r.st = 'dealer'; r.hide = false; r.sq++;
    this.dealerAt = Date.now() + 900; this.dirty = true;
  }
  canSplit(s, h) { return s.bj.hands.length < 4 && h.cards.length === 2 && !h.aceSplit && cardVal(h.cards[0]) === cardVal(h.cards[1]) && s.stack >= h.bet && !(h.cards[0][0] === 'A' && s.bj.hands.length > 1); }
  canDouble(s, h) { return h.cards.length === 2 && !h.aceSplit && s.stack >= h.bet && (this.rules.das || !h.split); }
  canSurrender(s, h) { return this.rules.sur && s.bj.hands.length === 1 && !h.split && h.cards.length === 2 && !h.dbl; }
  act(i, a) {
    const r = this.r, s = this.seats[i]; if (!s || r.st !== 'play' || r.tu !== i) return false;
    const h = s.bj.hands[r.hi]; if (!h || h.done) return false;
    if (a === 'hit') {
      h.cards.push(this.draw(this.hitPrefs(s, h)));
      if (bjTotal(h.cards).t >= 21) h.done = true;
    } else if (a === 'stand') {
      h.done = true;
    } else if (a === 'double') {
      if (!this.canDouble(s, h)) return false;
      s.stack -= h.bet; h.bet *= 2; h.dbl = true;
      h.cards.push(this.draw(this.hitPrefs(s, h))); h.done = true;
    } else if (a === 'split') {
      if (!this.canSplit(s, h)) return false;
      s.stack -= h.bet;
      const aces = h.cards[0][0] === 'A';
      const h2 = newHand(h.bet); h2.cards = [h.cards.pop()];
      h.split = h2.split = true;
      if (aces) h.aceSplit = h2.aceSplit = true;
      h.cards.push(this.draw(this.hitPrefs(s, h)));
      h2.cards.push(this.draw(this.hitPrefs(s, h2)));
      s.bj.hands.splice(r.hi + 1, 0, h2);
      if (aces) { h.done = true; h2.done = true; }
      for (const x of [h, h2]) if (bjTotal(x.cards).t >= 21) x.done = true;
    } else if (a === 'surrender') {
      if (!this.canSurrender(s, h)) return false;
      h.sur = true; h.done = true;
    } else return false;
    this.advance();
    return true;
  }
  dealerStep() {
    const r = this.r;
    const anyLive = this.seats.some(s => s.bj.inR && this.liveTotals(s).length);
    const dt = bjTotal(r.dl);
    if (r.dealerBJ || !anyLive || dt.t > 17 || (dt.t === 17 && !(this.rules.h17 && dt.soft))) { this.settle(); return; }
    const fin = c => bjTotal([...r.dl, c]).t;
    let prefs = null;
    if (r.lucky) {
      const ls = this.seats.find(s => s.id === r.lucky);
      const lt = ls ? this.liveTotals(ls) : [];
      if (lt.length) {
        const lb = Math.min(...lt);
        let ob = 0; for (const o of this.seats) if (o !== ls && o.bj.inR) for (const t of this.liveTotals(o)) if (t > ob) ob = t;
        prefs = lb > 17
          ? [c => { const t = fin(c); return t >= 17 && t < lb && t >= ob; }, c => { const t = fin(c); return t >= 17 && t < lb; }, c => fin(c) < 17, c => fin(c) > 21]
          : [c => fin(c) > 21, c => fin(c) < 17];
      }
    } else if (r.unlucky) {
      const us = this.seats.find(s => s.id === r.unlucky);
      const ut = us ? this.liveTotals(us) : [];
      if (ut.length) { const ub = Math.max(...ut); prefs = [c => { const t = fin(c); return t >= 17 && t <= 21 && t > ub; }, c => fin(c) < 17]; }
    }
    r.dl.push(this.draw(prefs));
    this.dirty = true;
    this.dealerAt = Date.now() + 850;
  }
  settle() {
    const r = this.r, now = Date.now();
    const d = bjTotal(r.dl), dBJ = isBJ(r.dl), dBust = d.t > 21;
    const parts = [];
    for (const s of this.seats) {
      if (!s.bj.inR || !s.bj.hands.length) continue;
      let net = 0;
      if (s.bj.ins) { const back = dBJ ? s.bj.ins * 3 : 0; s.stack += back; net += back - s.bj.ins; s.bj.insRes = dBJ ? 'win' : 'lose'; }
      for (const h of s.bj.hands) {
        const t = bjTotal(h.cards).t;
        let back = 0;
        if (h.even) { h.res = 'even'; back = h.bet * 2; }
        else if (h.sur) { h.res = 'sur'; back = Math.floor(h.bet / 2); }
        else if (t > 21) { h.res = 'bust'; }
        else if (h.nat && dBJ) { h.res = 'push'; back = h.bet; }
        else if (h.nat) { h.res = 'bj'; back = h.bet + Math.floor(h.bet * this.rules.bjPay); }
        else if (dBJ) { h.res = 'lose'; }
        else if (dBust || t > d.t) { h.res = 'win'; back = h.bet * 2; }
        else if (t === d.t) { h.res = 'push'; back = h.bet; }
        else { h.res = 'lose'; }
        h.pay = back - h.bet; s.stack += back; net += h.pay;
      }
      s.bj.net = net; s.won = net;
      this.statHand(s, net);
      parts.push(`${s.name} ${net > 0 ? '+' : ''}${fmt(net)}`);
    }
    r.line = dBJ ? '딜러 블랙잭!' : dBust ? `딜러 버스트! (${d.t})` : `딜러 ${d.t}`;
    this.log(`#${r.no} ${r.line} · ${parts.join(', ')}`);
    r.st = 'show'; r.tu = -1; r.sq++;
    this.seats.forEach(s => { s.out = s.stack < this.settings.minBet; });
    this.nextAt = now + 6500;
    this.bjBotReactions(dBust);
    this.dirty = true;
  }
  bjBotReactions(dBust) {
    const pick = arr => arr[randInt(arr.length)];
    const mb = this.settings.minBet;
    this.seats.filter(s => s.bot && s.bj.inR && s.bj.hands.length).forEach((b, k) => {
      let e = null;
      if (b.bj.hands.some(h => h.res === 'bj')) { if (rnd() < 0.6) e = pick(['😎', '🔥', '💸']); }
      else if (b.bj.net >= mb * 3) { if (rnd() < 0.45) e = pick(['😎', '💸', '😂']); }
      else if (b.bj.hands.some(h => h.res === 'bust')) { if (rnd() < 0.35) e = pick(['😭', '🤬', '😱']); }
      else if (dBust && b.bj.net > 0) { if (rnd() < 0.3) e = pick(['👏', '😂']); }
      if (e && EMOJIS.includes(e)) setTimeout(() => this.emitReact(b, e), 700 + k * 450 + randInt(500));
    });
  }

  /* ---- 방장 ---- */
  hostCmd(cmd, arg) {
    if (cmd === 'set' && this.status === 'lobby' && arg && typeof arg === 'object') {
      const ok = { stack: [500, 1000, 2000, 5000, 10000, 50000], minBet: [10, 20, 50, 100, 200, 500], timer: [20, 30, 60, 0] };
      for (const k of Object.keys(ok)) if (arg[k] !== undefined && ok[k].includes(+arg[k])) this.settings[k] = +arg[k];
      this.seats.forEach(s => { s.stack = this.settings.stack; });
      this.dirty = true;
    } else if (cmd === 'addbot') {
      return this.addBot(String(arg && arg.lv || 'normal'));
    } else if (cmd === 'start' && this.status === 'lobby') {
      if (!this.seats.some(s => s.online && !s.bot)) return '접속한 사람이 있어야 시작할 수 있어요';
      this.seats.forEach(s => { s.stack = this.settings.stack; s.out = false; s.bj.want = 0; });
      this.status = 'playing'; this.r = this.blankRound(this.r.sq + 1);
      this.statInit();
      this.log(`블랙잭 시작 · 시작 칩 ${fmt(this.settings.stack)}, 최소 베팅 ${fmt(this.settings.minBet)}`);
      this.startRound();
    } else if (cmd === 'next' && this.status === 'playing' && (this.r.st === 'show' || this.r.st === 'idle')) {
      this.nextAt = 0; this.startRound();
    } else if (cmd === 'rebuy') {
      let k = 0; this.seats.forEach(s => { if (s.stack < this.settings.minBet && !(this.live() && s.bj.inR)) { this.statBuy(s, this.settings.stack - s.stack); s.stack = this.settings.stack; s.out = false; k++; } });
      if (k) { this.log(`칩이 떨어진 ${k}명 리바이 (${fmt(this.settings.stack)})`); this.dirty = true; }
    } else if (cmd === 'lobby') {
      this.rankLog();
      this.status = 'lobby'; this.nextAt = 0; this.dealerAt = 0;
      this.r = this.blankRound(this.r.sq + 1); this.msg = '';
      this.seats = this.seats.filter(s => s.online && !s.kicked);
      this.seats.forEach(s => { this.resetBJ(s); s.stack = this.settings.stack; s.out = false; s.inHand = false; });
      this.log('대기실로 돌아왔어요'); this.dirty = true;
    }
    return '';
  }

  /* ---- 주기 처리 ---- */
  tick(now) {
    this.commonTick(now);
    const r = this.r;
    if (this.status === 'playing') {
      if ((r.st === 'show' || r.st === 'idle') && this.nextAt && now >= this.nextAt) { this.nextAt = 0; this.startRound(); }
      else if (r.st === 'bet') {
        for (const s of this.seats) if (s.bot && s.bj.inR && !s.bj.ok && now >= (s.bj.botAt || 0)) { s.bj.want = bjBotBet(this, s); s.bj.ok = true; this.dirty = true; }
        const waiting = this.seats.filter(s => s.bj.inR && !s.bj.ok && s.online && !s.kicked);
        if (!waiting.length || (this.betEnd && now >= this.betEnd)) this.deal();
      } else if (r.st === 'ins') {
        for (const s of this.seats) if (s.bot && s.bj.inR && s.bj.hands.length && !s.bj.insd && now >= (s.bj.botAt || 0)) {
          this.insDecide(s, s.lv === 'easy' && rnd() < 0.35);
        }
        const waiting = this.seats.filter(s => s.bj.inR && s.bj.hands.length && !s.bj.insd && s.online && !s.kicked);
        if (!waiting.length || now >= this.insEnd) { this.seats.forEach(s => { s.bj.insd = true; }); this.afterInsurance(); }
      } else if (r.st === 'play' && r.tu >= 0) {
        const s = this.seats[r.tu], h = s && s.bj.hands[r.hi];
        if (!s || !h) { this.advance(); }
        else if (s.bot) {
          if (this.botFor !== r.sq) { this.botFor = r.sq; this.botAt = now + 650 + randInt(1100); }
          else if (now >= this.botAt) { let m; try { m = bjBotMove(this, s, h); } catch (e) { m = 'stand'; } if (!this.act(r.tu, m)) this.act(r.tu, 'stand'); }
        } else if (s.kicked || now - this.turnStart > this.turnLimit(s)) { if (!s.kicked) this.log(`${s.name} 시간 초과 · 스탠드`); this.act(r.tu, 'stand'); }
      } else if (r.st === 'dealer' && now >= this.dealerAt) this.dealerStep();
    }
    if (this.dirty) { this.dirty = false; this.broadcast(); }
  }

  publicState() {
    const r = this.r, now = Date.now();
    const turnSeat = r.st === 'play' && r.tu >= 0 ? this.seats[r.tu] : null;
    const lim = turnSeat ? this.turnLimit(turnSeat) : Infinity;
    const dl = r.hide && r.dl.length === 2 ? [r.dl[0], 'back'] : r.dl;
    const dv = r.hide ? (r.dl.length ? bjTotal([r.dl[0]]) : { t: 0, soft: false }) : bjTotal(r.dl);
    return {
      game: 'bj', code: this.code, status: this.status, set: this.settings, rules: this.rules, msg: this.msg, rk: this.ranking(),
      seats: this.seats.map(s => ({
        id: s.id, n: s.name, s: s.stack, o: s.out ? 1 : 0, aw: s.online ? 0 : 1, host: s.pid === this.hostPid ? 1 : 0, bot: s.bot ? 1 : 0, lv: s.bot ? BOT_LEVELS[s.lv].label : '',
        pg: s.pendGive || 0, ir: s.bj.inR ? 1 : 0, want: s.bj.want, ok: s.bj.ok ? 1 : 0, sit: s.bj.sit ? 1 : 0, w: s.bj.net, ins: s.bj.ins, insd: s.bj.insd ? 1 : 0, insr: s.bj.insRes,
        hs: s.bj.hands.map(h => { const t = bjTotal(h.cards); return { c: h.cards, b: h.bet, t: t.t, soft: t.soft && t.t < 21 ? 1 : 0, bj: h.nat ? 1 : 0, done: h.done ? 1 : 0, dbl: h.dbl ? 1 : 0, sp: h.split ? 1 : 0, as: h.aceSplit ? 1 : 0, sur: h.sur ? 1 : 0, ev: h.even ? 1 : 0, res: h.res, pay: h.pay }; })
      })),
      h: {
        no: r.no, sq: r.sq, st: r.st, tu: r.tu, hi: r.hi, dl, dt: dv.t, ds: dv.soft && dv.t < 21 ? 1 : 0, line: r.line, dbj: r.dealerBJ ? 1 : 0,
        tl: turnSeat && !turnSeat.bot && isFinite(lim) ? Math.max(0, lim - (now - this.turnStart)) : -1,
        tt: isFinite(lim) ? lim : 0,
        bl: r.st === 'bet' && this.betEnd ? Math.max(0, this.betEnd - now) : (r.st === 'ins' ? Math.max(0, this.insEnd - now) : -1),
        nx: this.nextAt ? Math.max(0, this.nextAt - now) : -1
      }
    };
  }
  sendTo(c, pub) {
    const me = this.seats.findIndex(s => s.pid === c.pid), seat = this.seats[me];
    c.emit('state', { ...pub, me, isHost: c.pid === this.hostPid, lk: seat && seat.lucky ? 1 : 0 });
  }
}

/* ================= 바카라 ================= */
// 규칙 (일반적인 카지노 미니 바카라 기준)
// · 8덱 슈 · 카드 값: A=1, 2~9=숫자, 10/J/Q/K=0, 합계의 일의 자리만 씀
// · 처음 두 장이 8이나 9면 내추럴 → 둘 다 멈춤
// · 플레이어: 0~5 한 장 더, 6~7 멈춤
// · 뱅커: 플레이어가 멈췄으면 0~5 한 장 더. 플레이어가 세 번째 카드를 받았으면
//   0~2 받음 / 3: 그 카드가 8이 아니면 / 4: 2~7이면 / 5: 4~7이면 / 6: 6~7이면 / 7 멈춤
// · 배당: 플레이어 1:1 · 뱅커 1:1에서 5% 커미션(0.95:1) · 타이 8:1 (타이면 플레이어/뱅커 베팅은 돌려받음)
// · 플레이어 페어 / 뱅커 페어: 처음 두 장이 같은 숫자면 11:1
// · 플레이어 보너스 / 뱅커 보너스 (드래곤 보너스): 내추럴로 이기면 1:1, 내추럴 타이면 돌려받음,
//   내추럴이 아닐 때 9점 차 30:1, 8점 차 10:1, 7점 차 6:1, 6점 차 4:1, 5점 차 2:1, 4점 차 1:1, 그 아래는 짐
const BAC_DECKS = 8;
const BAC_SPOTS = ['p', 'b', 't', 'pp', 'bp', 'pb', 'bb'];
const BAC_NAMES = { p: '플레이어', b: '뱅커', t: '타이', pp: 'P페어', bp: 'B페어', pb: 'P보너스', bb: 'B보너스' };
const BAC_BONUS = { 9: 30, 8: 10, 7: 6, 6: 4, 5: 2, 4: 1 };
const bacVal = c => 'TJQK'.includes(c[0]) ? 0 : c[0] === 'A' ? 1 : +c[0];
const bacTot = cs => cs.reduce((a, c) => a + bacVal(c), 0) % 10;
function bacPlay(seq) {
  let i = 0;
  const p = [seq[i++]], b = [seq[i++]]; p.push(seq[i++]); b.push(seq[i++]);
  const p2 = bacTot(p), b2 = bacTot(b);
  const nat = p2 >= 8 || b2 >= 8;
  if (!nat) {
    let p3 = null;
    if (p2 <= 5) { p3 = seq[i++]; p.push(p3); }
    let bDraw;
    if (p3 === null) bDraw = b2 <= 5;
    else {
      const x = bacVal(p3);
      bDraw = b2 <= 2 || (b2 === 3 && x !== 8) || (b2 === 4 && x >= 2 && x <= 7) || (b2 === 5 && x >= 4 && x <= 7) || (b2 === 6 && (x === 6 || x === 7));
    }
    if (bDraw) b.push(seq[i++]);
  }
  const pt = bacTot(p), bt = bacTot(b);
  return { p, b, pt, bt, win: pt > bt ? 'P' : bt > pt ? 'B' : 'T', used: i, pNat: nat && p2 >= 8, bNat: nat && b2 >= 8, pp: p[0][0] === p[1][0], bp: b[0][0] === b[1][0] };
}
function bacBonusMult(side, o) {
  const mine = side === 'P' ? o.pt : o.bt, other = side === 'P' ? o.bt : o.pt, nat = side === 'P' ? o.pNat : o.bNat;
  if (o.win === side) { if (nat) return 2; const m = BAC_BONUS[mine - other]; return m ? m + 1 : 0; }
  if (o.win === 'T' && nat) return 1;
  return 0;
}
// 각 칸에 건 금액 a가 돌려받는 총액(원금 포함)
function bacReturn(spot, a, o) {
  if (!a) return 0;
  switch (spot) {
    case 'p': return o.win === 'P' ? a * 2 : o.win === 'T' ? a : 0;
    case 'b': return o.win === 'B' ? a + Math.floor(a * 0.95) : o.win === 'T' ? a : 0;
    case 't': return o.win === 'T' ? a * 9 : 0;
    case 'pp': return o.pp ? a * 12 : 0;
    case 'bp': return o.bp ? a * 12 : 0;
    case 'pb': return a * bacBonusMult('P', o);
    case 'bb': return a * bacBonusMult('B', o);
  }
  return 0;
}
const bacSum = bets => BAC_SPOTS.reduce((a, k) => a + (bets[k] || 0), 0);
const bacNet = (bets, o) => BAC_SPOTS.reduce((a, k) => a + bacReturn(k, bets[k] || 0, o), 0) - bacSum(bets);
function bacBotBets(room, s) {
  const u = Math.max(1, Math.min(room.settings.minBet, s.stack)), L = s.lv || 'normal', bets = {};
  const main = L === 'hard' ? (rnd() < 0.7 ? 'b' : 'p') : (rnd() < 0.5 ? 'p' : 'b');
  bets[main] = u * (L === 'easy' ? 1 + randInt(4) : L === 'hard' ? 2 + randInt(2) : 1 + randInt(3));
  if (L === 'easy') { if (rnd() < 0.25) bets.t = u; if (rnd() < 0.2) bets[rnd() < 0.5 ? 'pp' : 'bp'] = u; if (rnd() < 0.15) bets[main === 'p' ? 'pb' : 'bb'] = u; }
  else if (L === 'normal') { if (rnd() < 0.08) bets.t = u; if (rnd() < 0.08) bets[rnd() < 0.5 ? 'pp' : 'bp'] = u; }
  // 칩이 모자라면 큰 칸부터 줄임
  while (bacSum(bets) > s.stack) { const k = Object.keys(bets).sort((a, b) => bets[b] - bets[a])[0]; if (bets[k] > u) bets[k] -= u; else delete bets[k]; if (!Object.keys(bets).length) break; }
  return bets;
}

class BacRoom extends Room {
  constructor(code) {
    super(code);
    this.game = 'bac';
    this.settings = { stack: 1000, minBet: 20, timer: 20 };
    this.shoe = newShoe(BAC_DECKS); this.shoeNo = 1;
    this.r = this.blankRound(0);
    this.betEnd = 0; this.stepAt = 0;
  }
  blankRound(sq) { return { no: 0, sq, st: 'idle', o: null, order: [], shown: 0, line: '', hist: this.r ? this.r.hist : [], lucky: null, unlucky: null }; }
  newSeat(pid, name) { const s = super.newSeat(pid, name); s.bac = { bets: {}, last: {}, ok: false, sit: false, inR: false, net: 0, res: {} }; return s; }
  resetBac(s) { s.bac = { bets: {}, last: s.bac ? s.bac.last : {}, ok: false, sit: false, inR: false, net: 0, res: {} }; s.won = 0; s.inHand = false; }
  reveal() { return false; }
  live() { return this.r.st === 'deal'; }
  safeToRemove() { return this.status !== 'playing' || this.r.st !== 'deal'; }
  canDropOffline() { return this.safeToRemove() && this.r.st !== 'bet'; }
  removeSeatAt(i) { this.seats.splice(i, 1); }
  onKick() {}
  minStake() { return 1; } // 챌린지에서는 1,000

  startRound() {
    const r = this.r, now = Date.now();
    this.seats.forEach(s => this.resetBac(s));
    const humanHere = this.seats.some(s => !s.bot && s.online);
    // 바카라는 최소 베팅 없음: 칩이 1개라도 있으면 참여 (챌린지는 1,000)
    this.seats.forEach(s => { s.out = s.stack < this.minStake(); });
    const elig = this.seats.filter(s => s.online && !s.out && !s.kicked);
    if (!humanHere || !elig.length) {
      r.st = 'idle'; r.sq++; this.msg = !humanHere ? '접속한 사람이 없어서 쉬는 중이에요' : '베팅할 칩이 있는 사람이 없어요. 방장이 리바이를 해 주세요';
      this.nextAt = now + 3000; this.dirty = true; return;
    }
    this.msg = '';
    if (this.shoe.length < 52 * BAC_DECKS * 0.15) { this.shoe = newShoe(BAC_DECKS); this.shoeNo++; r.hist = []; this.log(`카드를 새로 섞었어요 · 슈 #${this.shoeNo}, 그림장을 새로 시작해요`); }
    Object.assign(r, { st: 'bet', o: null, order: [], shown: 0, line: '', lucky: null, unlucky: null });
    r.no++; r.sq++;
    const ls = this.seats.find(s => s.lucky && elig.includes(s));
    if (ls) { if (rnd() < LUCKY_RATE) r.lucky = ls.id; else r.unlucky = ls.id; }
    elig.forEach(s => { s.bac.inR = true; if (s.bot) s.bac.botAt = now + 800 + randInt(2200); });
    this.betEnd = this.settings.timer ? now + this.settings.timer * 1000 : 0;
    this.log(`#${r.no} 베팅 시작`);
    this.dirty = true;
  }
  bacMsg(pid, msg) {
    const r = this.r, s = this.seatOf(pid);
    if (!s || r.st !== 'bet' || !s.bac.inR || s.bac.ok) return;
    const a = String(msg.a || '');
    if (a === 'sit') { s.bac.ok = true; s.bac.sit = true; this.log(`${s.name} 이번 판 쉬기`); this.dirty = true; this.tick(Date.now()); return; }
    if (a !== 'betok') return;
    const src = msg.bets && typeof msg.bets === 'object' ? msg.bets : {};
    const bets = {};
    for (const k of BAC_SPOTS) { const v = Math.floor(+src[k] || 0); if (v > 0) bets[k] = v; }
    const sum = bacSum(bets);
    if (!sum) { tell(pid, 'err', '베팅할 칸을 골라 주세요'); return; }
    if (sum > s.stack) { tell(pid, 'err', '가진 칩보다 많이 걸 수 없어요'); return; }
    s.bac.bets = bets; s.bac.last = { ...bets }; s.bac.ok = true; this.dirty = true;
    this.tick(Date.now());
  }
  deal() {
    const r = this.r, now = Date.now();
    const players = this.seats.filter(s => s.bac.inR && s.bac.ok && !s.bac.sit && s.online && !s.kicked && bacSum(s.bac.bets) > 0 && bacSum(s.bac.bets) <= s.stack);
    this.seats.forEach(s => { if (!players.includes(s)) { s.bac.inR = false; s.bac.bets = {}; } });
    players.forEach(s => { s.stack -= bacSum(s.bac.bets); s.inHand = true; });
    // 카드 고르기: 보통은 슈 맨 위에서 그대로. 행운 판이면 조건에 맞는 카드 조합을 슈 안에서 무작위로 찾아서 사용
    let seq = null, o = null;
    const ls = this.seats.find(s => (s.id === r.lucky || s.id === r.unlucky) && players.includes(s));
    if (ls) {
      const want = r.lucky ? 1 : -1;
      const n = this.shoe.length;
      for (let t = 0; t < 4000; t++) {
        const idx = new Set(); while (idx.size < 6) idx.add(randInt(n));
        const ix = [...idx], cand = ix.map(k => this.shoe[k]);
        const oc = bacPlay(cand), net = bacNet(ls.bac.bets, oc);
        if ((want > 0 && net > 0) || (want < 0 && net < 0)) {
          const used = ix.slice(0, oc.used).sort((a, b) => b - a);
          for (const k of used) this.shoe.splice(k, 1);
          seq = cand.slice(0, oc.used); o = oc; break;
        }
      }
    }
    if (!o) { const top = this.shoe.slice(-6).reverse(); o = bacPlay(top); for (let k = 0; k < o.used; k++) this.shoe.pop(); }
    r.o = o;
    r.order = [['p', 0], ['b', 0], ['p', 1], ['b', 1]];
    if (o.p.length === 3) r.order.push(['p', 2]);
    if (o.b.length === 3) r.order.push(['b', 2]);
    r.shown = 0; r.st = 'deal'; r.sq++;
    this.stepAt = now + 500;
    if (!players.length) { r.st = 'show'; r.line = '모두 이번 판을 쉬었어요'; r.o = null; this.nextAt = now + 2500; }
    this.dirty = true;
  }
  step(now) {
    const r = this.r;
    if (r.shown < r.order.length) {
      r.shown++;
      // 세 번째 카드 전에는 살짝 더 뜸 들이기
      this.stepAt = now + (r.shown >= 4 && r.shown < r.order.length ? 1100 : 650);
      this.dirty = true;
    } else this.settle();
  }
  settle() {
    const r = this.r, o = r.o, now = Date.now();
    const parts = [];
    for (const s of this.seats) {
      if (!s.bac.inR || !bacSum(s.bac.bets)) continue;
      let back = 0; const res = {};
      for (const k of BAC_SPOTS) { const a = s.bac.bets[k] || 0; if (!a) continue; const x = bacReturn(k, a, o); res[k] = x - a; back += x; }
      const net = back - bacSum(s.bac.bets);
      s.stack += back; s.bac.net = net; s.bac.res = res; s.won = net;
      this.statHand(s, net);
      parts.push(`${s.name} ${net > 0 ? '+' : ''}${fmt(net)}`);
    }
    const extras = [o.pp ? 'P페어' : '', o.bp ? 'B페어' : '', (o.pNat || o.bNat) ? '내추럴' : ''].filter(Boolean).join('·');
    r.line = (o.win === 'P' ? `플레이어 승 · ${o.pt} 대 ${o.bt}` : o.win === 'B' ? `뱅커 승 · ${o.bt} 대 ${o.pt}` : `타이 · ${o.pt} 대 ${o.bt}`) + (extras ? ` (${extras})` : '');
    r.hist = [...(r.hist || []), { w: o.win, pp: o.pp ? 1 : 0, bp: o.bp ? 1 : 0, n: o.win === 'B' ? o.bt : o.pt, nat: (o.pNat || o.bNat) ? 1 : 0 }].slice(-150);
    this.log(`#${r.no} ${r.line}${parts.length ? ' · ' + parts.join(', ') : ''}`);
    r.st = 'show'; r.sq++;
    this.seats.forEach(s => { s.out = s.stack < this.minStake(); });
    this.nextAt = now + 6500;
    this.bacBotReactions(o);
    this.dirty = true;
  }
  bacBotReactions(o) {
    const pick = arr => arr[randInt(arr.length)];
    const mb = this.settings.minBet;
    this.seats.filter(s => s.bot && s.bac.inR && bacSum(s.bac.bets)).forEach((b, k) => {
      let e = null;
      if (b.bac.net >= mb * 5) { if (rnd() < 0.6) e = pick(['😎', '💸', '🔥']); }
      else if (b.bac.net > 0) { if (rnd() < 0.2) e = pick(['😂', '👍']); }
      else if (b.bac.net <= -mb * 3) { if (rnd() < 0.4) e = pick(['😭', '🤬', '😱']); }
      else if (o.win === 'T') { if (rnd() < 0.3) e = '😱'; }
      if (e && EMOJIS.includes(e)) setTimeout(() => this.emitReact(b, e), 700 + k * 450 + randInt(500));
    });
  }
  hostCmd(cmd, arg) {
    if (cmd === 'set' && this.status === 'lobby' && arg && typeof arg === 'object') {
      const ok = { stack: [500, 1000, 2000, 5000, 10000, 50000], minBet: [10, 20, 50, 100, 200, 500], timer: [15, 20, 30, 0] };
      for (const k of Object.keys(ok)) if (arg[k] !== undefined && ok[k].includes(+arg[k])) this.settings[k] = +arg[k];
      this.seats.forEach(s => { s.stack = this.settings.stack; });
      this.dirty = true;
    } else if (cmd === 'addbot') {
      return this.addBot(String(arg && arg.lv || 'normal'));
    } else if (cmd === 'start' && this.status === 'lobby') {
      if (!this.seats.some(s => s.online && !s.bot)) return '접속한 사람이 있어야 시작할 수 있어요';
      this.seats.forEach(s => { s.stack = this.settings.stack; s.out = false; });
      this.status = 'playing'; this.r = this.blankRound(this.r.sq + 1); this.r.hist = []; this.shoe = newShoe(BAC_DECKS); this.shoeNo = 1;
      this.statInit();
      this.log(`바카라 시작 · 시작 칩 ${fmt(this.settings.stack)} · 베팅 금액 자유`);
      this.startRound();
    } else if (cmd === 'next' && this.status === 'playing' && (this.r.st === 'show' || this.r.st === 'idle')) {
      this.nextAt = 0; this.startRound();
    } else if (cmd === 'rebuy') {
      let k = 0; this.seats.forEach(s => { if (s.stack < this.settings.minBet && !(this.live() && s.bac.inR)) { this.statBuy(s, this.settings.stack - s.stack); s.stack = this.settings.stack; s.out = false; k++; } });
      if (k) { this.log(`칩이 떨어진 ${k}명 리바이 (${fmt(this.settings.stack)})`); this.dirty = true; }
    } else if (cmd === 'lobby') {
      this.rankLog();
      this.status = 'lobby'; this.nextAt = 0;
      this.r = this.blankRound(this.r.sq + 1); this.msg = '';
      this.seats = this.seats.filter(s => s.online && !s.kicked);
      this.seats.forEach(s => { this.resetBac(s); s.stack = this.settings.stack; s.out = false; });
      this.log('대기실로 돌아왔어요'); this.dirty = true;
    }
    return '';
  }
  tick(now) {
    this.commonTick(now);
    const r = this.r;
    if (this.status === 'playing') {
      if ((r.st === 'show' || r.st === 'idle') && this.nextAt && now >= this.nextAt) { this.nextAt = 0; this.startRound(); }
      else if (r.st === 'bet') {
        for (const s of this.seats) if (s.bot && s.bac.inR && !s.bac.ok && now >= (s.bac.botAt || 0)) { const b = bacBotBets(this, s); if (bacSum(b)) { s.bac.bets = b; s.bac.ok = true; } else { s.bac.ok = true; s.bac.sit = true; } this.dirty = true; }
        const waiting = this.seats.filter(s => s.bac.inR && !s.bac.ok && s.online && !s.kicked);
        if (!waiting.length || (this.betEnd && now >= this.betEnd)) this.deal();
      } else if (r.st === 'deal' && now >= this.stepAt) this.step(now);
    }
    if (this.dirty) { this.dirty = false; this.broadcast(); }
  }
  publicState() {
    const r = this.r, now = Date.now(), o = r.o;
    const pc = [], bc = [];
    if (o) for (let k = 0; k < r.shown; k++) { const [side, j] = r.order[k]; (side === 'p' ? pc : bc).push(o[side][j]); }
    const done = r.st === 'show' && o;
    return {
      game: 'bac', code: this.code, status: this.status, set: this.settings, msg: this.msg, rk: this.ranking(),
      seats: this.seats.map(s => ({
        id: s.id, n: s.name, s: s.stack, o: s.out ? 1 : 0, aw: s.online ? 0 : 1, host: s.pid === this.hostPid ? 1 : 0, bot: s.bot ? 1 : 0, lv: s.bot ? BOT_LEVELS[s.lv].label : '',
        pg: s.pendGive || 0, ir: s.bac.inR ? 1 : 0, ok: s.bac.ok ? 1 : 0, sit: s.bac.sit ? 1 : 0, bets: s.bac.ok ? s.bac.bets : {}, last: s.bac.last, w: s.bac.net, res: s.bac.res
      })),
      h: {
        no: r.no, sq: r.sq, st: r.st, pc, bc, pt: pc.length ? bacTot(pc) : -1, bt: bc.length ? bacTot(bc) : -1,
        o: done ? { win: o.win, pt: o.pt, bt: o.bt, pp: o.pp ? 1 : 0, bp: o.bp ? 1 : 0, pn: o.pNat ? 1 : 0, bn: o.bNat ? 1 : 0 } : null,
        line: r.line, hist: r.hist || [], sh: this.shoeNo, left: this.shoe.length, tu: -1, tl: -1, tt: 0,
        bl: r.st === 'bet' && this.betEnd ? Math.max(0, this.betEnd - now) : -1,
        nx: this.nextAt ? Math.max(0, this.nextAt - now) : -1
      }
    };
  }
  sendTo(c, pub) {
    const me = this.seats.findIndex(s => s.pid === c.pid), seat = this.seats[me];
    c.emit('state', { ...pub, me, isHost: c.pid === this.hostPid, lk: seat && seat.lucky ? 1 : 0 });
  }
}

/* ================= 챌린지 (보스 깨기) ================= */
// 홀덤 · 블랙잭 · 바카라 각각 5단계. 혼자(1:1) 또는 친구들과 같이 보스를 쓰러뜨리면 다음 단계가 열려요.
// · 참가자는 모두 10,000칩으로 시작 · 홀덤 블라인드 100/200(10판마다 상승) · 블랙잭/바카라 최소 베팅 1,000
// · 홀덤: 보스 AI의 칩을 0으로 만들면 클리어, 우리 팀이 모두 탈락하면 실패
// · 블랙잭/바카라: 보스 체력 = 우리 팀이 따내야 할 칩. 정해진 라운드 안에 체력을 0으로 만들면 클리어
// · 친구랑 같이 하면 체력이 사람 수에 맞춰 늘어나요 (블랙잭 인원^0.7배, 바카라는 모두 같은 카드라 인원 배)
const CH_START = 10000;
const CH_INTRO_MS = 5600;
const CH_BLIND_EVERY = 10;
const CH_BLINDS = [[100, 200], [200, 400], [300, 600], [500, 1000], [800, 1600], [1000, 2000], [1500, 3000], [2000, 4000], [3000, 6000], [5000, 10000]];
const CH_GAMES = { holdem: '홀덤', bj: '블랙잭', bac: '바카라' };
const BJ_STD = { h17: false, bjPay: 1.5, sur: true, das: true };
const CH_STAGES = {
  holdem: [
    { name: '새내기 토끼', emo: '🐰', lv: 'easy', boss: 10000, diff: '쉬움', quote: '포… 포커는 처음인데 살살 해 줘!', skill: '아무 패나 들고 따라와요' },
    { name: '꾀돌이 여우', emo: '🦊', lv: 'normal', boss: 10000, diff: '보통', quote: '속는 쪽이 지는 거야~ 히히.', skill: '가끔 블러핑을 섞어요' },
    { name: '카지노 상어', emo: '🦈', lv: 'hard', boss: 12000, diff: '살짝 어려움', quote: '피 냄새가 나는군. 네 칩에서.', skill: '확률 계산이 정확해요 · 보스 칩 1.2배' },
    { name: '포커페이스 늑대', emo: '🐺', lv: 'pro', boss: 15000, diff: '많이 어려움', quote: '네 손이 떨리는 게 다 보여.', skill: '네 습관을 읽고 손패 범위를 계산해요 · 보스 칩 1.5배' },
    { name: '수완 드래곤', emo: '🐉', lv: 'boss', boss: 20000, diff: '극악', quote: '여기까지 온 건 칭찬하지. 하지만 여기가 끝이다.', skill: '매 베팅마다 최선의 수 · 습관 완전 분석 · 보스 칩 2배' }
  ],
  bj: [
    { name: '병아리 딜러', emo: '🐣', hp: 3000, rounds: 15, maxBet: 5000, rules: { ...BJ_STD }, diff: '쉬움', quote: '삐약! 카드 나눠 주는 건 자신 있어요!', skill: '기본 규칙 · 딜러 소프트 17 스탠드' },
    { name: '고양이 딜러', emo: '🐱', hp: 6000, rounds: 15, maxBet: 5000, rules: { ...BJ_STD }, diff: '보통', quote: '냥… 내 앞발은 빠르다냥.', skill: '기본 규칙 · 체력 증가' },
    { name: '부엉이 딜러', emo: '🦉', hp: 12000, rounds: 15, maxBet: 5000, rules: { ...BJ_STD, h17: true }, diff: '살짝 어려움', quote: '밤새 카드를 세어 왔지. 부엉.', skill: '딜러가 소프트 17에서도 한 장 더 받아요' },
    { name: '사자 딜러', emo: '🦁', hp: 20000, rounds: 12, maxBet: 5000, rules: { ...BJ_STD, h17: true, sur: false }, diff: '많이 어려움', quote: '도망칠 생각은 버려라. 서렌더는 없다.', skill: '소프트 17 히트 · 서렌더 금지 · 12라운드 제한' },
    { name: '해골 딜러', emo: '💀', hp: 28000, rounds: 12, maxBet: 5000, rules: { h17: true, bjPay: 1.2, sur: false, das: false }, diff: '극악', quote: '데스 테이블에 온 걸 환영한다… 크크크.', skill: '소프트 17 히트 · 블랙잭 6:5 · 서렌더 금지 · 스플릿 후 더블 금지 · 12라운드 제한' }
  ],
  bac: [
    { name: '판다 뱅커', emo: '🐼', hp: 3000, rounds: 15, maxBet: 5000, diff: '쉬움', quote: '대나무 걸고 한 판? 냠냠.', skill: '기본 규칙' },
    { name: '호랑이 뱅커', emo: '🐯', hp: 6000, rounds: 15, maxBet: 5000, diff: '보통', quote: '어흥! 내 줄무늬처럼 줄줄이 이겨 주지.', skill: '체력 증가' },
    { name: '문어 뱅커', emo: '🐙', hp: 12000, rounds: 15, maxBet: 5000, diff: '살짝 어려움', quote: '다리가 여덟 개라 카드도 여덟 덱이지.', skill: '체력 증가' },
    { name: '독수리 뱅커', emo: '🦅', hp: 17000, rounds: 12, maxBet: 5000, diff: '많이 어려움', quote: '높은 곳에서 네 칩을 노리고 있다.', skill: '체력 크게 증가 · 12라운드 제한' },
    { name: '바카라 황제', emo: '👑', hp: 22000, rounds: 12, maxBet: 5000, diff: '극악', quote: '짐의 테이블이다. 무릎 꿇어라.', skill: '체력 최대 · 12라운드 안에 쓰러뜨려야 해요' }
  ]
};
const CH_TAUNT = {
  hurt: ['크윽… 제법이군.', '이, 이럴 리가 없어!', '운이 좋았을 뿐이다!', '아직 끝나지 않았다…', '흥, 간지럽군.'],
  win: ['크하하! 그 정도로는 안 돼.', '내 테이블에서 이길 수 있을 것 같았나?', '고마워, 칩 잘 받을게~', '다음엔 더 잘해 봐.', '한 판 더 줄까? 후후.'],
  half: '체력이 절반 남았다고 방심하지 마라!',
  low: '크아아… 이 몸이 밀리다니!'
};
// 화면에 보낼 단계 정보 (챌린지 메뉴에서 씀)
const CH_INFO_PUB = Object.fromEntries(Object.entries(CH_STAGES).map(([g, L]) => [g, L.map(c => ({ name: c.name, emo: c.emo, diff: c.diff, quote: c.quote, skill: c.skill, boss: c.boss || 0, hp: c.hp || 0, rounds: c.rounds || 0, minBet: 1000, maxBet: c.maxBet || 0 }))]));
const chHpScale = (per, n, ex) => Math.round(per * Math.pow(n, ex) / 100) * 100;

/* ---- 명예의 전당 기록: 서버 파일 + 접속한 사람들 폰에도 서명된 사본을 보관 ----
   무료 서버가 재시작돼서 파일이 지워져도, 누군가 다시 접속하면 그 폰에 있던 기록을 서버가 서명 확인 후 되살려요. */
const DATA_DIR = process.env.DATA_DIR || path.join(__dirname, 'data');
const HOF_FILE = path.join(DATA_DIR, 'challenge.json');
const HOF_SECRET = process.env.HOF_SECRET || 'suwan-challenge-hof-2026';
const HOF = { recs: [], ids: new Set() };
const recSig = r => crypto.createHmac('sha256', HOF_SECRET).update(JSON.stringify([r.id, r.g, r.st, r.team, r.t, r.n, r.ms])).digest('base64url').slice(0, 24);
function recClean(x) {
  if (!x || typeof x !== 'object' || !Array.isArray(x.team)) return null;
  const r = { id: String(x.id || '').slice(0, 12), g: String(x.g || ''), st: Math.floor(+x.st), team: x.team.slice(0, 8).map(m => [String(m && m[0] || '').slice(0, 24), String(m && m[1] || '').slice(0, 10)]), t: Math.floor(+x.t) || 0, n: Math.floor(+x.n) || 0, ms: Math.floor(+x.ms) || 0 };
  if (!r.id || !CH_STAGES[r.g] || !(r.st >= 1 && r.st <= 5)) return null;
  r.sig = recSig(r);
  return r.sig === String(x.sig || '') ? r : null;
}
let hofT = null;
function hofSaveSoon() {
  clearTimeout(hofT);
  hofT = setTimeout(() => {
    try { fs.mkdirSync(DATA_DIR, { recursive: true }); const tmp = HOF_FILE + '.tmp'; fs.writeFileSync(tmp, JSON.stringify({ v: 1, recs: HOF.recs })); fs.renameSync(tmp, HOF_FILE); }
    catch (e) { console.error('챌린지 기록 저장 실패:', e.message); }
  }, 1200);
}
function hofAdd(r) {
  if (HOF.ids.has(r.id)) return false;
  HOF.ids.add(r.id); HOF.recs.push(r); HOF.recs.sort((a, b) => a.t - b.t);
  hofSaveSoon(); return true;
}
function hofLoad() {
  try { const j = JSON.parse(fs.readFileSync(HOF_FILE, 'utf8')); let k = 0; for (const x of j.recs || []) { const r = recClean(x); if (r && hofAdd(r)) k++; } console.log(`챌린지 기록 ${k}개 불러옴`); }
  catch (e) { /* 처음 실행이면 파일 없음 */ }
}
function chCleared(uid, g) { const set = new Set(); if (!uid) return set; for (const r of HOF.recs) if (r.g === g && r.team.some(m => m[0] === uid)) set.add(r.st); return set; }
function chMaxOpen(uid, g) { let m = 0; for (const x of chCleared(uid, g)) m = Math.max(m, x); return Math.min(5, m + 1); }

const ChMix = Base => class extends Base {
  chInit(g, st) { this.ch = { g, st, seq: 0, state: 'ready', team: [], t0: 0, result: null, introUntil: 0, hpMax: 0, base: 0, stk: {}, dmg: 0, net: 0, fresh: [], marks: {} }; this.chApply(); }
  get cfg() { return CH_STAGES[this.ch.g][this.ch.st - 1]; }
  chApply() {}
  addBot() { return '챌린지에서는 AI를 따로 넣을 수 없어요. 보스랑 싸워야 해요!'; }
  bossSay(t) { const c = this.cfg; const b = this.seats.find(s => s.boss); this.pushChat({ n: `${c.emo} ${c.name}`, sid: b ? b.id : '', t, boss: 1 }); }
  // 관전 중이던 사람(도전 중에 들어온 사람)을 다음 도전 때 자리에 앉힘
  chSeatSpectators() {
    for (const c of this.socks) {
      if (c.watch || !c.name || this.seatOf(c.pid) || this.banned.has(c.pid)) continue;
      if (this.seats.filter(s => !s.bot).length >= this.chHumanCap()) break;
      const seat = this.newSeat(c.pid, c.name); seat.uid = c.uid || ''; this.seats.push(seat);
      this.log(`${c.name} 도전 합류`);
    }
  }
  chStart() {
    const now = Date.now(), ch = this.ch;
    this.chSeatSpectators();
    this.seats = this.seats.filter(s => !s.bot && !s.kicked && s.online);
    const humans = this.seats;
    if (!humans.length) return '접속한 사람이 있어야 도전할 수 있어요';
    this.chApply();
    ch.team = humans.map(s => [s.uid || '', s.name]);
    ch.seq++; ch.state = 'intro'; ch.introUntil = now + CH_INTRO_MS; ch.result = null; ch.t0 = now;
    ch.dmg = 0; ch.net = 0; ch.fresh = []; ch.marks = {};
    this.status = 'playing'; this.msg = ''; this.nextAt = 0;
    this.chSetup(humans);
    this.statInit();
    const c = this.cfg;
    this.log(`⚔️ ${CH_GAMES[ch.g]} 챌린지 STAGE ${ch.st} · ${c.emo} ${c.name} 등장! (${humans.length}명 도전)`);
    this.dirty = true; return '';
  }
  chBossMood(prevHp, hp) { // 체력이 절반·4분의 1 아래로 내려갈 때 한마디
    const ch = this.ch, m = ch.hpMax;
    if (!ch.marks.half && prevHp > m / 2 && hp <= m / 2 && hp > 0) { ch.marks.half = 1; setTimeout(() => this.bossSay(CH_TAUNT.half), 1400); return true; }
    if (!ch.marks.low && prevHp > m / 4 && hp <= m / 4 && hp > 0) { ch.marks.low = 1; setTimeout(() => this.bossSay(CH_TAUNT.low), 1400); return true; }
    return false;
  }
  chEnd(win) {
    const ch = this.ch, now = Date.now(), c = this.cfg;
    if (ch.state === 'clear' || ch.state === 'fail') return;
    ch.state = win ? 'clear' : 'fail'; this.status = 'over'; this.nextAt = 0;
    const n = this.chNo(), ms = Math.max(0, now - ch.t0 - CH_INTRO_MS);
    let rec = null;
    if (win) {
      const team = ch.team.filter(m => m[0]);
      const fresh = team.filter(m => !chCleared(m[0], ch.g).has(ch.st));
      ch.fresh = fresh.map(m => m[1]);
      if (fresh.length) { rec = { id: crypto.randomBytes(6).toString('base64url'), g: ch.g, st: ch.st, team, t: now, n, ms }; rec.sig = recSig(rec); hofAdd(rec); }
    }
    const say = win ? (ch.st === 5 ? '말도 안 돼… 네가 진짜 챔피언이다.' : '크윽… 다음 단계에서 기다리겠다!') : CH_TAUNT.win[randInt(CH_TAUNT.win.length)];
    ch.result = { win: win ? 1 : 0, n, ms, rec: rec ? rec.id : '', at: now, say };
    this.log(win ? `🏆 STAGE ${ch.st} CLEAR! ${c.emo} ${c.name} 격파 · ${n}${this.chUnit()} 만에` : `💀 STAGE ${ch.st} 실패… ${c.emo} ${c.name}에게 졌어요`);
    setTimeout(() => this.bossSay(say), 2200);
    if (rec) for (const sock of this.socks) sock.emit('hofrec', rec);
    this.dirty = true;
  }
  chHostMax() { const h = this.seatOf(this.hostPid); return chMaxOpen(h && h.uid, this.ch.g); }
  hostCmd(cmd, arg) {
    const ch = this.ch;
    if (cmd === 'start' && this.status === 'lobby') return this.chStart();
    if (cmd === 'chretry' && this.status === 'over') return this.chStart();
    if (cmd === 'chnext' && this.status === 'over') {
      if (ch.state !== 'clear' || ch.st >= 5) return '다음 단계가 없어요';
      if (ch.st + 1 > this.chHostMax()) return '방장이 이 단계를 깨야 다음 단계를 열 수 있어요';
      ch.st++; return this.chStart();
    }
    if (cmd === 'chstage' && this.status === 'lobby') {
      const st = Math.floor(+(arg && arg.st));
      if (!(st >= 1 && st <= 5)) return '';
      if (st > this.chHostMax()) return '아직 열리지 않은 단계예요';
      ch.st = st; this.chApply(); this.log(`도전 단계 변경 · STAGE ${st} ${this.cfg.emo} ${this.cfg.name}`); this.dirty = true; return '';
    }
    if (cmd === 'lobby') { if (this.status === 'playing') this.log('🏳️ 도전을 포기했어요'); this.chToLobby(); return ''; }
    if (cmd === 'next') return super.hostCmd(cmd, arg);
    return '챌린지에서는 바꿀 수 없어요';
  }
  tick(now) {
    if (this.status === 'playing' && this.ch.state === 'intro') {
      this.commonTick(now);
      if (now >= this.ch.introUntil) { this.ch.state = 'play'; this.dirty = true; this.chBegin(); }
      if (this.dirty) { this.dirty = false; this.broadcast(); }
      return;
    }
    super.tick(now);
  }
  // 블랙잭/바카라 공통: 라운드가 끝날 때마다 팀 손익 = 보스에게 준 피해
  chAfterRound() {
    const ch = this.ch; if (ch.state !== 'play') return;
    for (const s of this.seats) if (ch.stk[s.id] !== undefined) ch.stk[s.id] = s.stack;
    const prevHp = this.chHp();
    const net = Object.values(ch.stk).reduce((a, x) => a + x, 0) - ch.base;
    ch.dmg = net - ch.net; ch.net = net;
    const hp = this.chHp();
    if (hp <= 0) { this.chEnd(true); return; }
    const spoke = this.chBossMood(prevHp, hp);
    if (!spoke && Math.abs(ch.dmg) >= this.settings.minBet * 3 && rnd() < 0.35) setTimeout(() => this.bossSay((ch.dmg > 0 ? CH_TAUNT.hurt : CH_TAUNT.win)[randInt(5)]), 1800);
    if (this.r.no >= this.cfg.rounds) { this.chEnd(false); return; }
    if (!this.seats.some(s => ch.stk[s.id] !== undefined && s.stack >= this.chMinStake() && s.online)) this.chEnd(false);
  }
  chMinStake() { return this.settings.minBet; }
  chPub() {
    const ch = this.ch, c = this.cfg, now = Date.now();
    return {
      g: ch.g, st: ch.st, seq: ch.seq, state: ch.state,
      boss: { n: c.name, emo: c.emo, diff: c.diff, quote: c.quote, skill: c.skill },
      hp: Math.max(0, this.chHp()), hpRaw: this.chHp(), hpMax: ch.hpMax, dmg: ch.dmg, no: this.chNo(), max: c.rounds || 0,
      intro: ch.state === 'intro' ? Math.max(0, ch.introUntil - now) : 0,
      result: ch.result, team: ch.team.map(m => m[1]), fresh: ch.fresh, hostMax: this.chHostMax(), info: this.chInfo(), unit: this.chUnit()
    };
  }
  publicState() { const p = super.publicState(); p.ch = this.chPub(); return p; }
};

class ChHoldem extends ChMix(Room) {
  constructor(code) { super(code); this.settings = { stack: CH_START, sb: 100, bb: 200, timer: 30 }; }
  chHumanCap() { return 6; }
  chUnit() { return '판'; }
  chNo() { return this.hand.no; }
  chSetup(humans) {
    const c = this.cfg;
    humans.forEach(s => { this.resetSeatHand(s); s.stack = CH_START; s.out = false; s.st0 = CH_START; });
    const boss = this.newSeat('boss:' + crypto.randomBytes(5).toString('hex'), c.name);
    Object.assign(boss, { bot: true, lv: c.lv, boss: true, emo: c.emo, stack: c.boss * humans.length });
    this.seats.push(boss);
    this.ch.hpMax = boss.stack;
    this.settings.sb = CH_BLINDS[0][0]; this.settings.bb = CH_BLINDS[0][1];
    this.hand = this.blankHand(this.hand.sq + 1); this.champ = ''; this.opp = new Map();
  }
  chBegin() { this.startHand(); }
  chHp() { const b = this.seats.find(s => s.boss); return b ? b.stack : 0; }
  chLvl() { return Math.min(CH_BLINDS.length - 1, Math.floor(Math.max(0, this.hand.no - 1) / CH_BLIND_EVERY)); }
  chInfo() {
    const lvl = this.chLvl(), last = lvl >= CH_BLINDS.length - 1;
    return { sb: this.settings.sb, bb: this.settings.bb, nextIn: last || !this.hand.no ? 0 : CH_BLIND_EVERY - ((this.hand.no - 1) % CH_BLIND_EVERY), nbb: last ? 0 : CH_BLINDS[lvl + 1][1] };
  }
  startHand() {
    if (this.ch.state === 'play') {
      const lvl = Math.min(CH_BLINDS.length - 1, Math.floor(this.hand.no / CH_BLIND_EVERY)), [sb, bb] = CH_BLINDS[lvl];
      if (bb !== this.settings.bb) { this.settings.sb = sb; this.settings.bb = bb; if (this.hand.no) this.log(`🔺 블라인드 상승! ${fmt(sb)} / ${fmt(bb)}`); }
    }
    super.startHand();
  }
  endHand() {
    this.botReactions();
    this.seats.forEach(o => { if (o.inHand) this.statHand(o, o.stack - (o.st0 ?? o.stack)); });
    this.seats.forEach(o => { if (o.stack <= 0) o.out = true; });
    const boss = this.seats.find(s => s.boss);
    if (!boss || boss.stack <= 0) { this.chEnd(true); return; }
    if (!this.seats.some(s => !s.bot && s.stack > 0)) { this.chEnd(false); return; }
    const prevHp = boss.st0 ?? boss.stack;
    const spoke = this.chBossMood(prevHp, boss.stack);
    const diff = boss.stack - prevHp;
    if (!spoke && boss.inHand && Math.abs(diff) >= this.settings.bb * 8 && rnd() < 0.4) setTimeout(() => this.bossSay((diff > 0 ? CH_TAUNT.win : CH_TAUNT.hurt)[randInt(5)]), 1600);
    this.nextAt = Date.now() + (this.hand.res && this.hand.res.kind === 'show' ? 8000 : 5500);
    this.dirty = true;
  }
  chToLobby() {
    this.status = 'lobby'; this.nextAt = 0; this.runoutAt = 0;
    this.hand = this.blankHand(this.hand.sq + 1); this.champ = ''; this.msg = '';
    this.seats = this.seats.filter(s => !s.bot && s.online && !s.kicked);
    this.seats.forEach(s => { this.resetSeatHand(s); s.stack = CH_START; s.out = false; });
    this.ch.state = 'ready'; this.ch.result = null;
    this.chSeatSpectators();
    this.log('도전 대기실로 돌아왔어요'); this.dirty = true;
  }
  publicState() {
    const p = super.publicState();
    p.seats.forEach((x, k) => { const s = this.seats[k]; if (s && s.boss) { x.boss = 1; x.emo = s.emo; x.lv = this.cfg.diff; } });
    return p;
  }
}

class ChBJ extends ChMix(BJRoom) {
  constructor(code) { super(code); this.settings = { stack: CH_START, minBet: 1000, timer: 30, maxBet: 5000 }; }
  chHumanCap() { return 7; }
  chUnit() { return '라운드'; }
  chNo() { return this.r.no; }
  chApply() { const c = this.cfg; this.rules = { ...c.rules }; this.settings.maxBet = c.maxBet; }
  chSetup(humans) {
    humans.forEach(s => { this.resetBJ(s); s.stack = CH_START; s.out = false; s.inHand = false; s.bj.want = this.settings.minBet; });
    this.ch.hpMax = chHpScale(this.cfg.hp, humans.length, 0.7); this.ch.base = CH_START * humans.length;
    this.ch.stk = Object.fromEntries(humans.map(s => [s.id, CH_START]));
    this.r = this.blankRound(this.r.sq + 1); this.shoe = newShoe(BJ_DECKS);
  }
  chBegin() { this.startRound(); }
  chHp() { return this.ch.hpMax - this.ch.net; }
  chInfo() { return { minBet: this.settings.minBet, maxBet: this.settings.maxBet, rules: this.rules }; }
  startRound() { super.startRound(); for (const s of this.seats) if (s.bj.inR) s.bj.want = Math.min(s.bj.want, this.settings.maxBet); }
  bjMsg(pid, msg) {
    if (this.r.st === 'bet' && String(msg && msg.a) === 'betok') {
      const x = Math.floor(+msg.x || 0);
      if (x > this.settings.maxBet) { msg = { ...msg, x: this.settings.maxBet }; tell(pid, 'err', `이 보스 테이블의 최대 베팅은 ${fmt(this.settings.maxBet)}이라 그만큼만 걸었어요`); }
    }
    super.bjMsg(pid, msg);
  }
  settle() { super.settle(); this.chAfterRound(); }
  chToLobby() {
    this.status = 'lobby'; this.nextAt = 0; this.dealerAt = 0;
    this.r = this.blankRound(this.r.sq + 1); this.msg = '';
    this.seats = this.seats.filter(s => !s.bot && s.online && !s.kicked);
    this.seats.forEach(s => { this.resetBJ(s); s.stack = CH_START; s.out = false; s.inHand = false; });
    this.ch.state = 'ready'; this.ch.result = null;
    this.chSeatSpectators();
    this.log('도전 대기실로 돌아왔어요'); this.dirty = true;
  }
}

class ChBac extends ChMix(BacRoom) {
  constructor(code) { super(code); this.settings = { stack: CH_START, minBet: 1000, timer: 20, maxBet: 5000 }; }
  chHumanCap() { return 7; }
  chUnit() { return '라운드'; }
  chNo() { return this.r.no; }
  minStake() { return this.settings.minBet; }
  chApply() { this.settings.maxBet = this.cfg.maxBet; }
  chSetup(humans) {
    humans.forEach(s => { this.resetBac(s); s.stack = CH_START; s.out = false; });
    this.ch.hpMax = chHpScale(this.cfg.hp, humans.length, 1); this.ch.base = CH_START * humans.length;
    this.ch.stk = Object.fromEntries(humans.map(s => [s.id, CH_START]));
    this.r = this.blankRound(this.r.sq + 1); this.r.hist = []; this.shoe = newShoe(BAC_DECKS); this.shoeNo = 1;
  }
  chBegin() { this.startRound(); }
  chHp() { return this.ch.hpMax - this.ch.net; }
  chInfo() { return { minBet: this.settings.minBet, maxBet: this.settings.maxBet }; }
  bacMsg(pid, msg) {
    const s = this.seatOf(pid);
    if (s && this.r.st === 'bet' && String(msg && msg.a) === 'betok') {
      const src = msg.bets && typeof msg.bets === 'object' ? msg.bets : {};
      const sum = BAC_SPOTS.reduce((a, k) => a + Math.max(0, Math.floor(+src[k] || 0)), 0);
      if (sum && sum < this.settings.minBet) { tell(pid, 'err', `챌린지는 한 판에 최소 ${fmt(this.settings.minBet)} 이상 걸어야 해요`); return; }
      if (sum > this.settings.maxBet) { tell(pid, 'err', `이 보스 테이블은 한 판 최대 ${fmt(this.settings.maxBet)}까지예요`); return; }
    }
    super.bacMsg(pid, msg);
  }
  settle() { super.settle(); this.chAfterRound(); }
  chToLobby() {
    this.status = 'lobby'; this.nextAt = 0;
    this.r = this.blankRound(this.r.sq + 1); this.r.hist = []; this.msg = '';
    this.seats = this.seats.filter(s => !s.bot && s.online && !s.kicked);
    this.seats.forEach(s => { this.resetBac(s); s.stack = CH_START; s.out = false; });
    this.ch.state = 'ready'; this.ch.result = null;
    this.chSeatSpectators();
    this.log('도전 대기실로 돌아왔어요'); this.dirty = true;
  }
}
const CH_CLASS = { holdem: ChHoldem, bj: ChBJ, bac: ChBac };


/* ---------------- 접속(SSE 스트림) ---------------- */
const clean = (v, n) => String(v ?? '').replace(/[\u0000-\u001f\u007f]/g, '').trim().slice(0, n);
const clients = new Map(); // pid -> Set<Client>
const lastReact = new Map();
class Client {
  constructor(pid, res) { this.pid = pid; this.res = res; this.code = null; this.lastChat = 0; this.alive = true; }
  emit(ev, data) {
    if (!this.alive) return;
    try { this.res.write(`event: ${ev}\ndata: ${JSON.stringify(data)}\n\n`); } catch (e) { this.alive = false; }
  }
}
function clientsOf(pid) { return clients.get(pid) || new Set(); }

function leaveCurrent(c) {
  const room = rooms.get(c.code);
  if (!room) { c.code = null; return; }
  room.socks.delete(c); c.watch = false;
  const stillHere = [...room.socks].some(s => s.pid === c.pid);
  const seat = room.seatOf(c.pid);
  if (seat && !stillHere) { seat.online = false; seat.offSince = Date.now(); room.dirty = true; }
  if (!room.socks.size) room.emptySince = Date.now();
  c.code = null;
}
function enter(c, room, name) {
  if (room.banned.has(c.pid)) { c.emit('nojoin', '방장이 내보낸 방이라 다시 들어갈 수 없어요'); return; }
  if (c.code && c.code !== room.code) leaveCurrent(c);
  c.code = room.code; c.watch = false;
  if (name) c.name = name;
  room.socks.add(c);
  const pid = c.pid;
  let seat = room.seatOf(pid);
  const chBusy = room.ch && (room.status !== 'lobby' || room.seats.filter(s => !s.bot).length >= room.chHumanCap());
  if (seat) {
    seat.online = true;
    if (name && seat.name !== name) seat.name = name;
    if (c.uid && !seat.uid) seat.uid = c.uid;
  } else if (chBusy) {
    room.dirty = true; room.tick(Date.now());
    c.emit('chatlog', room.chat);
    c.emit('err', room.status !== 'lobby' ? '지금 보스와 싸우는 중이라 관전으로 들어왔어요. 다음 도전부터 같이 해요!' : '도전 인원이 꽉 찼어요. 관전으로 들어왔어요');
    return;
  } else if (room.seats.length < 8) {
    seat = room.newSeat(pid, name);
    seat.uid = c.uid || '';
    room.seats.push(seat);
    if (room.status === 'playing') room.statAdd(seat);
    room.log(`${name} 입장${room.status === 'playing' ? ' · 다음 핸드부터 참여' : ''}`);
  }
  if (!room.hostPid) room.hostPid = pid;
  room.dirty = true;
  room.tick(Date.now());
  c.emit('chatlog', room.chat);
  if (!seat) c.emit('err', '자리가 꽉 차서 관전으로 들어왔어요');
}
// 관리자 관전: 자리 없이 화면만 받음. 입장 기록·채팅·이모티콘이 안 남아서 다른 사람은 모름
function watchEnter(c, room) {
  if (c.code && c.code !== room.code) leaveCurrent(c);
  c.code = room.code; c.watch = true;
  room.socks.add(c);
  room.sendTo(c, room.publicState());
  c.emit('chatlog', room.chat);
}
const GAME_KO = { holdem: '홀덤', bj: '블랙잭', bac: '바카라' };
function adminList() {
  const now = Date.now();
  return [...rooms.values()].map(r => {
    const no = r.r ? r.r.no || 0 : (r.hand && r.hand.no) || 0;
    const host = r.seats.find(s => s.pid === r.hostPid);
    return {
      code: r.code, game: r.game || 'holdem', g: GAME_KO[r.game || 'holdem'] + (r.ch ? ` 챌린지 ${r.ch.st}단계` : ''), st: r.status, no,
      host: host ? host.name : '',
      ppl: r.seats.filter(s => !s.kicked).map(s => ({ n: s.name, bot: s.bot ? 1 : 0, s: s.stack, on: s.bot || s.online ? 1 : 0 })),
      watch: [...r.socks].filter(c => !c.watch).length,
      idle: r.socks.size ? 0 : Math.round((now - r.emptySince) / 60000)
    };
  }).sort((a, b) => (b.st === 'playing') - (a.st === 'playing') || b.watch - a.watch);
}
function roomOf(pid) { for (const c of clientsOf(pid)) { const r = rooms.get(c.code); if (r) return r; } return null; }
function tell(pid, ev, data) { for (const c of clientsOf(pid)) c.emit(ev, data); }

function handle(msg) {
  const pid = clean(msg && msg.pid, 40);
  const cs = clientsOf(pid);
  if (pid.length < 12 || !cs.size) return;
  const type = String(msg.type || '');
  if (type === 'create' || type === 'join') for (const c of cs) c.uid = clean(msg.uid, 24);
  if (type === 'create' && msg.ch && typeof msg.ch === 'object') {
    // 챌린지 방 만들기 (solo면 바로 시작)
    const name = clean(msg.name, 10) || '도전자';
    const g = String(msg.ch.g || ''), st = Math.floor(+msg.ch.st);
    if (!CH_STAGES[g] || !(st >= 1 && st <= 5)) return;
    const uid = clean(msg.uid, 24);
    if (st > chMaxOpen(uid, g)) { tell(pid, 'nojoin', `${CH_GAMES[g]} ${st}단계는 아직 잠겨 있어요. 앞 단계를 먼저 깨 주세요`); return; }
    let code; do { code = Array.from({ length: 5 }, () => CODE_ABC[randInt(CODE_ABC.length)]).join(''); } while (rooms.has(code));
    const room = new CH_CLASS[g](code); room.chInit(g, st); rooms.set(code, room);
    room.hostPid = pid;
    room.log(`${CH_GAMES[g]} 챌린지 방이에요. 코드 ${code}를 친구에게 보내면 같이 도전할 수 있어요`);
    for (const c of cs) enter(c, room, name);
    if (msg.solo) room.hostCmd('start');
    room.tick(Date.now());
  } else if (type === 'hof') {
    tell(pid, 'hof', { recs: HOF.recs });
  } else if (type === 'hofsync') {
    // 폰에 남아 있던 기록 되살리기 (서명이 맞는 것만)
    const list = Array.isArray(msg.recs) ? msg.recs.slice(0, 30) : [];
    let k = 0; for (const x of list) { const r = recClean(x); if (r && hofAdd(r)) k++; }
    if (k) console.log(`챌린지 기록 ${k}개 복구`);
  } else if (type === 'create') {
    const name = clean(msg.name, 10) || '방장';
    let code; do { code = Array.from({ length: 5 }, () => CODE_ABC[randInt(CODE_ABC.length)]).join(''); } while (rooms.has(code));
    const room = msg.game === 'bj' ? new BJRoom(code) : msg.game === 'bac' ? new BacRoom(code) : new Room(code); rooms.set(code, room);
    room.hostPid = pid;
    room.log(`방이 만들어졌어요. 코드 ${code}`);
    for (const c of cs) enter(c, room, name);
  } else if (type === 'join') {
    const code = clean(msg.code, 5).toUpperCase();
    const name = clean(msg.name, 10) || '손님';
    const room = rooms.get(code);
    if (!room) { tell(pid, 'nojoin', '그 코드의 방이 없어요. 코드를 다시 확인해 주세요'); return; }
    for (const c of cs) enter(c, room, name);
  } else if (type === 'act') {
    const room = roomOf(pid); if (!room || room.status !== 'playing') return;
    if (room.game === 'bj') { room.bjMsg(pid, msg); return; }
    if (room.game === 'bac') { room.bacMsg(pid, msg); return; }
    const i = room.seats.findIndex(s => s.pid === pid);
    if (i < 0 || room.hand.tu !== i || msg.sq !== room.hand.sq) return;
    if (!room.act(i, String(msg.a), msg.x)) tell(pid, 'err', '지금은 그 액션을 할 수 없어요');
    room.dirty = true; room.tick(Date.now());
  } else if (type === 'admin') {
    // 관리자 로그인 / 방 목록 / 관전
    const now = Date.now();
    let tok = String(msg.tok || '');
    if (msg.pw !== undefined) {
      const f = pwFails.get(pid) || { n: 0, until: 0 };
      if (now < f.until) { tell(pid, 'admin', { ok: 0, why: '잠시 후 다시 시도해 주세요' }); return; }
      if (String(msg.pw) !== ADMIN_PW) { f.n++; if (f.n >= 5) { f.n = 0; f.until = now + 60000; } pwFails.set(pid, f); tell(pid, 'admin', { ok: 0, why: '비밀번호가 틀렸어요' }); return; }
      pwFails.delete(pid);
      tok = crypto.randomBytes(16).toString('hex'); adminTokens.set(tok, now + 12 * 3600e3);
    }
    if (!isAdmin(tok)) { tell(pid, 'admin', { ok: 0, why: '관리자 로그인이 만료됐어요. 다시 입력해 주세요', out: 1 }); return; }
    if (msg.a === 'watch') {
      const room = rooms.get(clean(msg.code, 5).toUpperCase());
      if (!room) { tell(pid, 'admin', { ok: 1, tok, list: adminList(), why: '그 방은 이미 없어졌어요' }); return; }
      for (const c of cs) { if (room.seatOf(pid)) enter(c, room, ''); else watchEnter(c, room); }
      return;
    }
    tell(pid, 'admin', { ok: 1, tok, list: adminList() });
  } else if (type === 'chat') {
    const room = roomOf(pid); if (!room) return;
    if ([...cs].some(c => c.watch)) return;
    const c0 = [...cs][0]; const now = Date.now();
    if (now - c0.lastChat < 400) return; c0.lastChat = now;
    const t = clean(msg.t, 140); if (!t) return;
    const seat = room.seatOf(pid);
    room.pushChat({ n: seat ? seat.name : '관전자', sid: seat ? seat.id : '', t });
  } else if (type === 'react') {
    const room = roomOf(pid); if (!room) return;
    if ([...cs].some(c => c.watch)) return;
    const e = String(msg.e || ''); if (!EMOJIS.includes(e)) return;
    const now = Date.now(); if (now - (lastReact.get(pid) || 0) < 700) return; lastReact.set(pid, now);
    const seat = room.seatOf(pid);
    const r = { e, sid: seat ? seat.id : '', n: seat ? seat.name : '관전자', k: crypto.randomBytes(3).toString('hex') };
    for (const c of room.socks) c.emit('react', r);
  } else if (type === 'secret') {
    const room = roomOf(pid); if (!room) return;
    const seat = room.seatOf(pid); if (!seat) return;
    if (room.ch) { tell(pid, 'err', '챌린지에서는 쓸 수 없어요. 실력으로 깨야 명예의 전당에 올라가요!'); return; }
    const f = pwFails.get(pid) || { n: 0, until: 0 }; const now = Date.now();
    if (now < f.until) { tell(pid, 'err', '잠시 후 다시 시도해 주세요'); return; }
    if (String(msg.pw || '') !== LUCKY_PW) { f.n++; if (f.n >= 5) { f.n = 0; f.until = now + 60000; } pwFails.set(pid, f); tell(pid, 'secret', { ok: 0 }); return; }
    pwFails.delete(pid);
    seat.lucky = !seat.lucky;
    tell(pid, 'secret', { ok: 1, on: seat.lucky ? 1 : 0 });
    room.dirty = true; room.tick(now);
  } else if (type === 'reveal') {
    const room = roomOf(pid); if (!room) return;
    room.reveal(room.seatOf(pid)); room.tick(Date.now());
  } else if (type === 'host') {
    const room = roomOf(pid); if (!room || room.hostPid !== pid) return;
    const cmd = String(msg.cmd);
    if (cmd === 'kick' || cmd === 'kickbot') {
      const seat = room.seats.find(s => s.id === String(msg.arg && msg.arg.id || ''));
      if (!seat || seat.pid === pid || seat.kicked) return;
      room.kickSeat(seat);
      if (!seat.bot) {
        room.banned.add(seat.pid);
        for (const c of [...clientsOf(seat.pid)]) if (c.code === room.code) { c.emit('kicked', { code: room.code }); leaveCurrent(c); }
      }
      room.tick(Date.now()); return;
    }
    if (cmd === 'give') {
      const seat = room.seats.find(s => s.id === String(msg.arg && msg.arg.id || ''));
      const amt = Math.floor(+(msg.arg && msg.arg.amt) || 0);
      if (!seat || seat.kicked) return;
      if (room.ch) { tell(pid, 'err', '챌린지에서는 칩을 줄 수 없어요'); return; }
      if (room.status !== 'playing') { tell(pid, 'err', '게임을 시작한 뒤에 칩을 줄 수 있어요'); return; }
      // 금액 제한 없음 (계산이 틀어지지 않는 선인 1000조까지만 막음)
      if (amt < 1) { tell(pid, 'err', '줄 칩 수를 입력해 주세요'); return; }
      if (seat.stack + (seat.pendGive || 0) + amt > 1e15) { tell(pid, 'err', '한 사람이 가질 수 있는 칩은 1000조까지예요'); return; }
      room.giveChips(seat, amt); room.tick(Date.now()); return;
    }
    const err = room.hostCmd(cmd, msg.arg);
    if (err) tell(pid, 'err', err);
    room.tick(Date.now());
  } else if (type === 'leave') {
    const room = roomOf(pid);
    for (const c of cs) leaveCurrent(c);
    if (room) {
      const seat = room.seatOf(pid);
      if (seat && room.status !== 'playing') { room.seats = room.seats.filter(s => s !== seat); room.log(`${seat.name} 퇴장`); room.dirty = true; }
      room.tick(Date.now());
    }
  }
}

const server = http.createServer((req, res) => {
  const url = new URL(req.url, 'http://localhost');
  if (url.pathname === '/healthz') { res.writeHead(200); res.end('ok'); return; }
  const origin = `https://${String(req.headers['x-forwarded-host'] || req.headers.host || '').replace(/[^\w.\-:]/g, '')}`;
  if (url.pathname === '/robots.txt') { res.writeHead(200, { 'content-type': 'text/plain; charset=utf-8' }); res.end(`User-agent: *\nAllow: /\nDisallow: /api\nDisallow: /events\nSitemap: ${origin}/sitemap.xml\n`); return; }
  if (url.pathname === '/sitemap.xml') { res.writeHead(200, { 'content-type': 'application/xml; charset=utf-8' }); res.end(`<?xml version="1.0" encoding="UTF-8"?>\n<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9"><url><loc>${origin}/</loc><changefreq>weekly</changefreq><priority>1.0</priority></url></urlset>\n`); return; }
  if (url.pathname === '/favicon.ico') { res.writeHead(204); res.end(); return; }
  if (url.pathname === '/events' && req.method === 'GET') {
    const pid = clean(url.searchParams.get('pid'), 40);
    if (pid.length < 12) { res.writeHead(400); res.end(); return; }
    req.socket.setNoDelay(true);
    req.socket.setKeepAlive(true, 15000);
    res.writeHead(200, { 'content-type': 'text/event-stream; charset=utf-8', 'cache-control': 'no-cache, no-transform', connection: 'keep-alive', 'x-accel-buffering': 'no' });
    res.write('retry: 1500\n\n');
    const c = new Client(pid, res);
    if (!clients.has(pid)) clients.set(pid, new Set());
    clients.get(pid).add(c);
    c.emit('hello', { t: Date.now(), emojis: EMOJIS, hof: HOF.recs.map(r => r.id), ch: CH_INFO_PUB });
    const ka = setInterval(() => { try { res.write(': ka\n\n'); } catch (e) {} }, 15000);
    req.on('close', () => {
      clearInterval(ka); c.alive = false;
      const set = clients.get(pid); if (set) { set.delete(c); if (!set.size) clients.delete(pid); }
      const room = rooms.get(c.code); leaveCurrent(c); if (room) room.tick(Date.now());
    });
    return;
  }
  if (url.pathname === '/api' && req.method === 'POST') {
    let body = '';
    req.on('data', d => { body += d; if (body.length > 10000) req.destroy(); });
    req.on('end', () => {
      let msg; try { msg = JSON.parse(body); } catch (e) { res.writeHead(400); res.end(); return; }
      res.writeHead(204); res.end();
      try { handle(msg); } catch (e) { console.error('handle error', e); }
    });
    return;
  }
  if (req.headers['if-none-match'] === PAGE_ETAG) { res.writeHead(304, { etag: PAGE_ETAG }); res.end(); return; }
  const gz = /\bgzip\b/.test(req.headers['accept-encoding'] || '');
  res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache', etag: PAGE_ETAG, vary: 'accept-encoding', ...(gz ? { 'content-encoding': 'gzip' } : {}) });
  res.end(gz ? PAGE_GZ : PAGE);
});

setInterval(() => {
  const now = Date.now();
  for (const [code, room] of rooms) {
    if (!room.socks.size && now - room.emptySince > 2 * 3600e3) { rooms.delete(code); continue; }
    try { room.tick(now); } catch (e) { console.error('tick error', code, e); }
  }
  for (const [pid, t] of lastReact) if (now - t > 60000) lastReact.delete(pid);
}, 250);

server.keepAliveTimeout = 65000;
hofLoad();
if (require.main === module) server.listen(PORT, () => console.log(`수완 종합게임 서버 실행 중: http://localhost:${PORT}`));

module.exports = { BOT_LEVELS, ChHoldem, ChBJ, ChBac, CH_STAGES, CH_CLASS, HOF, hofAdd, recSig, recClean, chMaxOpen, proDecide, PRE, BJRoom, BacRoom, bacPlay, bacReturn, bacNet, bjTotal, basicStrategy, Room, rooms, server, bestHand, handName, cmpScore, eval5, equity, botDecide, eval7i, CARD_INT };
