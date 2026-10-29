// 우리끼리 홀덤 — 실시간 서버
// 실행: npm start  (외부 패키지 없음. PORT 환경변수가 있으면 그 포트 사용)
// 서버 → 화면: Server-Sent Events(/events), 화면 → 서버: POST /api
'use strict';
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');
const zlib = require('zlib');

const PORT = process.env.PORT || 3000;
const PAGE = fs.readFileSync(path.join(__dirname, 'index.html'));
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
  hard:   { label: '어려움', sims: 1200, noise: 0.03, loose: 0.02, aggr: 1.05, bluff: 0.14, slow: [1200, 3200] }
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

/* ---------------- 행운 모드 (비밀) ---------------- */
// Render 환경변수 LUCKY_PW 로 바꿀 수 있어요. 없으면 기본값 사용.
const LUCKY_PW = process.env.LUCKY_PW || '0104';
const LUCKY_RATE = 0.85; // 85% 확률로 이기는 패, 나머지는 평범하게 (티 안 나게)
const pwFails = new Map();

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
  }
  blankHand(sq) { return { no: 0, d: -1, sq, tu: -1, st: 'idle', bd: [], pot: 0, cb: 0, mr: 0, holes: {}, deck: [], res: null, sbI: -1, bbI: -1 }; }
  newSeat(pid, name) {
    return { pid, id: crypto.randomBytes(4).toString('hex'), name, stack: this.settings.stack, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, out: false, online: true, offSince: 0, shown: null, best: null, la: '', won: 0, hn: '' };
  }
  resetSeatHand(s) { Object.assign(s, { popped: false, bet: 0, contrib: 0, folded: false, allIn: false, acted: false, inHand: false, shown: null, best: null, la: '', won: 0, hn: '' }); }
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
    elig.forEach(i => this.seats[i].inHand = true);
    hd.no++;
    hd.d = this.nextIn(hd.d ?? -1);
    let sbI, bbI;
    if (elig.length === 2) { sbI = hd.d; bbI = this.nextIn(hd.d); } else { sbI = this.nextIn(hd.d); bbI = this.nextIn(sbI); }
    this.pay(this.seats[sbI], this.settings.sb); this.seats[sbI].la = 'SB';
    this.pay(this.seats[bbI], this.settings.bb); this.seats[bbI].la = 'BB';
    Object.assign(hd, { sbI, bbI, cb: this.settings.bb, mr: this.settings.bb, pot: 0, bd: [], st: 'pre', res: null, deck: newDeck(), holes: {} });
    const dealHoles = deck => { const holes = {}; for (let r = 0; r < 2; r++) { let j = hd.d; for (let c = 0; c < elig.length; c++) { j = this.nextIn(j); const pid = this.seats[j].pid; (holes[pid] || (holes[pid] = [])).push(deck.pop()); } } return holes; };
    hd.holes = dealHoles(hd.deck);
    // 행운 모드: 해당 플레이어가 리버까지 가면 이기도록 덱을 골라요 (가끔은 일부러 평범하게)
    const lucky = this.seats.find(s => s.lucky && s.inHand);
    if (lucky && rnd() < LUCKY_RATE) {
      for (let t = 0; t < 400; t++) {
        const deck = newDeck(), holes = dealHoles(deck);
        const d = deck.slice(); d.pop(); const bd = [d.pop(), d.pop(), d.pop()]; d.pop(); bd.push(d.pop()); d.pop(); bd.push(d.pop());
        const ints = cs => cs.map(c => CARD_INT[c]);
        const mine = eval7i(ints([...holes[lucky.pid], ...bd]));
        if (mine < B13[5]) continue; // 최소 원페어 이상
        let ok = true;
        for (const pid of Object.keys(holes)) if (pid !== lucky.pid && eval7i(ints([...holes[pid], ...bd])) >= mine) { ok = false; break; }
        if (ok) { hd.deck = deck; hd.holes = holes; break; }
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
    const toCall = hd.cb - s.bet;
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
    const live = this.seats.filter(o => o.inHand && !o.folded);
    if (live.length === 1) { this.winByFold(live[0]); return true; }
    const nt = this.findNeed(i, false);
    if (nt < 0) this.endStreet(); else { hd.tu = nt; hd.sq++; this.turnStart = Date.now(); this.dirty = true; }
    return true;
  }
  endStreet() {
    const hd = this.hand;
    this.seats.forEach(o => { hd.pot += o.bet; o.bet = 0; o.acted = false; if (o.inHand && !o.folded && o.la !== '올인') o.la = ''; });
    hd.cb = 0; hd.mr = this.settings.bb;
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
        note: w.length > 1 ? '' : kickerNote(best, runner),
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
      if (p.split) return `${head}무승부 · ${p.names.join(', ')} ${p.hn}로 ${fmt(p.amt)} 나눔`;
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
    this.seats.forEach(o => { if (o.stack <= 0) o.out = true; });
    const alive = this.seats.filter(o => o.stack > 0);
    if (alive.length < 2) { this.status = 'over'; this.champ = alive[0] ? alive[0].name : ''; this.log(`게임 종료 · ${this.champ} 우승`); this.nextAt = 0; }
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
      this.log(`게임 시작 · 시작 칩 ${fmt(this.settings.stack)}, 블라인드 ${this.settings.sb}/${this.settings.bb}`);
      this.startHand();
    } else if (cmd === 'next' && this.status === 'playing' && (this.hand.st === 'show' || this.hand.st === 'idle')) {
      this.nextAt = 0; this.startHand();
    } else if (cmd === 'rebuy') {
      let k = 0; this.seats.forEach(s => { if (s.out && !s.inHand) { s.stack = this.settings.stack; s.out = false; k++; } });
      if (k) { this.log(`탈락자 ${k}명 리바이 (${fmt(this.settings.stack)})`); this.dirty = true; }
    } else if (cmd === 'lobby') {
      this.status = 'lobby'; this.nextAt = 0; this.runoutAt = 0;
      this.hand = this.blankHand(this.hand.sq + 1); this.champ = ''; this.msg = '';
      this.seats = this.seats.filter(s => s.online);
      this.seats.forEach(s => { this.resetSeatHand(s); s.stack = this.settings.stack; s.out = false; });
      this.log('대기실로 돌아왔어요'); this.dirty = true;
    }
    return '';
  }

  /* ---- 주기 처리 ---- */
  tick(now) {
    const host = this.seatOf(this.hostPid);
    if (!host || (!host.online && now - host.offSince > 30000)) {
      const next = this.seats.find(s => s.online && !s.bot && s.pid !== this.hostPid);
      if (next) { this.hostPid = next.pid; this.log(`${next.name}님이 새 방장이 됐어요`); this.dirty = true; }
    }
    if (this.status !== 'playing') {
      const before = this.seats.length;
      this.seats = this.seats.filter(s => { if (s.online || now - s.offSince < 60000) return true; this.log(`${s.name} 퇴장`); return false; });
      if (before !== this.seats.length) this.dirty = true;
    }
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
        if (now - this.turnStart > this.turnLimit(s)) { this.log(`${s.name} 시간 초과`); this.act(hd.tu, hd.cb > s.bet ? 'fold' : 'check'); }
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
      code: this.code, status: this.status, set: this.settings, msg: this.msg, champ: this.champ,
      seats: this.seats.map(s => ({ id: s.id, n: s.name, s: s.stack, b: s.bet, f: s.folded ? 1 : 0, a: s.allIn ? 1 : 0, ac: s.acted ? 1 : 0, ih: s.inHand ? 1 : 0, o: s.out ? 1 : 0, aw: s.online ? 0 : 1, sh: s.shown || 0, bc: s.best || 0, la: s.la, w: s.won, hn: s.hn, host: s.pid === this.hostPid ? 1 : 0, bot: s.bot ? 1 : 0, pp: s.popped ? 1 : 0, lv: s.bot ? BOT_LEVELS[s.lv].label : '' })),
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
  room.socks.delete(c);
  const stillHere = [...room.socks].some(s => s.pid === c.pid);
  const seat = room.seatOf(c.pid);
  if (seat && !stillHere) { seat.online = false; seat.offSince = Date.now(); room.dirty = true; }
  if (!room.socks.size) room.emptySince = Date.now();
  c.code = null;
}
function enter(c, room, name) {
  if (c.code && c.code !== room.code) leaveCurrent(c);
  c.code = room.code;
  room.socks.add(c);
  const pid = c.pid;
  let seat = room.seatOf(pid);
  if (seat) {
    seat.online = true;
    if (name && seat.name !== name) seat.name = name;
  } else if (room.seats.length < 8) {
    seat = room.newSeat(pid, name);
    room.seats.push(seat);
    room.log(`${name} 입장${room.status === 'playing' ? ' · 다음 핸드부터 참여' : ''}`);
  }
  if (!room.hostPid) room.hostPid = pid;
  room.dirty = true;
  room.tick(Date.now());
  c.emit('chatlog', room.chat);
  if (!seat) c.emit('err', '자리가 꽉 차서 관전으로 들어왔어요');
}
function roomOf(pid) { for (const c of clientsOf(pid)) { const r = rooms.get(c.code); if (r) return r; } return null; }
function tell(pid, ev, data) { for (const c of clientsOf(pid)) c.emit(ev, data); }

function handle(msg) {
  const pid = clean(msg && msg.pid, 40);
  const cs = clientsOf(pid);
  if (pid.length < 12 || !cs.size) return;
  const type = String(msg.type || '');
  if (type === 'create') {
    const name = clean(msg.name, 10) || '방장';
    let code; do { code = Array.from({ length: 5 }, () => CODE_ABC[randInt(CODE_ABC.length)]).join(''); } while (rooms.has(code));
    const room = new Room(code); rooms.set(code, room);
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
    const i = room.seats.findIndex(s => s.pid === pid);
    if (i < 0 || room.hand.tu !== i || msg.sq !== room.hand.sq) return;
    if (!room.act(i, String(msg.a), msg.x)) tell(pid, 'err', '지금은 그 액션을 할 수 없어요');
    room.dirty = true; room.tick(Date.now());
  } else if (type === 'chat') {
    const room = roomOf(pid); if (!room) return;
    const c0 = [...cs][0]; const now = Date.now();
    if (now - c0.lastChat < 400) return; c0.lastChat = now;
    const t = clean(msg.t, 140); if (!t) return;
    const seat = room.seatOf(pid);
    room.pushChat({ n: seat ? seat.name : '관전자', sid: seat ? seat.id : '', t });
  } else if (type === 'react') {
    const room = roomOf(pid); if (!room) return;
    const e = String(msg.e || ''); if (!EMOJIS.includes(e)) return;
    const now = Date.now(); if (now - (lastReact.get(pid) || 0) < 700) return; lastReact.set(pid, now);
    const seat = room.seatOf(pid);
    const r = { e, sid: seat ? seat.id : '', n: seat ? seat.name : '관전자', k: crypto.randomBytes(3).toString('hex') };
    for (const c of room.socks) c.emit('react', r);
  } else if (type === 'secret') {
    const room = roomOf(pid); if (!room) return;
    const seat = room.seatOf(pid); if (!seat) return;
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
    const err = room.hostCmd(String(msg.cmd), msg.arg);
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
    c.emit('hello', { t: Date.now(), emojis: EMOJIS });
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
if (require.main === module) server.listen(PORT, () => console.log(`우리끼리 홀덤 서버 실행 중: http://localhost:${PORT}`));

module.exports = { Room, rooms, server, bestHand, handName, cmpScore, eval5, equity, botDecide, eval7i, CARD_INT };
